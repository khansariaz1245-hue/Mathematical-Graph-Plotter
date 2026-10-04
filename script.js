/**
 * ====================================================================
 * Mathematical Graph Plotter - Engine & Controller
 * Built for Mathematics Students & High-Precision Visual Exploration
 * ====================================================================
 */

(function () {
  'use strict';

  // --- Palette for Multiple Plotted Functions ---
  const COLOR_PALETTE = [
    '#3b82f6', // Electric Blue
    '#8b5cf6', // Neon Violet
    '#10b981', // Emerald Green
    '#f43f5e', // Sunset Rose
    '#f59e0b', // Amber Orange
    '#06b6d4', // Cyan
    '#ec4899', // Pink
    '#14b8a6', // Teal
    '#a855f7', // Purple
    '#eab308'  // Gold
  ];

  // --- Mathematical Parser & Tokenizer ---

  /**
   * Pre-processes human-friendly math strings:
   * - Strips "y =", "f(x) =", "g(x) =" prefixes
   * - Replaces unicode exponents: x² -> x^2, x³ -> x^3, x⁴ -> x^4, etc.
   * - Replaces √x with sqrt(x)
   * - Replaces |x| with abs(x)
   * - Normalizes symbols: π -> pi, × -> *, ÷ -> /
   */
  function sanitizeMathExpression(raw) {
    if (!raw) return '';
    let str = raw.trim();

    // Remove leading y = or f(x) =
    str = str.replace(/^[a-zA-Z](\([a-zA-Z0-9_]*\))?\s*=\s*/, '');

    // Replace unicode exponents
    str = str.replace(/²/g, '^2')
             .replace(/³/g, '^3')
             .replace(/⁴/g, '^4')
             .replace(/⁵/g, '^5');

    // Replace unicode symbols
    str = str.replace(/π/g, 'pi')
             .replace(/×/g, '*')
             .replace(/÷/g, '/');

    // Replace square root symbol √x or √(expr)
    str = str.replace(/√\s*([a-zA-Z0-9_]+|\([^\)]+\))/g, 'sqrt($1)');
    str = str.replace(/√/g, 'sqrt');

    // Handle absolute value pipes |expr| -> abs(expr)
    // Replace |...| iteratively
    let prev;
    do {
      prev = str;
      str = str.replace(/\|([^|]+)\|/g, 'abs($1)');
    } while (str !== prev);

    return str;
  }

  /**
   * Tokenizer: Breaks mathematical string into semantic tokens
   */
  function tokenize(expr) {
    const tokens = [];
    let i = 0;
    const len = expr.length;

    while (i < len) {
      const ch = expr[i];

      // Skip whitespace
      if (/\s/.test(ch)) {
        i++;
        continue;
      }

      // Numbers (integers and decimals)
      if (/[0-9]/.test(ch) || (ch === '.' && i + 1 < len && /[0-9]/.test(expr[i + 1]))) {
        let numStr = '';
        while (i < len && (/[0-9]/.test(expr[i]) || expr[i] === '.')) {
          numStr += expr[i];
          i++;
        }
        tokens.push({ type: 'NUM', value: parseFloat(numStr) });
        continue;
      }

      // Identifiers (variable x, constants pi/e, functions sin, cos, tan, etc.)
      if (/[a-zA-Z_]/.test(ch)) {
        let name = '';
        while (i < len && /[a-zA-Z0-9_]/.test(expr[i])) {
          name += expr[i];
          i++;
        }
        const lower = name.toLowerCase();
        if (lower === 'x') {
          tokens.push({ type: 'VAR', name: 'x' });
        } else if (lower === 'pi') {
          tokens.push({ type: 'NUM', value: Math.PI });
        } else if (lower === 'e') {
          tokens.push({ type: 'NUM', value: Math.E });
        } else {
          tokens.push({ type: 'FN', name: lower });
        }
        continue;
      }

      // Operators and Parentheses
      if ('+-*/^%(),'.includes(ch)) {
        tokens.push({ type: 'OP', value: ch });
        i++;
        continue;
      }

      throw new Error(`Unexpected character: "${ch}"`);
    }

    // Insert implicit multiplication tokens (e.g. 2x -> 2 * x, 3(x+1) -> 3 * (x+1), (x+1)(x-1) -> (x+1)*(x-1))
    const withImplicit = [];
    for (let j = 0; j < tokens.length; j++) {
      const cur = tokens[j];
      withImplicit.push(cur);

      if (j + 1 < tokens.length) {
        const next = tokens[j + 1];
        const curCanMultiply =
          cur.type === 'NUM' ||
          cur.type === 'VAR' ||
          (cur.type === 'OP' && cur.value === ')');

        const nextCanBeMultiplied =
          next.type === 'NUM' ||
          next.type === 'VAR' ||
          next.type === 'FN' ||
          (next.type === 'OP' && next.value === '(');

        if (curCanMultiply && nextCanBeMultiplied) {
          withImplicit.push({ type: 'OP', value: '*' });
        }
      }
    }

    return withImplicit;
  }

  /**
   * Recursive Descent Parser: Builds an Abstract Syntax Tree (AST)
   * Precedence hierarchy:
   * 1. Primary: numbers, variable, constants, function calls, (expr)
   * 2. Exponentiation: ^ (right-associative)
   * 3. Unary prefix: + -
   * 4. Multiplicative: * / %
   * 5. Additive: + -
   */
  function parseAST(tokens) {
    let pos = 0;

    function peek() {
      return tokens[pos];
    }

    function consume(expectedVal = null) {
      const tok = tokens[pos++];
      if (!tok) throw new Error('Unexpected end of equation');
      if (expectedVal && tok.value !== expectedVal) {
        throw new Error(`Expected "${expectedVal}" but found "${tok.value}"`);
      }
      return tok;
    }

    function parseExpression() {
      return parseAddSub();
    }

    function parseAddSub() {
      let node = parseMulDiv();
      while (pos < tokens.length) {
        const tok = peek();
        if (tok && tok.type === 'OP' && (tok.value === '+' || tok.value === '-')) {
          consume();
          const right = parseMulDiv();
          node = { type: 'binary', op: tok.value, left: node, right };
        } else {
          break;
        }
      }
      return node;
    }

    function parseMulDiv() {
      let node = parseUnary();
      while (pos < tokens.length) {
        const tok = peek();
        if (tok && tok.type === 'OP' && (tok.value === '*' || tok.value === '/' || tok.value === '%')) {
          consume();
          const right = parseUnary();
          node = { type: 'binary', op: tok.value, left: node, right };
        } else {
          break;
        }
      }
      return node;
    }

    function parseUnary() {
      const tok = peek();
      if (tok && tok.type === 'OP' && (tok.value === '+' || tok.value === '-')) {
        consume();
        const expr = parseUnary();
        return { type: 'unary', op: tok.value, expr };
      }
      return parseExponent();
    }

    function parseExponent() {
      let node = parsePrimary();
      const tok = peek();
      if (tok && tok.type === 'OP' && tok.value === '^') {
        consume();
        // Right-associative exponentiation
        const right = parseExponent();
        node = { type: 'binary', op: '^', left: node, right };
      }
      return node;
    }

    function parsePrimary() {
      const tok = peek();
      if (!tok) throw new Error('Unexpected end of expression');

      // Numbers
      if (tok.type === 'NUM') {
        consume();
        return { type: 'number', value: tok.value };
      }

      // Variable x
      if (tok.type === 'VAR') {
        consume();
        return { type: 'variable', name: 'x' };
      }

      // Function calls: sin(x), sqrt(x), etc.
      if (tok.type === 'FN') {
        const fnTok = consume();
        const next = peek();
        let arg;
        if (next && next.type === 'OP' && next.value === '(') {
          consume('(');
          arg = parseExpression();
          consume(')');
        } else {
          // Allow sin x or sqrt x without brackets
          arg = parsePrimary();
        }
        return { type: 'call', fn: fnTok.name, arg };
      }

      // Parentheses (expr)
      if (tok.type === 'OP' && tok.value === '(') {
        consume('(');
        const expr = parseExpression();
        consume(')');
        return expr;
      }

      throw new Error(`Unexpected token "${tok.value || tok.name || tok.type}"`);
    }

    const ast = parseExpression();
    if (pos < tokens.length) {
      throw new Error(`Unexpected extra characters after expression`);
    }
    return ast;
  }

  /**
   * AST Evaluator: safely evaluates f(x) for any value of x
   */
  function evaluateAST(node, x) {
    if (!node) return NaN;

    switch (node.type) {
      case 'number':
        return node.value;

      case 'variable':
        return x;

      case 'unary': {
        const val = evaluateAST(node.expr, x);
        return node.op === '-' ? -val : +val;
      }

      case 'binary': {
        const left = evaluateAST(node.left, x);
        const right = evaluateAST(node.right, x);

        switch (node.op) {
          case '+': return left + right;
          case '-': return left - right;
          case '*': return left * right;
          case '/': return right === 0 ? (left > 0 ? Infinity : left < 0 ? -Infinity : NaN) : left / right;
          case '%': return left % right;
          case '^': return Math.pow(left, right);
          default: return NaN;
        }
      }

      case 'call': {
        const argVal = evaluateAST(node.arg, x);
        switch (node.fn) {
          case 'sin': return Math.sin(argVal);
          case 'cos': return Math.cos(argVal);
          case 'tan': return Math.tan(argVal);
          case 'asin': return (argVal < -1 || argVal > 1) ? NaN : Math.asin(argVal);
          case 'acos': return (argVal < -1 || argVal > 1) ? NaN : Math.acos(argVal);
          case 'atan': return Math.atan(argVal);
          case 'sqrt': return argVal < 0 ? NaN : Math.sqrt(argVal);
          case 'cbrt': return Math.cbrt(argVal);
          case 'abs': return Math.abs(argVal);
          case 'exp': return Math.exp(argVal);
          case 'log': // Natural log (ln)
          case 'ln': return argVal <= 0 ? NaN : Math.log(argVal);
          case 'log10': return argVal <= 0 ? NaN : Math.log10(argVal);
          case 'floor': return Math.floor(argVal);
          case 'ceil': return Math.ceil(argVal);
          case 'round': return Math.round(argVal);
          case 'sinh': return Math.sinh(argVal);
          case 'cosh': return Math.cosh(argVal);
          case 'tanh': return Math.tanh(argVal);
          default:
            throw new Error(`Unknown mathematical function: ${node.fn}()`);
        }
      }

      default:
        return NaN;
    }
  }

  /**
   * Safe parser wrapper returning compiled AST or error message
   */
  function compileMathExpression(rawText) {
    try {
      const sanitized = sanitizeMathExpression(rawText);
      if (!sanitized) {
        return { ast: null, error: 'Empty expression' };
      }
      const tokens = tokenize(sanitized);
      const ast = parseAST(tokens);
      // Quick sanity check with x = 1.0
      evaluateAST(ast, 1.0);
      return { ast, error: null };
    } catch (err) {
      return { ast: null, error: err.message || 'Syntax error' };
    }
  }

  // --- Coordinate Plane & Graph Engine State ---

  const state = {
    // Canvas viewport
    centerX: 0,        // Math x coordinate at center of canvas
    centerY: 0,        // Math y coordinate at center of canvas
    scale: 50,         // Pixels per mathematical unit (50px = 1 unit)
    defaultScale: 50,  // Reset scale
    minScale: 5,       // Max zoom out
    maxScale: 2000,    // Max zoom in
    
    // Equations array
    equations: [
      { id: 'eq_1', text: 'x^2', color: COLOR_PALETTE[0], visible: true, ast: null, error: null },
      { id: 'eq_2', text: 'sin(x)', color: COLOR_PALETTE[1], visible: true, ast: null, error: null }
    ],

    // Interaction state
    isDragging: false,
    dragStartX: 0,
    dragStartY: 0,
    dragCenterStartX: 0,
    dragCenterStartY: 0,
    hoverMathX: null,
    hoverMathY: null,
    showTangent: false,
    showGrid: true,
    showNumbers: true,
    detectRoots: true,
    lastFocusedInput: null
  };

  // --- DOM Elements ---
  const canvas = document.getElementById('graphCanvas');
  const ctx = canvas.getContext('2d');
  const equationsContainer = document.getElementById('equationsContainer');
  const equationCountBadge = document.getElementById('equationCountBadge');
  const btnAddEquation = document.getElementById('btnAddEquation');
  const btnPlotGraph = document.getElementById('btnPlotGraph');
  const btnClearGraph = document.getElementById('btnClearGraph');
  const btnResetView = document.getElementById('btnResetView');
  const btnCanvasReset = document.getElementById('btnCanvasReset');
  const btnZoomIn = document.getElementById('btnZoomIn');
  const btnZoomOut = document.getElementById('btnZoomOut');
  const btnThemeToggle = document.getElementById('btnThemeToggle');
  const btnToggleTangent = document.getElementById('btnToggleTangent');
  const tangentStatusText = document.getElementById('tangentStatusText');
  const btnExportImage = document.getElementById('btnExportImage');
  const btnOpenHelp = document.getElementById('btnOpenHelp');
  const btnCloseHelpModal = document.getElementById('btnCloseHelpModal');
  const btnCloseHelpModalBtn = document.getElementById('btnCloseHelpModalBtn');
  const helpModal = document.getElementById('helpModal');
  
  // Table of Values elements
  const btnOpenTable = document.getElementById('btnOpenTable');
  const tableModal = document.getElementById('tableModal');
  const btnCloseTableModal = document.getElementById('btnCloseTableModal');
  const btnCloseTableModalBtn = document.getElementById('btnCloseTableModalBtn');
  const btnRefreshTable = document.getElementById('btnRefreshTable');
  const btnCopyTable = document.getElementById('btnCopyTable');
  const tableHeadRow = document.getElementById('tableHeadRow');
  const tableBody = document.getElementById('tableBody');
  const tableStartInput = document.getElementById('tableStart');
  const tableEndInput = document.getElementById('tableEnd');
  const tableStepInput = document.getElementById('tableStep');

  // Viewport Settings elements
  const inputXMin = document.getElementById('inputXMin');
  const inputXMax = document.getElementById('inputXMax');
  const inputYMin = document.getElementById('inputYMin');
  const inputYMax = document.getElementById('inputYMax');
  const btnApplyRanges = document.getElementById('btnApplyRanges');
  const chkShowGrid = document.getElementById('chkShowGrid');
  const chkShowNumbers = document.getElementById('chkShowNumbers');
  const chkDetectRoots = document.getElementById('chkDetectRoots');

  // Keypad & Inspector elements
  const btnToggleKeypad = document.getElementById('btnToggleKeypad');
  const keypadGrid = document.getElementById('keypadGrid');
  const cursorInspector = document.getElementById('cursorInspector');
  const cursorCoordVal = document.getElementById('cursorCoordVal');
  const cursorFuncsList = document.getElementById('cursorFuncsList');
  const cursorTangentInfo = document.getElementById('cursorTangentInfo');
  const tangentSlopeVal = document.getElementById('tangentSlopeVal');
  const canvasPointTooltip = document.getElementById('canvasPointTooltip');
  const canvasLegend = document.getElementById('canvasLegend');

  // Presets elements
  const btnPresetsMenu = document.getElementById('btnPresetsMenu');
  const presetsDropdown = document.getElementById('presetsDropdown');

  // --- High-DPI Canvas Resizing ---
  let canvasWidth = 0;
  let canvasHeight = 0;
  let dpr = 1;

  function resizeCanvas() {
    dpr = window.devicePixelRatio || 1;
    const rect = canvas.getBoundingClientRect();
    canvasWidth = rect.width;
    canvasHeight = rect.height;

    canvas.width = Math.round(rect.width * dpr);
    canvas.height = Math.round(rect.height * dpr);

    ctx.resetTransform();
    ctx.scale(dpr, dpr);

    updateRangeInputs();
    renderGraph();
  }

  // --- Coordinate Conversions ---
  function toScreenX(mathX) {
    return canvasWidth / 2 + (mathX - state.centerX) * state.scale;
  }

  function toScreenY(mathY) {
    return canvasHeight / 2 - (mathY - state.centerY) * state.scale;
  }

  function toMathX(screenX) {
    return state.centerX + (screenX - canvasWidth / 2) / state.scale;
  }

  function toMathY(screenY) {
    return state.centerY - (screenY - canvasHeight / 2) / state.scale;
  }

  // --- Range Inputs Synchronizer ---
  function updateRangeInputs() {
    if (!canvasWidth || !canvasHeight) return;
    const xMin = toMathX(0);
    const xMax = toMathX(canvasWidth);
    const yMin = toMathY(canvasHeight);
    const yMax = toMathY(0);

    inputXMin.value = xMin.toFixed(2);
    inputXMax.value = xMax.toFixed(2);
    inputYMin.value = yMin.toFixed(2);
    inputYMax.value = yMax.toFixed(2);
  }

  // --- Dynamic Grid Step Calculator ---
  /**
   * Computes a visually pleasing grid spacing (1, 2, 5 * 10^k)
   * so grid lines remain between 60 and 120 pixels apart at any zoom level.
   */
  function calculateNiceGridStep(scale) {
    const minPixelsPerGrid = 60;
    const rawStep = minPixelsPerGrid / scale;
    const power = Math.floor(Math.log10(rawStep));
    const base = Math.pow(10, power);
    const fraction = rawStep / base;

    let niceMultiplier = 1;
    if (fraction > 5) {
      niceMultiplier = 10;
    } else if (fraction > 2) {
      niceMultiplier = 5;
    } else if (fraction > 1) {
      niceMultiplier = 2;
    }

    return niceMultiplier * base;
  }

  // --- Grid and Axes Renderer ---
  function drawCoordinateSystem(colors) {
    const xMin = toMathX(0);
    const xMax = toMathX(canvasWidth);
    const yMin = toMathY(canvasHeight);
    const yMax = toMathY(0);

    const majorStep = calculateNiceGridStep(state.scale);
    const minorStep = majorStep / 5;

    // 1. Minor Grid Lines
    if (state.showGrid) {
      ctx.lineWidth = 1;
      ctx.strokeStyle = colors.gridMinor;
      ctx.beginPath();

      // Vertical minor grid
      const startMinorX = Math.floor(xMin / minorStep) * minorStep;
      for (let x = startMinorX; x <= xMax; x += minorStep) {
        const sx = toScreenX(x);
        ctx.moveTo(Math.round(sx) + 0.5, 0);
        ctx.lineTo(Math.round(sx) + 0.5, canvasHeight);
      }

      // Horizontal minor grid
      const startMinorY = Math.floor(yMin / minorStep) * minorStep;
      for (let y = startMinorY; y <= yMax; y += minorStep) {
        const sy = toScreenY(y);
        ctx.moveTo(0, Math.round(sy) + 0.5);
        ctx.lineTo(canvasWidth, Math.round(sy) + 0.5);
      }
      ctx.stroke();

      // 2. Major Grid Lines
      ctx.lineWidth = 1.2;
      ctx.strokeStyle = colors.gridMajor;
      ctx.beginPath();

      const startMajorX = Math.floor(xMin / majorStep) * majorStep;
      for (let x = startMajorX; x <= xMax; x += majorStep) {
        const sx = toScreenX(x);
        ctx.moveTo(Math.round(sx) + 0.5, 0);
        ctx.lineTo(Math.round(sx) + 0.5, canvasHeight);
      }

      const startMajorY = Math.floor(yMin / majorStep) * majorStep;
      for (let y = startMajorY; y <= yMax; y += majorStep) {
        const sy = toScreenY(y);
        ctx.moveTo(0, Math.round(sy) + 0.5);
        ctx.lineTo(canvasWidth, Math.round(sy) + 0.5);
      }
      ctx.stroke();
    }

    // 3. Coordinate Axes (X and Y Axes)
    const originX = toScreenX(0);
    const originY = toScreenY(0);

    ctx.lineWidth = 2;
    ctx.strokeStyle = colors.axisLine;
    ctx.beginPath();

    // X-Axis
    const clampedY = Math.max(1, Math.min(canvasHeight - 1, originY));
    ctx.moveTo(0, clampedY);
    ctx.lineTo(canvasWidth, clampedY);

    // Y-Axis
    const clampedX = Math.max(1, Math.min(canvasWidth - 1, originX));
    ctx.moveTo(clampedX, 0);
    ctx.lineTo(clampedX, canvasHeight);
    ctx.stroke();

    // Axis Arrows
    ctx.fillStyle = colors.axisLine;
    // X-axis arrow at right
    ctx.beginPath();
    ctx.moveTo(canvasWidth - 12, clampedY - 5);
    ctx.lineTo(canvasWidth - 2, clampedY);
    ctx.lineTo(canvasWidth - 12, clampedY + 5);
    ctx.fill();

    // Y-axis arrow at top
    ctx.beginPath();
    ctx.moveTo(clampedX - 5, 12);
    ctx.lineTo(clampedX, 2);
    ctx.lineTo(clampedX + 5, 12);
    ctx.fill();

    // Axis Labels 'x' and 'y'
    ctx.font = '600 13px JetBrains Mono, monospace';
    ctx.fillStyle = colors.axisText;
    ctx.fillText('x', canvasWidth - 18, clampedY > 25 ? clampedY - 10 : clampedY + 20);
    ctx.fillText('y', clampedX < canvasWidth - 30 ? clampedX + 10 : clampedX - 20, 22);

    // 4. Axis Tick Numbers
    if (state.showNumbers) {
      ctx.font = '11px JetBrains Mono, monospace';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'top';

      const precision = majorStep >= 1 ? 0 : Math.min(4, Math.ceil(-Math.log10(majorStep)));

      // X-Axis Numbers
      const startX = Math.floor(xMin / majorStep) * majorStep;
      for (let x = startX; x <= xMax; x += majorStep) {
        if (Math.abs(x) < 1e-9) continue; // Skip zero at axis intersection
        const sx = toScreenX(x);
        if (sx < 25 || sx > canvasWidth - 25) continue;

        // Tick mark
        ctx.beginPath();
        ctx.moveTo(sx, clampedY - 4);
        ctx.lineTo(sx, clampedY + 4);
        ctx.strokeStyle = colors.axisLine;
        ctx.stroke();

        // Label
        const label = x.toFixed(precision);
        const textY = clampedY > canvasHeight - 25 ? clampedY - 18 : clampedY + 6;
        ctx.fillText(label, sx, textY);
      }

      // Y-Axis Numbers
      ctx.textAlign = 'right';
      ctx.textBaseline = 'middle';
      const startY = Math.floor(yMin / majorStep) * majorStep;
      for (let y = startY; y <= yMax; y += majorStep) {
        if (Math.abs(y) < 1e-9) continue;
        const sy = toScreenY(y);
        if (sy < 25 || sy > canvasHeight - 25) continue;

        // Tick mark
        ctx.beginPath();
        ctx.moveTo(clampedX - 4, sy);
        ctx.lineTo(clampedX + 4, sy);
        ctx.strokeStyle = colors.axisLine;
        ctx.stroke();

        // Label
        const label = y.toFixed(precision);
        const textX = clampedX < 45 ? clampedX + 28 : clampedX - 8;
        ctx.fillText(label, textX, sy);
      }

      // Origin "0" label
      if (originX >= 15 && originX <= canvasWidth - 15 && originY >= 15 && originY <= canvasHeight - 15) {
        ctx.textAlign = 'right';
        ctx.textBaseline = 'top';
        ctx.fillText('0', originX - 6, originY + 6);
      }
    }
  }

  // --- Function Curves Renderer (Continuous & Asymptote-Aware) ---
  function drawFunctionCurves() {
    const activeEquations = state.equations.filter(eq => eq.visible && eq.ast && !eq.error);

    activeEquations.forEach(eq => {
      ctx.save();
      ctx.strokeStyle = eq.color;
      ctx.lineWidth = 2.5;
      ctx.lineJoin = 'round';
      ctx.lineCap = 'round';

      // Subtle neon bloom glow in dark mode
      const isDark = document.documentElement.getAttribute('data-theme') === 'dark';
      if (isDark) {
        ctx.shadowColor = eq.color;
        ctx.shadowBlur = 6;
      }

      ctx.beginPath();
      let isDrawing = false;
      let prevScreenY = null;
      let prevMathY = null;

      // Sample every screen pixel horizontally across canvas
      const stepPixels = 1;
      for (let sx = 0; sx <= canvasWidth; sx += stepPixels) {
        const mx = toMathX(sx);
        const my = evaluateAST(eq.ast, mx);

        // Check for NaN or domain invalidity (e.g. sqrt(-1), log(-2))
        if (isNaN(my) || !isFinite(my)) {
          if (isDrawing) {
            ctx.stroke();
            ctx.beginPath();
            isDrawing = false;
          }
          prevScreenY = null;
          prevMathY = null;
          continue;
        }

        const sy = toScreenY(my);

        // Asymptote & vertical disconnect detection (e.g. tan(x), 1/x across vertical asymptote)
        if (prevMathY !== null && isDrawing) {
          const dy = sy - prevScreenY;
          // If rapid jump between opposite sides of infinity
          const massiveJump = Math.abs(dy) > canvasHeight * 0.85;
          const signFlipped = (my * prevMathY < 0);
          if (massiveJump && signFlipped) {
            ctx.stroke();
            ctx.beginPath();
            isDrawing = false;
          }
        }

        if (!isDrawing) {
          ctx.moveTo(sx, sy);
          isDrawing = true;
        } else {
          ctx.lineTo(sx, sy);
        }

        prevScreenY = sy;
        prevMathY = my;
      }

      if (isDrawing) {
        ctx.stroke();
      }
      ctx.restore();
    });
  }

  // --- Roots & Intercepts Highlighter ---
  function drawRootsAndIntercepts() {
    if (!state.detectRoots) return;

    const xMin = toMathX(0);
    const xMax = toMathX(canvasWidth);
    const activeEquations = state.equations.filter(eq => eq.visible && eq.ast && !eq.error);

    activeEquations.forEach(eq => {
      // 1. Y-Intercept: f(0)
      const yAtZero = evaluateAST(eq.ast, 0);
      if (isFinite(yAtZero) && !isNaN(yAtZero)) {
        const sx = toScreenX(0);
        const sy = toScreenY(yAtZero);
        if (sx >= 0 && sx <= canvasWidth && sy >= 0 && sy <= canvasHeight) {
          drawGlowPoint(sx, sy, eq.color, `(0, ${yAtZero.toFixed(2)})`);
        }
      }

      // 2. X-Intercepts (Roots): scan across visible domain
      const samples = 150;
      const step = (xMax - xMin) / samples;
      let prevX = xMin;
      let prevY = evaluateAST(eq.ast, prevX);

      for (let i = 1; i <= samples; i++) {
        const currX = xMin + i * step;
        const currY = evaluateAST(eq.ast, currX);

        if (isFinite(prevY) && isFinite(currY) && (prevY * currY <= 0)) {
          // Bisection method to isolate root precisely
          let low = prevX;
          let high = currX;
          let root = low;

          for (let iter = 0; iter < 18; iter++) {
            const mid = (low + high) / 2;
            const midY = evaluateAST(eq.ast, mid);
            root = mid;
            if (Math.abs(midY) < 1e-6) break;
            if (prevY * midY <= 0) {
              high = mid;
            } else {
              low = mid;
            }
          }

          const sx = toScreenX(root);
          const sy = toScreenY(0);
          if (sx >= 0 && sx <= canvasWidth && sy >= 0 && sy <= canvasHeight) {
            drawGlowPoint(sx, sy, eq.color, `Root: (${root.toFixed(2)}, 0)`);
          }
        }

        prevX = currX;
        prevY = currY;
      }
    });
  }

  function drawGlowPoint(sx, sy, color, label) {
    ctx.save();
    ctx.fillStyle = '#ffffff';
    ctx.strokeStyle = color;
    ctx.lineWidth = 2.5;

    ctx.beginPath();
    ctx.arc(sx, sy, 4.5, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();

    // Check if mouse is hovering nearby to show point label
    if (state.hoverMathX !== null) {
      const mouseScreenX = toScreenX(state.hoverMathX);
      const mouseScreenY = toScreenY(state.hoverMathY);
      const dist = Math.hypot(sx - mouseScreenX, sy - mouseScreenY);
      if (dist < 15) {
        ctx.font = '600 11px JetBrains Mono, monospace';
        ctx.fillStyle = color;
        ctx.fillText(label, sx + 8, sy - 8);
      }
    }
    ctx.restore();
  }

  // --- Interactive Inspector & Tangent Line Preview ---
  function drawCursorOverlay() {
    if (state.hoverMathX === null || state.isDragging) return;

    const sx = toScreenX(state.hoverMathX);
    const activeEquations = state.equations.filter(eq => eq.visible && eq.ast && !eq.error);

    // Vertical Crosshair Line
    ctx.save();
    ctx.strokeStyle = 'rgba(148, 163, 184, 0.4)';
    ctx.setLineDash([4, 4]);
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(sx, 0);
    ctx.lineTo(sx, canvasHeight);
    ctx.stroke();

    // Horizontal Crosshair Line
    const syMouse = toScreenY(state.hoverMathY);
    ctx.beginPath();
    ctx.moveTo(0, syMouse);
    ctx.lineTo(canvasWidth, syMouse);
    ctx.stroke();
    ctx.restore();

    // Points on each active curve at cursor X
    activeEquations.forEach(eq => {
      const my = evaluateAST(eq.ast, state.hoverMathX);
      if (isFinite(my) && !isNaN(my)) {
        const sy = toScreenY(my);
        if (sy >= -10 && sy <= canvasHeight + 10) {
          ctx.save();
          ctx.fillStyle = eq.color;
          ctx.strokeStyle = '#ffffff';
          ctx.lineWidth = 2;
          ctx.beginPath();
          ctx.arc(sx, sy, 5, 0, Math.PI * 2);
          ctx.fill();
          ctx.stroke();
          ctx.restore();

          // Tangent line at cursor X for the first active equation
          if (state.showTangent && eq === activeEquations[0]) {
            drawTangentLine(eq, state.hoverMathX, my, sx, sy);
          }
        }
      }
    });
  }

  function drawTangentLine(eq, x0, y0, sx0, sy0) {
    // Numerical central difference for derivative f'(x)
    const h = 1e-5;
    const yPlus = evaluateAST(eq.ast, x0 + h);
    const yMinus = evaluateAST(eq.ast, x0 - h);
    const slope = (yPlus - yMinus) / (2 * h);

    if (isFinite(slope) && !isNaN(slope)) {
      tangentSlopeVal.textContent = slope.toFixed(3);
      cursorTangentInfo.style.display = 'block';

      // Draw tangent line across canvas
      ctx.save();
      ctx.strokeStyle = '#f59e0b'; // Amber
      ctx.lineWidth = 1.8;
      ctx.setLineDash([6, 4]);

      const xMin = toMathX(0);
      const xMax = toMathX(canvasWidth);
      const yLeft = y0 + slope * (xMin - x0);
      const yRight = y0 + slope * (xMax - x0);

      ctx.beginPath();
      ctx.moveTo(toScreenX(xMin), toScreenY(yLeft));
      ctx.lineTo(toScreenX(xMax), toScreenY(yRight));
      ctx.stroke();
      ctx.restore();
    }
  }

  // --- Main Render Function ---
  function renderGraph() {
    const isDark = document.documentElement.getAttribute('data-theme') === 'dark';
    const colors = {
      canvasBg: isDark ? '#0b0f19' : '#fcfdff',
      gridMinor: isDark ? 'rgba(148, 163, 184, 0.08)' : 'rgba(71, 85, 105, 0.07)',
      gridMajor: isDark ? 'rgba(148, 163, 184, 0.22)' : 'rgba(71, 85, 105, 0.18)',
      axisLine: isDark ? '#94a3b8' : '#334155',
      axisText: isDark ? '#cbd5e1' : '#1e293b'
    };

    // Clear canvas
    ctx.clearRect(0, 0, canvasWidth, canvasHeight);

    // 1. Coordinate Grid & Axes
    drawCoordinateSystem(colors);

    // 2. Plotted Function Curves
    drawFunctionCurves();

    // 3. Roots & Intercepts Highlights
    drawRootsAndIntercepts();

    // 4. Cursor Crosshair & Tangent Line
    drawCursorOverlay();

    // 5. Update Floating Legend
    updateCanvasLegend();
  }

  // --- UI Updates: Equations List & Floating Badges ---

  function updateCanvasLegend() {
    canvasLegend.innerHTML = '';
    const active = state.equations.filter(eq => eq.visible && eq.ast && !eq.error);
    active.forEach(eq => {
      const chip = document.createElement('div');
      chip.className = 'legend-chip';
      chip.innerHTML = `
        <span class="legend-dot" style="--dot-color: ${eq.color}"></span>
        <span>y = ${escapeHTML(eq.text)}</span>
      `;
      canvasLegend.appendChild(chip);
    });
  }

  function escapeHTML(str) {
    return str.replace(/[&<>'"]/g, tag => ({
      '&': '&amp;',
      '<': '&lt;',
      '>': '&gt;',
      "'": '&#39;',
      '"': '&quot;'
    }[tag] || tag));
  }

  function renderEquationCards() {
    equationsContainer.innerHTML = '';
    const count = state.equations.filter(eq => eq.visible).length;
    equationCountBadge.textContent = `${count} active`;

    state.equations.forEach((eq, index) => {
      const card = document.createElement('div');
      card.className = `equation-card ${eq.error ? 'has-error' : ''}`;
      card.style.setProperty('--eq-color', eq.color);

      card.innerHTML = `
        <div class="equation-main-row">
          <div class="color-picker-wrapper" style="background-color: ${eq.color}" title="Change graph color">
            <input type="color" class="color-input-native" value="${eq.color}">
          </div>
          <span class="eq-prefix">f${index + 1}(x) =</span>
          <input type="text" class="eq-input-box" value="${escapeHTML(eq.text)}" placeholder="e.g. x^2, sin(x), 2x+1" spellcheck="false" autocomplete="off">
          <div class="eq-actions">
            <button class="eq-action-btn ${eq.visible ? 'active-visible' : ''}" data-action="toggle-visibility" title="${eq.visible ? 'Hide graph' : 'Show graph'}">
              <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                ${eq.visible ? 
                  `<path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z"></path><circle cx="12" cy="12" r="3"></circle>` :
                  `<path d="M17.94 17.94A10.07 10.07 0 0 1 12 20c-7 0-11-8-11-8a18.45 18.45 0 0 1 5.06-5.94M9.9 4.24A9.12 9.12 0 0 1 12 4c7 0 11 8 11 8a18.5 18.5 0 0 1-2.16 3.19m-6.72-1.07a3 3 0 1 1-4.24-4.24"></path><line x1="1" y1="1" x2="23" y2="23"></line>`
                }
              </svg>
            </button>
            <button class="eq-action-btn delete-btn" data-action="delete" title="Delete equation">
              <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <polyline points="3 6 5 6 21 6"></polyline>
                <path d="M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"></path>
              </svg>
            </button>
          </div>
        </div>
        <div class="eq-error-msg">${escapeHTML(eq.error || '')}</div>
      `;

      // Event Listeners for Equation Card
      const inputBox = card.querySelector('.eq-input-box');
      const colorInput = card.querySelector('.color-input-native');
      const colorWrapper = card.querySelector('.color-picker-wrapper');
      const btnToggle = card.querySelector('[data-action="toggle-visibility"]');
      const btnDelete = card.querySelector('[data-action="delete"]');

      // Track focus for keypad quick inserts
      inputBox.addEventListener('focus', () => {
        state.lastFocusedInput = inputBox;
      });

      // Live parsing & input change
      inputBox.addEventListener('input', (e) => {
        eq.text = e.target.value;
        const res = compileMathExpression(eq.text);
        eq.ast = res.ast;
        eq.error = res.error;

        const errDiv = card.querySelector('.eq-error-msg');
        if (eq.error) {
          card.classList.add('has-error');
          errDiv.textContent = eq.error;
        } else {
          card.classList.remove('has-error');
          errDiv.textContent = '';
        }
        renderGraph();
      });

      // Press Enter to plot
      inputBox.addEventListener('keydown', (e) => {
        if (e.key === 'Enter') {
          compileAllEquations();
          renderGraph();
        }
      });

      // Color change
      colorInput.addEventListener('input', (e) => {
        eq.color = e.target.value;
        colorWrapper.style.backgroundColor = eq.color;
        card.style.setProperty('--eq-color', eq.color);
        renderGraph();
      });

      // Visibility toggle
      btnToggle.addEventListener('click', () => {
        eq.visible = !eq.visible;
        renderEquationCards();
        renderGraph();
      });

      // Delete equation
      btnDelete.addEventListener('click', () => {
        if (state.equations.length <= 1) {
          // Clear text instead of deleting the last one
          eq.text = '';
          eq.ast = null;
          eq.error = null;
          renderEquationCards();
          renderGraph();
          return;
        }
        state.equations.splice(index, 1);
        renderEquationCards();
        renderGraph();
      });

      equationsContainer.appendChild(card);
    });
  }

  function compileAllEquations() {
    state.equations.forEach(eq => {
      const res = compileMathExpression(eq.text);
      eq.ast = res.ast;
      eq.error = res.error;
    });
    renderEquationCards();
  }

  // --- Zoom, Pan & Navigation Controllers ---

  function zoomAtPoint(factor, screenX = canvasWidth / 2, screenY = canvasHeight / 2) {
    const mathX = toMathX(screenX);
    const mathY = toMathY(screenY);

    const newScale = Math.max(state.minScale, Math.min(state.maxScale, state.scale * factor));
    if (newScale === state.scale) return;

    state.scale = newScale;
    state.centerX = mathX - (screenX - canvasWidth / 2) / state.scale;
    state.centerY = mathY + (screenY - canvasHeight / 2) / state.scale;

    updateRangeInputs();
    renderGraph();
  }

  function resetView() {
    state.centerX = 0;
    state.centerY = 0;
    state.scale = state.defaultScale;
    updateRangeInputs();
    renderGraph();
  }

  // Mouse wheel zoom centered on cursor
  canvas.addEventListener('wheel', (e) => {
    e.preventDefault();
    const factor = e.deltaY < 0 ? 1.15 : 0.87;
    zoomAtPoint(factor, e.offsetX, e.offsetY);
  }, { passive: false });

  // Canvas Mouse Pan & Drag
  canvas.addEventListener('mousedown', (e) => {
    if (e.button !== 0) return; // Only left click
    state.isDragging = true;
    state.dragStartX = e.clientX;
    state.dragStartY = e.clientY;
    state.dragCenterStartX = state.centerX;
    state.dragCenterStartY = state.centerY;
    canvas.style.cursor = 'grabbing';
  });

  window.addEventListener('mousemove', (e) => {
    if (state.isDragging) {
      const dx = e.clientX - state.dragStartX;
      const dy = e.clientY - state.dragStartY;
      state.centerX = state.dragCenterStartX - dx / state.scale;
      state.centerY = state.dragCenterStartY + dy / state.scale;
      updateRangeInputs();
      renderGraph();
      return;
    }

    // Live Hover Inspector
    const rect = canvas.getBoundingClientRect();
    const mx = e.clientX - rect.left;
    const my = e.clientY - rect.top;

    if (mx >= 0 && mx <= canvasWidth && my >= 0 && my <= canvasHeight) {
      state.hoverMathX = toMathX(mx);
      state.hoverMathY = toMathY(my);
      updateInspectorBadge(state.hoverMathX, state.hoverMathY);
      renderGraph();
    } else {
      state.hoverMathX = null;
      state.hoverMathY = null;
      cursorInspector.style.opacity = '0.5';
    }
  });

  window.addEventListener('mouseup', () => {
    if (state.isDragging) {
      state.isDragging = false;
      canvas.style.cursor = 'crosshair';
    }
  });

  // Touch Support for Mobile & Tablets
  let touchStartDist = 0;
  let touchStartScale = state.scale;

  canvas.addEventListener('touchstart', (e) => {
    if (e.touches.length === 1) {
      const t = e.touches[0];
      state.isDragging = true;
      state.dragStartX = t.clientX;
      state.dragStartY = t.clientY;
      state.dragCenterStartX = state.centerX;
      state.dragCenterStartY = state.centerY;
    } else if (e.touches.length === 2) {
      state.isDragging = false;
      touchStartDist = Math.hypot(
        e.touches[0].clientX - e.touches[1].clientX,
        e.touches[0].clientY - e.touches[1].clientY
      );
      touchStartScale = state.scale;
    }
  }, { passive: false });

  canvas.addEventListener('touchmove', (e) => {
    e.preventDefault();
    if (e.touches.length === 1 && state.isDragging) {
      const t = e.touches[0];
      const dx = t.clientX - state.dragStartX;
      const dy = t.clientY - state.dragStartY;
      state.centerX = state.dragCenterStartX - dx / state.scale;
      state.centerY = state.dragCenterStartY + dy / state.scale;
      updateRangeInputs();
      renderGraph();
    } else if (e.touches.length === 2 && touchStartDist > 0) {
      const dist = Math.hypot(
        e.touches[0].clientX - e.touches[1].clientX,
        e.touches[0].clientY - e.touches[1].clientY
      );
      const factor = dist / touchStartDist;
      state.scale = Math.max(state.minScale, Math.min(state.maxScale, touchStartScale * factor));
      updateRangeInputs();
      renderGraph();
    }
  }, { passive: false });

  canvas.addEventListener('touchend', () => {
    state.isDragging = false;
    touchStartDist = 0;
  });

  // --- Inspector Badge Content Updater ---
  function updateInspectorBadge(mathX, mathY) {
    cursorInspector.style.opacity = '1';
    cursorCoordVal.textContent = `x: ${mathX.toFixed(3)}, y: ${mathY.toFixed(3)}`;

    cursorFuncsList.innerHTML = '';
    const active = state.equations.filter(eq => eq.visible && eq.ast && !eq.error);

    active.forEach((eq, idx) => {
      const val = evaluateAST(eq.ast, mathX);
      const row = document.createElement('div');
      row.className = 'inspector-fn-row';
      row.innerHTML = `
        <span class="inspector-fn-name" style="color: ${eq.color}">f${idx + 1}(x):</span>
        <span class="inspector-fn-val">${isFinite(val) && !isNaN(val) ? val.toFixed(3) : 'undefined'}</span>
      `;
      cursorFuncsList.appendChild(row);
    });

    if (!state.showTangent) {
      cursorTangentInfo.style.display = 'none';
    }
  }

  // --- Primary Action Buttons Handlers ---

  // "Plot Graph"
  btnPlotGraph.addEventListener('click', () => {
    compileAllEquations();
    renderGraph();
  });

  // "Clear Graph"
  btnClearGraph.addEventListener('click', () => {
    state.equations = [
      { id: 'eq_1', text: '', color: COLOR_PALETTE[0], visible: true, ast: null, error: null }
    ];
    renderEquationCards();
    renderGraph();
  });

  // "Reset" view
  btnResetView.addEventListener('click', resetView);
  btnCanvasReset.addEventListener('click', resetView);

  // Zoom In & Zoom Out buttons
  btnZoomIn.addEventListener('click', () => zoomAtPoint(1.25));
  btnZoomOut.addEventListener('click', () => zoomAtPoint(0.8));

  // Add Equation button
  btnAddEquation.addEventListener('click', () => {
    const nextColor = COLOR_PALETTE[state.equations.length % COLOR_PALETTE.length];
    state.equations.push({
      id: `eq_${Date.now()}`,
      text: '',
      color: nextColor,
      visible: true,
      ast: null,
      error: null
    });
    renderEquationCards();
    // Focus new input
    const inputs = equationsContainer.querySelectorAll('.eq-input-box');
    if (inputs.length > 0) {
      inputs[inputs.length - 1].focus();
    }
  });

  // --- Quick Math Keypad Insertions ---
  keypadGrid.addEventListener('click', (e) => {
    const btn = e.target.closest('.key-btn');
    if (!btn) return;
    const insertStr = btn.getAttribute('data-insert');
    if (!insertStr) return;

    let targetInput = state.lastFocusedInput;
    if (!targetInput || !document.body.contains(targetInput)) {
      targetInput = equationsContainer.querySelector('.eq-input-box');
    }
    if (!targetInput) return;

    const start = targetInput.selectionStart || targetInput.value.length;
    const end = targetInput.selectionEnd || targetInput.value.length;
    const oldVal = targetInput.value;

    targetInput.value = oldVal.slice(0, start) + insertStr + oldVal.slice(end);
    targetInput.focus();
    targetInput.setSelectionRange(start + insertStr.length, start + insertStr.length);

    // Trigger input event
    targetInput.dispatchEvent(new Event('input'));
  });

  btnToggleKeypad.addEventListener('click', () => {
    if (keypadGrid.style.display === 'none') {
      keypadGrid.style.display = 'grid';
      btnToggleKeypad.textContent = 'Hide';
    } else {
      keypadGrid.style.display = 'none';
      btnToggleKeypad.textContent = 'Show';
    }
  });

  // --- Presets Dropdown Controller ---
  btnPresetsMenu.addEventListener('click', (e) => {
    e.stopPropagation();
    presetsDropdown.classList.toggle('show');
  });

  window.addEventListener('click', () => {
    presetsDropdown.classList.remove('show');
  });

  presetsDropdown.addEventListener('click', (e) => {
    const item = e.target.closest('[data-preset]');
    if (!item) return;
    const presetFormula = item.getAttribute('data-preset');

    // Either update focused input or add new equation
    let targetEq = null;
    if (state.lastFocusedInput && document.body.contains(state.lastFocusedInput)) {
      const card = state.lastFocusedInput.closest('.equation-card');
      const index = Array.from(equationsContainer.children).indexOf(card);
      if (index !== -1) {
        targetEq = state.equations[index];
      }
    }

    if (targetEq) {
      targetEq.text = presetFormula;
    } else {
      const nextColor = COLOR_PALETTE[state.equations.length % COLOR_PALETTE.length];
      state.equations.push({
        id: `eq_${Date.now()}`,
        text: presetFormula,
        color: nextColor,
        visible: true,
        ast: null,
        error: null
      });
    }

    compileAllEquations();
    renderGraph();
    presetsDropdown.classList.remove('show');
  });

  // --- Viewport Range Settings Inputs Controller ---
  btnApplyRanges.addEventListener('click', () => {
    const xMin = parseFloat(inputXMin.value);
    const xMax = parseFloat(inputXMax.value);
    const yMin = parseFloat(inputYMin.value);
    const yMax = parseFloat(inputYMax.value);

    if (isNaN(xMin) || isNaN(xMax) || isNaN(yMin) || isNaN(yMax) || xMin >= xMax || yMin >= yMax) {
      alert('Please enter valid numeric ranges with Min < Max.');
      return;
    }

    state.centerX = (xMin + xMax) / 2;
    state.centerY = (yMin + yMax) / 2;
    const scaleX = canvasWidth / (xMax - xMin);
    const scaleY = canvasHeight / (yMax - yMin);
    state.scale = Math.min(scaleX, scaleY);

    renderGraph();
  });

  chkShowGrid.addEventListener('change', (e) => {
    state.showGrid = e.target.checked;
    renderGraph();
  });

  chkShowNumbers.addEventListener('change', (e) => {
    state.showNumbers = e.target.checked;
    renderGraph();
  });

  chkDetectRoots.addEventListener('change', (e) => {
    state.detectRoots = e.target.checked;
    renderGraph();
  });

  // --- Tangent Line Inspector Toggle ---
  btnToggleTangent.addEventListener('click', () => {
    state.showTangent = !state.showTangent;
    tangentStatusText.textContent = `Tangent: ${state.showTangent ? 'On' : 'Off'}`;
    btnToggleTangent.classList.toggle('active-visible', state.showTangent);
    if (!state.showTangent) {
      cursorTangentInfo.style.display = 'none';
    }
    renderGraph();
  });

  // --- Dark / Light Mode Toggle ---
  function initTheme() {
    const savedTheme = localStorage.getItem('plotter_theme') || 'dark';
    document.documentElement.setAttribute('data-theme', savedTheme);
  }

  btnThemeToggle.addEventListener('click', () => {
    const current = document.documentElement.getAttribute('data-theme');
    const next = current === 'dark' ? 'light' : 'dark';
    document.documentElement.setAttribute('data-theme', next);
    localStorage.setItem('plotter_theme', next);
    renderGraph();
  });

  // --- Table of Values Modal Controller ---
  function populateTableOfValues() {
    const startX = parseFloat(tableStartInput.value);
    const endX = parseFloat(tableEndInput.value);
    const step = parseFloat(tableStepInput.value);

    if (isNaN(startX) || isNaN(endX) || isNaN(step) || step <= 0 || startX > endX) {
      alert('Invalid table range. Make sure start <= end and step > 0.');
      return;
    }

    // Build Table Header
    const active = state.equations.filter(eq => eq.visible && eq.ast && !eq.error);
    tableHeadRow.innerHTML = '<th>x</th>';
    active.forEach((eq, idx) => {
      const th = document.createElement('th');
      th.style.color = eq.color;
      th.textContent = `f${idx + 1}(x) = ${eq.text}`;
      tableHeadRow.appendChild(th);
    });

    // Build Table Rows
    tableBody.innerHTML = '';
    const maxRows = 200; // Safeguard
    let count = 0;

    for (let x = startX; x <= endX + 1e-9 && count < maxRows; x += step, count++) {
      const tr = document.createElement('tr');
      const cleanX = Math.round(x * 1000) / 1000;
      let rowHtml = `<td>${cleanX}</td>`;

      active.forEach(eq => {
        const yVal = evaluateAST(eq.ast, cleanX);
        const displayVal = isFinite(yVal) && !isNaN(yVal) ? yVal.toFixed(4) : 'undefined';
        rowHtml += `<td>${displayVal}</td>`;
      });

      tr.innerHTML = rowHtml;
      tableBody.appendChild(tr);
    }
  }

  btnOpenTable.addEventListener('click', () => {
    populateTableOfValues();
    tableModal.classList.add('show');
  });

  btnCloseTableModal.addEventListener('click', () => tableModal.classList.remove('show'));
  btnCloseTableModalBtn.addEventListener('click', () => tableModal.classList.remove('show'));
  btnRefreshTable.addEventListener('click', populateTableOfValues);

  btnCopyTable.addEventListener('click', () => {
    const table = document.getElementById('valuesTable');
    let text = '';
    for (let r of table.rows) {
      const rowData = Array.from(r.cells).map(c => c.textContent.trim());
      text += rowData.join('\t') + '\n';
    }
    navigator.clipboard.writeText(text).then(() => {
      const old = btnCopyTable.textContent;
      btnCopyTable.textContent = 'Copied to Clipboard!';
      setTimeout(() => btnCopyTable.textContent = old, 1800);
    });
  });

  // --- Help Guide Modal ---
  btnOpenHelp.addEventListener('click', () => helpModal.classList.add('show'));
  btnCloseHelpModal.addEventListener('click', () => helpModal.classList.remove('show'));
  btnCloseHelpModalBtn.addEventListener('click', () => helpModal.classList.remove('show'));

  // Close modals when clicking backdrop
  window.addEventListener('click', (e) => {
    if (e.target === tableModal) tableModal.classList.remove('show');
    if (e.target === helpModal) helpModal.classList.remove('show');
  });

  // --- Export Graph to Image (PNG) ---
  btnExportImage.addEventListener('click', () => {
    // Render high resolution snapshot
    const link = document.createElement('a');
    link.download = `graph-plot-${Date.now()}.png`;
    link.href = canvas.toDataURL('image/png');
    link.click();
  });

  // --- Initialization ---
  function init() {
    initTheme();
    compileAllEquations();
    resizeCanvas();
    window.addEventListener('resize', resizeCanvas);
  }

  // Run when DOM ready
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

})();
