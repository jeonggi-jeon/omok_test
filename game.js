/**
 * 15×15 오목: 흑(사용자) / 백(AI), 정확히 5연속만 승.
 * 돌은 격자 교차점에 둠. 흑 차례에 20초 내 미착수 시 백 차례로 넘김.
 */
(function () {
  const SIZE = 15;
  const EMPTY = 0;
  const BLACK = 1;
  const WHITE = 2;
  const MOVE_LIMIT_SEC = 20;
  /** 백(AI) 착수 전 “생각” 대기(밀리초) — 랜덤으로 약간씩 달라짐 */
  const AI_THINK_MIN_MS = 650;
  const AI_THINK_MAX_MS = 1550;

  const boardEl = document.getElementById("board");
  const pointsEl = document.getElementById("board-points");
  const statusEl = document.getElementById("status");
  const lastMoveEl = document.getElementById("last-move");
  const restartEl = document.getElementById("restart");
  const winDialog = document.getElementById("win-dialog");
  const loseDialog = document.getElementById("lose-dialog");
  const timerPanel = document.getElementById("timer-panel");
  const timerLabel = document.getElementById("timer-label");
  const timerFill = document.getElementById("timer-fill");
  const welcomeLayer = document.getElementById("welcome-layer");
  const btnStart = document.getElementById("btn-start");

  /** @type {number[][]} */
  let board;
  let gameOver = false;
  /** 게임 시작 버튼을 누른 뒤에만 true */
  let matchLive = false;
  /** 흑(사용자)이 둘 차례일 때만 true */
  let humanTurn = false;
  /** @type {ReturnType<typeof setInterval> | null} */
  let turnTimerId = null;
  /** 백 차례: 1초 간격 카운트다운(흑과 동일 속도), 착수는 별도 thinkMs 타임아웃 */
  /** @type {ReturnType<typeof setInterval> | null} */
  let aiThinkTickId = null;
  /** @type {ReturnType<typeof setTimeout> | null} */
  let aiPlaceTimeoutId = null;
  /** @type {HTMLElement[]} */
  let cells;

  function buildGrid() {
    pointsEl.replaceChildren();
    cells = [];
    board = Array.from({ length: SIZE }, () => Array(SIZE).fill(EMPTY));
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        const btn = document.createElement("button");
        btn.type = "button";
        btn.className = "pt empty";
        btn.dataset.r = String(r);
        btn.dataset.c = String(c);
        btn.style.setProperty("--pr", String(r));
        btn.style.setProperty("--pc", String(c));
        btn.setAttribute("role", "gridcell");
        btn.setAttribute("aria-rowindex", String(r + 1));
        btn.setAttribute("aria-colindex", String(c + 1));
        btn.setAttribute("aria-label", `빈 교차점 ${r + 1}행 ${c + 1}열`);
        pointsEl.appendChild(btn);
        cells.push(btn);
      }
    }
  }

  function idx(r, c) {
    return r * SIZE + c;
  }

  function paintCell(r, c) {
    const el = cells[idx(r, c)];
    const v = board[r][c];
    el.classList.remove("empty", "black", "white");
    if (v === EMPTY) {
      el.classList.add("pt", "empty");
      el.setAttribute("aria-label", `빈 교차점 ${r + 1}행 ${c + 1}열`);
      el.disabled = false;
    } else if (v === BLACK) {
      el.classList.add("pt", "black");
      el.setAttribute("aria-label", `흑 ${r + 1}행 ${c + 1}열`);
      el.disabled = true;
    } else {
      el.classList.add("pt", "white");
      el.setAttribute("aria-label", `백 ${r + 1}행 ${c + 1}열`);
      el.disabled = true;
    }
  }

  function countLine(r, c, dr, dc, player) {
    let n = 0;
    let rr = r + dr;
    let cc = c + dc;
    while (rr >= 0 && rr < SIZE && cc >= 0 && cc < SIZE && board[rr][cc] === player) {
      n++;
      rr += dr;
      cc += dc;
    }
    rr = r - dr;
    cc = c - dc;
    while (rr >= 0 && rr < SIZE && cc >= 0 && cc < SIZE && board[rr][cc] === player) {
      n++;
      rr -= dr;
      cc -= dc;
    }
    return n + 1;
  }

  /** 정확히 5연속만 승 (6목 이상은 승 아님) */
  function isExactFiveWin(r, c, player) {
    const dirs = [
      [0, 1],
      [1, 0],
      [1, 1],
      [1, -1],
    ];
    for (const [dr, dc] of dirs) {
      const line = countLine(r, c, dr, dc, player);
      if (line === 5) return true;
    }
    return false;
  }

  /** 승리한 방향에서 연속 5칸 좌표 (마지막 착수 기준) */
  function collectWinningFive(r, c, player) {
    const dirs = [
      [0, 1],
      [1, 0],
      [1, 1],
      [1, -1],
    ];
    for (const [dr, dc] of dirs) {
      if (countLine(r, c, dr, dc, player) !== 5) continue;
      let rr = r;
      let cc = c;
      while (
        rr - dr >= 0 &&
        rr - dr < SIZE &&
        cc - dc >= 0 &&
        cc - dc < SIZE &&
        board[rr - dr][cc - dc] === player
      ) {
        rr -= dr;
        cc -= dc;
      }
      const out = [];
      for (let i = 0; i < 5; i++) {
        out.push({ r: rr, c: cc });
        rr += dr;
        cc += dc;
      }
      return out;
    }
    return [];
  }

  function highlightWinningFive(r, c, player) {
    for (const { r: rr, c: cc } of collectWinningFive(r, c, player)) {
      cells[idx(rr, cc)].classList.add("win-line");
    }
  }

  /** @type {{ r: number; c: number } | null} */
  let lastBlackPos = null;
  /** @type {{ r: number; c: number } | null} */
  let lastWhitePos = null;

  function refreshPlacementSummary() {
    const fmt = (p) => (p ? `${p.r + 1}행 ${p.c + 1}열` : "—");
    lastMoveEl.textContent = `착수 위치 · 흑 ${fmt(lastBlackPos)} · 백 ${fmt(lastWhitePos)}`;
  }

  function recordMove(player, r, c) {
    if (player === BLACK) lastBlackPos = { r, c };
    else lastWhitePos = { r, c };
    refreshPlacementSummary();
  }

  function clearPlacementHistory() {
    lastBlackPos = null;
    lastWhitePos = null;
    refreshPlacementSummary();
  }

  function stopTurnTimer() {
    if (turnTimerId !== null) {
      clearInterval(turnTimerId);
      turnTimerId = null;
    }
  }

  function stopAiThinkTimer() {
    if (aiThinkTickId !== null) {
      clearInterval(aiThinkTickId);
      aiThinkTickId = null;
    }
    if (aiPlaceTimeoutId !== null) {
      clearTimeout(aiPlaceTimeoutId);
      aiPlaceTimeoutId = null;
    }
  }

  function updateTimerDisplay(secondsLeft, active) {
    if (!timerPanel || !timerLabel || !timerFill) return;
    const bar = timerPanel.querySelector(".timer-bar");
    if (!active || gameOver) {
      timerPanel.classList.add("timer-idle");
      timerPanel.classList.remove("timer-urgent", "timer-ai");
      timerLabel.textContent = "—";
      timerFill.style.width = "0%";
      if (bar) bar.setAttribute("aria-valuenow", "0");
      return;
    }
    timerPanel.classList.remove("timer-idle", "timer-ai");
    timerLabel.textContent = `${secondsLeft}초`;
    timerFill.style.width = `${(secondsLeft / MOVE_LIMIT_SEC) * 100}%`;
    timerPanel.classList.toggle("timer-urgent", secondsLeft <= 5);
    if (bar) {
      bar.setAttribute("aria-valuenow", String(secondsLeft));
      bar.setAttribute("aria-valuemax", String(MOVE_LIMIT_SEC));
    }
  }

  /** 백 차례 타이머 — 실시간 1초마다 감소(흑과 동일). 막대 비율도 초 기준. */
  function updateAiCountdownDisplay(secondsLeft) {
    if (!timerPanel || !timerLabel || !timerFill || gameOver) return;
    const bar = timerPanel.querySelector(".timer-bar");
    timerPanel.classList.remove("timer-idle");
    timerPanel.classList.add("timer-ai");
    timerLabel.textContent = `${secondsLeft}초`;
    timerFill.style.width = `${(secondsLeft / MOVE_LIMIT_SEC) * 100}%`;
    timerPanel.classList.toggle("timer-urgent", secondsLeft <= 5);
    if (bar) {
      bar.setAttribute("aria-valuenow", String(secondsLeft));
      bar.setAttribute("aria-valuemax", String(MOVE_LIMIT_SEC));
    }
  }

  function startTurnTimer() {
    stopTurnTimer();
    stopAiThinkTimer();
    if (gameOver || !humanTurn) {
      updateTimerDisplay(0, false);
      return;
    }
    let sec = MOVE_LIMIT_SEC;
    updateTimerDisplay(sec, true);
    turnTimerId = setInterval(() => {
      sec -= 1;
      if (sec <= 0) {
        stopTurnTimer();
        onTurnTimeout();
        return;
      }
      updateTimerDisplay(sec, true);
    }, 1000);
  }

  function closeAllDialogs() {
    if (winDialog && winDialog.open) winDialog.close();
    if (loseDialog && loseDialog.open) loseDialog.close();
  }

  function endGame(message, options) {
    stopTurnTimer();
    stopAiThinkTimer();
    humanTurn = false;
    gameOver = true;
    statusEl.textContent = message;
    updateTimerDisplay(0, false);
    const opt = options || {};
    if (
      opt.winLine &&
      typeof opt.winR === "number" &&
      typeof opt.winC === "number" &&
      (opt.winPlayer === BLACK || opt.winPlayer === WHITE)
    ) {
      highlightWinningFive(opt.winR, opt.winC, opt.winPlayer);
    }
    for (const el of cells) {
      if (board[+el.dataset.r][+el.dataset.c] === EMPTY) el.disabled = true;
    }
    if (opt.congratulate && winDialog && typeof winDialog.showModal === "function") {
      winDialog.showModal();
    }
    if (opt.condolences && loseDialog && typeof loseDialog.showModal === "function") {
      loseDialog.showModal();
    }
  }

  function pickRandomEmpty() {
    const empties = [];
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] === EMPTY) empties.push([r, c]);
      }
    }
    if (!empties.length) return null;
    const i = Math.floor(Math.random() * empties.length);
    return empties[i];
  }

  const DIRS = [
    [0, 1],
    [1, 0],
    [1, 1],
    [1, -1],
  ];

  const SC = {
    WIN: 10_000_000,
    OPEN_FOUR: 500_000,
    RUSH_FOUR: 120_000,
    OPEN_THREE: 9_000,
    RUSH_THREE: 2_200,
    OPEN_TWO: 180,
    RUSH_TWO: 45,
    OVERLINE_PEN: 50_000,
    NEIGHBOR_BONUS: 8,
  };

  function inBounds(r, c) {
    return r >= 0 && r < SIZE && c >= 0 && c < SIZE;
  }

  function walkArm(r, c, dr, dc, player) {
    let n = 0;
    let rr = r + dr;
    let cc = c + dc;
    while (inBounds(rr, cc) && board[rr][cc] === player) {
      n++;
      rr += dr;
      cc += dc;
    }
    let beyond = EMPTY;
    if (!inBounds(rr, cc)) beyond = -1;
    else beyond = board[rr][cc];
    return { n, beyond };
  }

  function axisAfterMove(r, c, dr, dc, player) {
    const a = walkArm(r, c, dr, dc, player);
    const b = walkArm(r, c, -dr, -dc, player);
    const total = 1 + a.n + b.n;
    return { total, capA: a.beyond, capB: b.beyond };
  }

  function isCapOpen(cap) {
    return cap === EMPTY;
  }

  function axisScore(ax) {
    const { total, capA, capB } = ax;
    const oa = isCapOpen(capA);
    const ob = isCapOpen(capB);
    const opens = (oa ? 1 : 0) + (ob ? 1 : 0);

    if (total >= 6) return -SC.OVERLINE_PEN;
    if (total === 5) return SC.WIN;

    if (total === 4) {
      if (opens === 2) return SC.OPEN_FOUR;
      if (opens === 1) return SC.RUSH_FOUR;
      return SC.RUSH_FOUR / 6;
    }
    if (total === 3) {
      if (opens === 2) return SC.OPEN_THREE;
      if (opens === 1) return SC.RUSH_THREE;
      return SC.RUSH_THREE / 5;
    }
    if (total === 2) {
      if (opens === 2) return SC.OPEN_TWO;
      if (opens === 1) return SC.RUSH_TWO;
      return SC.RUSH_TWO / 4;
    }
    if (total === 1) {
      if (opens === 2) return SC.OPEN_TWO / 10;
    }
    return 0;
  }

  function evaluateHypothetical(r, c, player) {
    if (board[r][c] !== EMPTY) return -1e15;
    board[r][c] = player;
    let s = 0;
    for (const [dr, dc] of DIRS) {
      s += axisScore(axisAfterMove(r, c, dr, dc, player));
    }
    if (isExactFiveWin(r, c, player)) s = Math.max(s, SC.WIN);
    board[r][c] = EMPTY;
    return s;
  }

  function winsIfPlays(r, c, player) {
    if (board[r][c] !== EMPTY) return false;
    board[r][c] = player;
    const ok = isExactFiveWin(r, c, player);
    board[r][c] = EMPTY;
    return ok;
  }

  function nearestStoneDist(r, c) {
    let best = 99;
    for (let rr = 0; rr < SIZE; rr++) {
      for (let cc = 0; cc < SIZE; cc++) {
        if (board[rr][cc] === EMPTY) continue;
        const d = Math.max(Math.abs(rr - r), Math.abs(cc - c));
        if (d < best) best = d;
      }
    }
    return best;
  }

  /** 인접한 백(본인) 돌 개수 — 연장·포위 공격 유도 */
  function adjacentFriendlyCount(r, c, player) {
    let n = 0;
    for (let dr = -1; dr <= 1; dr++) {
      for (let dc = -1; dc <= 1; dc++) {
        if (dr === 0 && dc === 0) continue;
        const rr = r + dr;
        const cc = c + dc;
        if (inBounds(rr, cc) && board[rr][cc] === player) n++;
      }
    }
    return n;
  }

  function collectCandidates() {
    let hasStone = false;
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) {
          hasStone = true;
          break;
        }
      }
      if (hasStone) break;
    }
    const out = [];
    if (!hasStone) {
      for (let r = 0; r < SIZE; r++) {
        for (let c = 0; c < SIZE; c++) {
          if (board[r][c] === EMPTY) out.push([r, c]);
        }
      }
      return out;
    }
    const seen = new Set();
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] === EMPTY) continue;
        for (let dr = -2; dr <= 2; dr++) {
          for (let dc = -2; dc <= 2; dc++) {
            const nr = r + dr;
            const nc = c + dc;
            if (!inBounds(nr, nc) || board[nr][nc] !== EMPTY) continue;
            const key = nr * SIZE + nc;
            if (seen.has(key)) continue;
            seen.add(key);
            out.push([nr, nc]);
          }
        }
      }
    }
    if (!out.length) {
      for (let r = 0; r < SIZE; r++) {
        for (let c = 0; c < SIZE; c++) {
          if (board[r][c] === EMPTY) out.push([r, c]);
        }
      }
    }
    return out;
  }

  function pickAiMove() {
    const candidates = collectCandidates();
    if (!candidates.length) return null;

    let best = -Infinity;
    let picks = [];

    for (const [r, c] of candidates) {
      if (board[r][c] !== EMPTY) continue;
      if (winsIfPlays(r, c, WHITE)) return [r, c];
    }

    for (const [r, c] of candidates) {
      if (board[r][c] !== EMPTY) continue;
      if (winsIfPlays(r, c, BLACK)) return [r, c];
    }

    const center = (SIZE - 1) / 2;
    /** 공격 위주: 백 자신 패턴은 강하게, 흑 방어는 약하게 반영 */
    const ATT_WEIGHT = 1.42;
    const DEF_WEIGHT = 0.84;
    /** 내 돌 옆을 우선 — 적극적으로 모양 붙이기 */
    const EXTEND_BONUS = 165;

    for (const [r, c] of candidates) {
      if (board[r][c] !== EMPTY) continue;
      const attack = evaluateHypothetical(r, c, WHITE);
      const defense = evaluateHypothetical(r, c, BLACK);
      let score = attack * ATT_WEIGHT + defense * DEF_WEIGHT;
      score += adjacentFriendlyCount(r, c, WHITE) * EXTEND_BONUS;
      const nd = nearestStoneDist(r, c);
      if (nd < 99) score += (4 - Math.min(nd, 4)) * SC.NEIGHBOR_BONUS;

      if (score > best) {
        best = score;
        picks = [[r, c]];
      } else if (score === best) {
        picks.push([r, c]);
      }
    }

    picks.sort((a, b) => {
      const da = Math.abs(a[0] - center) + Math.abs(a[1] - center);
      const db = Math.abs(b[0] - center) + Math.abs(b[1] - center);
      if (da !== db) return da - db;
      if (a[0] !== b[0]) return a[0] - b[0];
      return a[1] - b[1];
    });
    return picks[0] || null;
  }

  function aiMove() {
    const pick = pickAiMove() || pickRandomEmpty();
    if (!pick) {
      endGame("무승부 (판 가득 참)");
      return;
    }
    const [r, c] = pick;
    board[r][c] = WHITE;
    paintCell(r, c);
    recordMove(WHITE, r, c);
    if (isExactFiveWin(r, c, WHITE)) {
      endGame("패배했습니다 (백이 5연속).", {
        condolences: true,
        winLine: true,
        winR: r,
        winC: c,
        winPlayer: WHITE,
      });
      return;
    }
    if (!pickRandomEmpty()) {
      endGame("무승부 (판 가득 참)");
      return;
    }
    statusEl.textContent = "당신의 차례입니다 (흑)";
    humanTurn = true;
    for (const el of cells) {
      if (board[+el.dataset.r][+el.dataset.c] === EMPTY) el.disabled = false;
    }
    startTurnTimer();
  }

  function runAiTurn() {
    stopTurnTimer();
    stopAiThinkTimer();
    statusEl.textContent = "컴퓨터(백)가 생각하는 중…";
    for (const el of cells) {
      if (board[+el.dataset.r][+el.dataset.c] === EMPTY) el.disabled = true;
    }
    const thinkMs =
      AI_THINK_MIN_MS + Math.random() * (AI_THINK_MAX_MS - AI_THINK_MIN_MS);

    let sec = MOVE_LIMIT_SEC;
    updateAiCountdownDisplay(sec);

    aiThinkTickId = setInterval(() => {
      if (gameOver) {
        stopAiThinkTimer();
        updateTimerDisplay(0, false);
        return;
      }
      sec -= 1;
      if (sec <= 0) {
        stopAiThinkTimer();
        updateAiCountdownDisplay(0);
        if (!gameOver) aiMove();
        return;
      }
      updateAiCountdownDisplay(sec);
    }, 1000);

    aiPlaceTimeoutId = setTimeout(() => {
      aiPlaceTimeoutId = null;
      if (gameOver) return;
      if (aiThinkTickId !== null) {
        clearInterval(aiThinkTickId);
        aiThinkTickId = null;
      }
      if (!gameOver) aiMove();
    }, thinkMs);
  }

  function onTurnTimeout() {
    if (!matchLive || gameOver || !humanTurn) return;
    humanTurn = false;
    stopTurnTimer();
    stopAiThinkTimer();
    updateTimerDisplay(0, false);
    statusEl.textContent = "시간 초과 — 흑 착수 없음, 백이 둡니다.";
    runAiTurn();
  }

  function onBoardClick(e) {
    if (!matchLive || gameOver || !humanTurn) return;
    const btn = e.target.closest(".pt");
    if (!btn || btn.disabled) return;
    const r = +btn.dataset.r;
    const c = +btn.dataset.c;
    if (board[r][c] !== EMPTY) return;

    humanTurn = false;
    stopTurnTimer();
    stopAiThinkTimer();
    updateTimerDisplay(0, false);

    board[r][c] = BLACK;
    paintCell(r, c);
    recordMove(BLACK, r, c);

    if (isExactFiveWin(r, c, BLACK)) {
      endGame("승리! 흑 5연속입니다.", {
        congratulate: true,
        winLine: true,
        winR: r,
        winC: c,
        winPlayer: BLACK,
      });
      return;
    }

    if (!pickRandomEmpty()) {
      endGame("무승부 (판 가득 참)");
      return;
    }

    runAiTurn();
  }

  function resetUi() {
    closeAllDialogs();
    stopTurnTimer();
    stopAiThinkTimer();
    gameOver = false;
    matchLive = true;
    if (welcomeLayer) welcomeLayer.hidden = true;
    buildGrid();
    clearPlacementHistory();
    statusEl.textContent = "당신의 차례입니다 (흑)";
    humanTurn = true;
    if (restartEl) restartEl.disabled = false;
    startTurnTimer();
  }

  function initPreGame() {
    closeAllDialogs();
    stopTurnTimer();
    stopAiThinkTimer();
    matchLive = false;
    humanTurn = false;
    gameOver = false;
    buildGrid();
    clearPlacementHistory();
    statusEl.textContent = "게임 시작 버튼을 눌러 주세요.";
    updateTimerDisplay(0, false);
    if (welcomeLayer) welcomeLayer.hidden = false;
    if (restartEl) restartEl.disabled = true;
    for (const el of cells) el.disabled = true;
    if (btnStart) btnStart.focus();
  }

  pointsEl.addEventListener("click", onBoardClick);
  restartEl.addEventListener("click", resetUi);
  if (btnStart) btnStart.addEventListener("click", resetUi);

  initPreGame();
})();
