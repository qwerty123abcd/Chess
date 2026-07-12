/* ============================================================
   ENDGAME — a small, self-contained chess implementation.
   Board convention: row 0 = rank 8 (top), row 7 = rank 1 (bottom).
                      col 0 = file a,      col 7 = file h.
   ============================================================ */

const FILES = ['a','b','c','d','e','f','g','h'];

const UNICODE = {
  w: { p:'♙', n:'♘', b:'♗', r:'♖', q:'♕', k:'♔' },
  b: { p:'♟', n:'♞', b:'♝', r:'♜', q:'♛', k:'♚' }
};

const PIECE_VALUE = { p:100, n:320, b:330, r:500, q:900, k:20000 };

const KNIGHT_OFFSETS = [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]];
const KING_OFFSETS   = [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]];
const ROOK_DIRS      = [[-1,0],[1,0],[0,-1],[0,1]];
const BISHOP_DIRS    = [[-1,-1],[-1,1],[1,-1],[1,1]];

function inBounds(r,c){ return r>=0 && r<8 && c>=0 && c<8; }
function sq(r,c){ return FILES[c] + (8-r); }

function cloneBoard(board){
  return board.map(row => row.map(cell => cell ? {...cell} : null));
}

function freshBoard(){
  const back = ['r','n','b','q','k','b','n','r'];
  const board = Array.from({length:8}, () => Array(8).fill(null));
  for(let c=0;c<8;c++){
    board[0][c] = { type: back[c], color: 'b' };
    board[1][c] = { type: 'p', color: 'b' };
    board[6][c] = { type: 'p', color: 'w' };
    board[7][c] = { type: back[c], color: 'w' };
  }
  return board;
}

/* ---------------- Game state ---------------- */

let game = null;

function newGame(){
  game = {
    board: freshBoard(),
    turn: 'w',
    castling: { wK:true, wQ:true, bK:true, bQ:true },
    enPassant: null,        // {r,c} square a pawn could capture into
    history: [],            // list of {move, notation, snapshotBefore}
    capturedByWhite: [],     // black pieces white has taken
    capturedByBlack: [],     // white pieces black has taken
    over: false,
    result: null,
    flipped: false,
    mode: 'two-player',
    difficulty: 'medium',
    selected: null,
    legalMovesForSelected: []
  };
  render();
  updateStatus();
}

/* ---------------- Attack / check detection ---------------- */

function isSquareAttacked(board, r, c, byColor){
  const pawnDir = byColor === 'w' ? 1 : -1;
  for(const dc of [-1,1]){
    const pr = r + pawnDir, pc = c + dc;
    if(inBounds(pr,pc)){
      const p = board[pr][pc];
      if(p && p.color === byColor && p.type === 'p') return true;
    }
  }
  for(const [dr,dc] of KNIGHT_OFFSETS){
    const nr=r+dr, nc=c+dc;
    if(inBounds(nr,nc)){
      const p = board[nr][nc];
      if(p && p.color === byColor && p.type === 'n') return true;
    }
  }
  for(const [dr,dc] of KING_OFFSETS){
    const nr=r+dr, nc=c+dc;
    if(inBounds(nr,nc)){
      const p = board[nr][nc];
      if(p && p.color === byColor && p.type === 'k') return true;
    }
  }
  for(const [dr,dc] of ROOK_DIRS){
    let nr=r+dr, nc=c+dc;
    while(inBounds(nr,nc)){
      const p = board[nr][nc];
      if(p){
        if(p.color === byColor && (p.type==='r' || p.type==='q')) return true;
        break;
      }
      nr+=dr; nc+=dc;
    }
  }
  for(const [dr,dc] of BISHOP_DIRS){
    let nr=r+dr, nc=c+dc;
    while(inBounds(nr,nc)){
      const p = board[nr][nc];
      if(p){
        if(p.color === byColor && (p.type==='b' || p.type==='q')) return true;
        break;
      }
      nr+=dr; nc+=dc;
    }
  }
  return false;
}

function findKing(board, color){
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(p && p.color===color && p.type==='k') return {r,c};
  }
  return null;
}

function inCheck(board, color){
  const k = findKing(board, color);
  if(!k) return false;
  return isSquareAttacked(board, k.r, k.c, color==='w' ? 'b' : 'w');
}

/* ---------------- Pseudo-legal move generation ---------------- */

function generatePieceMoves(board, r, c, state){
  const piece = board[r][c];
  if(!piece) return [];
  const moves = [];
  const color = piece.color;
  const enemy = color === 'w' ? 'b' : 'w';

  const addSlide = (dirs) => {
    for(const [dr,dc] of dirs){
      let nr=r+dr, nc=c+dc;
      while(inBounds(nr,nc)){
        const target = board[nr][nc];
        if(!target){
          moves.push({ from:{r,c}, to:{r:nr,c:nc} });
        } else {
          if(target.color === enemy) moves.push({ from:{r,c}, to:{r:nr,c:nc}, capture:true });
          break;
        }
        nr+=dr; nc+=dc;
      }
    }
  };

  if(piece.type === 'p'){
    const dir = color === 'w' ? -1 : 1;
    const startRow = color === 'w' ? 6 : 1;
    const promoRow = color === 'w' ? 0 : 7;
    const oneR = r+dir;
    if(inBounds(oneR,c) && !board[oneR][c]){
      if(oneR === promoRow){
        for(const promo of ['q','r','b','n']) moves.push({from:{r,c}, to:{r:oneR,c}, promotion:promo});
      } else {
        moves.push({from:{r,c}, to:{r:oneR,c}});
        const twoR = r+dir*2;
        if(r===startRow && !board[twoR][c]){
          moves.push({from:{r,c}, to:{r:twoR,c}, doubleStep:true});
        }
      }
    }
    for(const dc of [-1,1]){
      const nr=r+dir, nc=c+dc;
      if(!inBounds(nr,nc)) continue;
      const target = board[nr][nc];
      if(target && target.color===enemy){
        if(nr===promoRow){
          for(const promo of ['q','r','b','n']) moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true, promotion:promo});
        } else {
          moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true});
        }
      } else if(state.enPassant && state.enPassant.r===nr && state.enPassant.c===nc){
        moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true, enPassant:true});
      }
    }
  }
  else if(piece.type === 'n'){
    for(const [dr,dc] of KNIGHT_OFFSETS){
      const nr=r+dr, nc=c+dc;
      if(!inBounds(nr,nc)) continue;
      const target = board[nr][nc];
      if(!target) moves.push({from:{r,c}, to:{r:nr,c:nc}});
      else if(target.color===enemy) moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true});
    }
  }
  else if(piece.type === 'b'){ addSlide(BISHOP_DIRS); }
  else if(piece.type === 'r'){ addSlide(ROOK_DIRS); }
  else if(piece.type === 'q'){ addSlide(ROOK_DIRS); addSlide(BISHOP_DIRS); }
  else if(piece.type === 'k'){
    for(const [dr,dc] of KING_OFFSETS){
      const nr=r+dr, nc=c+dc;
      if(!inBounds(nr,nc)) continue;
      const target = board[nr][nc];
      if(!target) moves.push({from:{r,c}, to:{r:nr,c:nc}});
      else if(target.color===enemy) moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true});
    }
    // Castling
    const enemyColor = enemy;
    const rights = state.castling;
    const homeRow = color==='w' ? 7 : 0;
    if(r===homeRow && c===4 && !inCheck(board,color)){
      const kingSideRight = color==='w' ? rights.wK : rights.bK;
      const queenSideRight = color==='w' ? rights.wQ : rights.bQ;
      if(kingSideRight && !board[homeRow][5] && !board[homeRow][6] &&
         board[homeRow][7] && board[homeRow][7].type==='r' && board[homeRow][7].color===color &&
         !isSquareAttacked(board, homeRow, 5, enemyColor) &&
         !isSquareAttacked(board, homeRow, 6, enemyColor)){
        moves.push({from:{r,c}, to:{r:homeRow,c:6}, castle:'K'});
      }
      if(queenSideRight && !board[homeRow][3] && !board[homeRow][2] && !board[homeRow][1] &&
         board[homeRow][0] && board[homeRow][0].type==='r' && board[homeRow][0].color===color &&
         !isSquareAttacked(board, homeRow, 3, enemyColor) &&
         !isSquareAttacked(board, homeRow, 2, enemyColor)){
        moves.push({from:{r,c}, to:{r:homeRow,c:2}, castle:'Q'});
      }
    }
  }
  return moves;
}

function generateAllMoves(board, color, state){
  let moves = [];
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(p && p.color===color) moves.push(...generatePieceMoves(board,r,c,state));
  }
  return moves;
}

/* Apply a move to a board+state pair, returning nothing (mutates copies passed in) */
function applyMove(board, state, move){
  const piece = board[move.from.r][move.from.c];
  const color = piece.color;
  let captured = null;

  if(move.enPassant){
    const capRow = move.from.r;
    const capCol = move.to.c;
    captured = board[capRow][capCol];
    board[capRow][capCol] = null;
  } else if(board[move.to.r][move.to.c]){
    captured = board[move.to.r][move.to.c];
  }

  board[move.to.r][move.to.c] = { type: move.promotion || piece.type, color };
  board[move.from.r][move.from.c] = null;

  if(move.castle){
    const homeRow = move.from.r;
    if(move.castle === 'K'){
      board[homeRow][5] = board[homeRow][7];
      board[homeRow][7] = null;
    } else {
      board[homeRow][3] = board[homeRow][0];
      board[homeRow][0] = null;
    }
  }

  // update castling rights
  if(piece.type === 'k'){
    if(color==='w'){ state.castling.wK=false; state.castling.wQ=false; }
    else { state.castling.bK=false; state.castling.bQ=false; }
  }
  if(piece.type === 'r'){
    if(color==='w' && move.from.r===7 && move.from.c===0) state.castling.wQ=false;
    if(color==='w' && move.from.r===7 && move.from.c===7) state.castling.wK=false;
    if(color==='b' && move.from.r===0 && move.from.c===0) state.castling.bQ=false;
    if(color==='b' && move.from.r===0 && move.from.c===7) state.castling.bK=false;
  }
  if(captured && captured.type==='r'){
    if(move.to.r===7 && move.to.c===0) state.castling.wQ=false;
    if(move.to.r===7 && move.to.c===7) state.castling.wK=false;
    if(move.to.r===0 && move.to.c===0) state.castling.bQ=false;
    if(move.to.r===0 && move.to.c===7) state.castling.bK=false;
  }

  // update en passant target
  if(move.doubleStep){
    const midRow = (move.from.r + move.to.r) / 2;
    state.enPassant = { r: midRow, c: move.from.c };
  } else {
    state.enPassant = null;
  }

  return captured;
}

/* Legal moves = pseudo moves that don't leave own king in check */
function legalMovesFrom(r,c){
  const board = game.board;
  const piece = board[r][c];
  if(!piece || piece.color !== game.turn) return [];
  const pseudo = generatePieceMoves(board, r, c, game);
  const legal = [];
  for(const move of pseudo){
    const b2 = cloneBoard(board);
    const s2 = { castling: {...game.castling}, enPassant: game.enPassant };
    applyMove(b2, s2, move);
    if(!inCheck(b2, piece.color)) legal.push(move);
  }
  return legal;
}

function allLegalMoves(color){
  const board = game.board;
  let moves = [];
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(p && p.color===color){
      const pseudo = generatePieceMoves(board, r, c, game);
      for(const move of pseudo){
        const b2 = cloneBoard(board);
        const s2 = { castling: {...game.castling}, enPassant: game.enPassant };
        applyMove(b2, s2, move);
        if(!inCheck(b2, color)) moves.push(move);
      }
    }
  }
  return moves;
}

/* ---------------- Notation ---------------- */

function moveNotation(move, piece, wasCapture, checkChar){
  if(move.castle === 'K') return 'O-O' + checkChar;
  if(move.castle === 'Q') return 'O-O-O' + checkChar;
  const files = 'abcdefgh';
  let s = '';
  if(piece.type !== 'p'){
    s += piece.type.toUpperCase();
    if(wasCapture) s += 'x';
  } else if(wasCapture){
    s += files[move.from.c] + 'x';
  }
  s += sq(move.to.r, move.to.c);
  if(move.promotion) s += '=' + move.promotion.toUpperCase();
  s += checkChar;
  return s;
}

/* ---------------- Making a real move on the live game ---------------- */

function playMove(move){
  const board = game.board;
  const piece = board[move.from.r][move.from.c];
  const color = piece.color;
  const wasCapture = !!move.capture || !!board[move.to.r][move.to.c];

  const snapshot = {
    board: cloneBoard(board),
    turn: game.turn,
    castling: {...game.castling},
    enPassant: game.enPassant
  };

  const captured = applyMove(board, game, move);
  if(captured){
    if(color==='w') game.capturedByWhite.push(captured);
    else game.capturedByBlack.push(captured);
  }

  game.turn = color === 'w' ? 'b' : 'w';

  const opponentInCheck = inCheck(board, game.turn);
  const opponentMoves = allLegalMoves(game.turn);
  let checkChar = '';
  let gameOver = false;
  let resultText = null;

  if(opponentMoves.length === 0){
    gameOver = true;
    if(opponentInCheck){
      checkChar = '#';
      resultText = (color==='w' ? 'White' : 'Black') + ' wins by checkmate';
    } else {
      resultText = 'Draw by stalemate';
    }
  } else if(opponentInCheck){
    checkChar = '+';
  }

  const notation = moveNotation(move, piece, wasCapture, checkChar);
  game.history.push({ notation, snapshot, color, captured, move });
  game.over = gameOver;
  game.result = resultText;

  game.lastMove = { from: move.from, to: move.to };
  game.selected = null;
  game.legalMovesForSelected = [];

  render();
  updateMoveList();
  updateCaptures();
  updateStatus();

  if(!gameOver && game.mode === 'computer' && game.turn === 'b'){
    setTimeout(computerMove, 350);
  }
}

function undoMove(){
  if(game.history.length === 0) return;
  const last = game.history.pop();
  game.board = last.snapshot.board;
  game.turn = last.snapshot.turn;
  game.castling = last.snapshot.castling;
  game.enPassant = last.snapshot.enPassant;
  game.over = false;
  game.result = null;
  game.selected = null;
  game.legalMovesForSelected = [];

  if(last.captured){
    const list = last.color === 'w' ? game.capturedByWhite : game.capturedByBlack;
    list.pop();
  }

  game.lastMove = game.history.length
    ? game.history[game.history.length - 1].move || null
    : null;

  render();
  updateMoveList();
  updateCaptures();
  updateStatus();
}

/* ---------------- Simple AI (minimax + alpha-beta, depth 3) ---------------- */

function evaluateBoard(board){
  let score = 0;
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(!p) continue;
    const val = PIECE_VALUE[p.type];
    score += p.color === 'w' ? val : -val;
  }
  return score; // positive favors white
}

function orderMoves(moves, board){
  return moves.slice().sort((a,b) => {
    const scoreOf = (m) => {
      let s = 0;
      const target = board[m.to.r][m.to.c];
      if(target) s += PIECE_VALUE[target.type];
      if(m.promotion) s += PIECE_VALUE[m.promotion];
      return s;
    };
    return scoreOf(b) - scoreOf(a);
  });
}

function minimax(board, state, depth, alpha, beta, maximizing){
  if(depth === 0){
    return evaluateBoard(board);
  }
  const color = maximizing ? 'w' : 'b';
  let moves = [];
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(p && p.color===color) moves.push(...generatePieceMoves(board, r, c, state));
  }
  // filter to legal
  const legal = [];
  for(const m of moves){
    const b2 = cloneBoard(board);
    const s2 = { castling: {...state.castling}, enPassant: state.enPassant };
    applyMove(b2, s2, m);
    if(!inCheck(b2, color)) legal.push(m);
  }
  if(legal.length === 0){
    if(inCheck(board, color)) return maximizing ? -100000 - depth : 100000 + depth;
    return 0;
  }
  const ordered = orderMoves(legal, board);

  if(maximizing){
    let best = -Infinity;
    for(const m of ordered){
      const b2 = cloneBoard(board);
      const s2 = { castling: {...state.castling}, enPassant: state.enPassant };
      applyMove(b2, s2, m);
      const val = minimax(b2, s2, depth-1, alpha, beta, false);
      best = Math.max(best, val);
      alpha = Math.max(alpha, val);
      if(beta <= alpha) break;
    }
    return best;
  } else {
    let best = Infinity;
    for(const m of ordered){
      const b2 = cloneBoard(board);
      const s2 = { castling: {...state.castling}, enPassant: state.enPassant };
      applyMove(b2, s2, m);
      const val = minimax(b2, s2, depth-1, alpha, beta, true);
      best = Math.min(best, val);
      beta = Math.min(beta, val);
      if(beta <= alpha) break;
    }
    return best;
  }
}

const DIFFICULTY_DEPTH = { easy: 1, medium: 2, hard: 3 };

function computerMove(){
  if(game.over) return;
  const moves = allLegalMoves('b');
  if(moves.length === 0) return;

  // Easy mode: mostly random, with only a mild preference for not hanging pieces for free.
  if(game.difficulty === 'easy' && Math.random() < 0.7){
    const chosen = moves[Math.floor(Math.random()*moves.length)];
    playMove(chosen);
    return;
  }

  const depth = DIFFICULTY_DEPTH[game.difficulty] || 2;
  const ordered = orderMoves(moves, game.board);
  let bestMoves = [];
  let bestScore = Infinity;
  for(const m of ordered){
    const b2 = cloneBoard(game.board);
    const s2 = { castling: {...game.castling}, enPassant: game.enPassant };
    applyMove(b2, s2, m);
    const score = minimax(b2, s2, depth, -Infinity, Infinity, true);
    if(score < bestScore){
      bestScore = score;
      bestMoves = [m];
    } else if(score === bestScore){
      bestMoves.push(m);
    }
  }
  const chosen = bestMoves[Math.floor(Math.random()*bestMoves.length)];
  playMove(chosen);
}

/* ---------------- Rendering ---------------- */

const boardEl = document.getElementById('board');
const statusEl = document.getElementById('status');
const moveListEl = document.getElementById('moveList');
const capturedByWhiteEl = document.getElementById('capturedByWhite');
const capturedByBlackEl = document.getElementById('capturedByBlack');
const promoModal = document.getElementById('promoModal');
const promoChoices = document.getElementById('promoChoices');

function displayCoords(){
  const rows = game.flipped ? [...Array(8).keys()] : [...Array(8).keys()].reverse();
  const cols = game.flipped ? [...Array(8).keys()].reverse() : [...Array(8).keys()];
  return { rows, cols };
}

function render(){
  boardEl.innerHTML = '';
  const { rows, cols } = displayCoords();

  for(const r of rows){
    for(const c of cols){
      const square = document.createElement('div');
      const isLight = (r+c) % 2 === 0;
      square.className = 'square ' + (isLight ? 'light' : 'dark');
      square.dataset.r = r;
      square.dataset.c = c;

      if(game.lastMove && ((game.lastMove.from.r===r && game.lastMove.from.c===c) || (game.lastMove.to.r===r && game.lastMove.to.c===c))){
        square.classList.add('last-move');
      }

      if(game.selected && game.selected.r===r && game.selected.c===c){
        square.classList.add('selected');
      }

      const piece = game.board[r][c];
      if(piece){
        const span = document.createElement('span');
        span.className = 'piece ' + (piece.color === 'w' ? 'piece-white' : 'piece-black');
        span.textContent = UNICODE[piece.color][piece.type];
        square.appendChild(span);

        if(piece.type === 'k' && inCheck(game.board, piece.color)){
          square.classList.add('king-check');
        }
      }

      const isLegalTarget = game.legalMovesForSelected.find(m => m.to.r===r && m.to.c===c);
      if(isLegalTarget){
        const marker = document.createElement('div');
        marker.className = piece ? 'capture-ring' : 'move-dot';
        square.appendChild(marker);
      }

      square.addEventListener('click', onSquareClick);
      boardEl.appendChild(square);
    }
  }
}

function onSquareClick(e){
  if(game.over) return;
  if(game.mode === 'computer' && game.turn === 'b') return;

  const r = parseInt(e.currentTarget.dataset.r, 10);
  const c = parseInt(e.currentTarget.dataset.c, 10);
  const piece = game.board[r][c];

  if(game.selected){
    const move = game.legalMovesForSelected.find(m => m.to.r===r && m.to.c===c);
    if(move){
      if(move.promotion){
        askPromotion(move.to.r, move.to.c, (chosen) => {
          const promoMove = game.legalMovesForSelected.find(m => m.to.r===r && m.to.c===c && m.promotion===chosen);
          playMove(promoMove);
        });
        return;
      }
      playMove(move);
      return;
    }
    if(piece && piece.color === game.turn){
      game.selected = {r,c};
      game.legalMovesForSelected = legalMovesFrom(r,c);
      render();
      return;
    }
    game.selected = null;
    game.legalMovesForSelected = [];
    render();
    return;
  }

  if(piece && piece.color === game.turn){
    game.selected = {r,c};
    game.legalMovesForSelected = legalMovesFrom(r,c);
    render();
  }
}

function askPromotion(r, c, callback){
  const color = game.turn;
  promoChoices.innerHTML = '';
  for(const type of ['q','r','b','n']){
    const btn = document.createElement('button');
    btn.textContent = UNICODE[color][type];
    btn.addEventListener('click', () => {
      promoModal.classList.add('hidden');
      callback(type);
    });
    promoChoices.appendChild(btn);
  }
  promoModal.classList.remove('hidden');
}

function updateStatus(){
  statusEl.classList.remove('check','win');
  if(game.over){
    statusEl.textContent = game.result;
    statusEl.classList.add('win');
    return;
  }
  const turnName = game.turn === 'w' ? 'White' : 'Black';
  if(inCheck(game.board, game.turn)){
    statusEl.textContent = turnName + ' is in check';
    statusEl.classList.add('check');
  } else {
    statusEl.textContent = turnName + ' to move';
  }
}

function updateMoveList(){
  moveListEl.innerHTML = '';
  const moves = game.history.map(h => h.notation);
  for(let i=0; i<moves.length; i+=2){
    const li = document.createElement('li');
    const num = document.createElement('span');
    num.className = 'mv-num';
    num.textContent = (i/2 + 1) + '.';
    const white = document.createElement('span');
    white.className = 'mv-white';
    white.textContent = moves[i] || '';
    const black = document.createElement('span');
    black.className = 'mv-black';
    black.textContent = moves[i+1] || '';
    li.appendChild(num);
    li.appendChild(white);
    li.appendChild(black);
    moveListEl.appendChild(li);
  }
  moveListEl.scrollTop = moveListEl.scrollHeight;
}

function updateCaptures(){
  capturedByWhiteEl.textContent = game.capturedByWhite.map(p => UNICODE['b'][p.type]).join(' ');
  capturedByBlackEl.textContent = game.capturedByBlack.map(p => UNICODE['w'][p.type]).join(' ');
}

/* ---------------- Controls ---------------- */

document.getElementById('newGameBtn').addEventListener('click', () => {
  const mode = game ? game.mode : 'two-player';
  const difficulty = game ? game.difficulty : 'medium';
  newGame();
  game.mode = mode;
  game.difficulty = difficulty;
});

document.getElementById('undoBtn').addEventListener('click', undoMove);

document.getElementById('flipBtn').addEventListener('click', () => {
  game.flipped = !game.flipped;
  render();
});

document.getElementById('modeToggle').addEventListener('click', (e) => {
  const btn = e.target.closest('.mode-option');
  if(!btn) return;
  document.querySelectorAll('#modeToggle .mode-option').forEach(b => b.classList.remove('active'));
  btn.classList.add('active');
  game.mode = btn.dataset.mode;
  difficultyToggleEl.classList.toggle('hidden', game.mode !== 'computer');
});

const difficultyToggleEl = document.getElementById('difficultyToggle');
difficultyToggleEl.addEventListener('click', (e) => {
  const btn = e.target.closest('.mode-option');
  if(!btn) return;
  document.querySelectorAll('#difficultyToggle .mode-option').forEach(b => b.classList.remove('active'));
  btn.classList.add('active');
  game.difficulty = btn.dataset.difficulty;
});

/* ---------------- Boot ---------------- */

newGame();