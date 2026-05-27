
const TT = new Map();

const EMPTY = 0;

const WHITE = 1;
const BLACK = -1;

const PAWN   = 1;
const KNIGHT = 2;
const BISHOP = 3;
const ROOK   = 4;
const QUEEN  = 5;
const KING   = 6;

let pendingPromotionMove = null;
let promotionChoices = ["q", "r", "b", "n"];
let currentDifficulty = "grandmaster"; 
let lastMove = null; // { fromFile, fromRank, toFile, toRank }
let humanSide = WHITE;
const NULL_MOVE_R = 2;      // reduction
const NULL_MOVE_MIN_DEPTH = 3; // only do at depth >= 3
const TT_SIZE = 10000000000000;

const PIECE_NONE = 0;
// Map your internal piece codes to 0..N-1
// Example (adapt to your engine):
// 1: white pawn, 2: white knight, ..., 7: black pawn, etc.

let zobristPiece = [];   // [square][piece]
let zobristSide;         // side to move
let zobristCastling = []; // castling rights index
let zobristEnPassant = []; // file index (0-7) or 8 = none

let zobristKey = 0n;     // BigInt for safety



const DIFFICULTY = {
  easy:    { depth: 1, noise: 0.40, blunder: 0.30 },
  normal:  { depth: 2, noise: 0.20, blunder: 0.10 },
  hard:    { depth: 3, noise: 0.05, blunder: 0.02 },
  insane:  { depth: 4, noise: 0.01, blunder: 0.004 },
  master:  { depth: 5, noise: 0.001, blunder: 0.001 },
  grandmaster:  { depth: 7, noise: 0.0001, blunder: 0.0001 }
};

class Position {
  constructor() {
    this.board = this.createStartBoard();
    this.sideToMove = WHITE;

    this.castlingRights = {
      whiteKingSide: true,
      whiteQueenSide: true,
      blackKingSide: true,
      blackQueenSide: true
    };

    this.enPassantSquare = null; // {file, rank} or null
    this.halfmoveClock = 0;
    this.fullmoveNumber = 1;
  }

  createStartBoard() {
    const b = [];
    for (let r = 0; r < 8; r++) {
      b[r] = new Array(8).fill(EMPTY);
    }

    // place pieces (simple encoding: color * pieceType)
    // white
    b[7] = [
      WHITE * ROOK, WHITE * KNIGHT, WHITE * BISHOP, WHITE * QUEEN,
      WHITE * KING, WHITE * BISHOP, WHITE * KNIGHT, WHITE * ROOK
    ];
    b[6] = new Array(8).fill(WHITE * PAWN);

    // black
    b[0] = [
      BLACK * ROOK, BLACK * KNIGHT, BLACK * BISHOP, BLACK * QUEEN,
      BLACK * KING, BLACK * BISHOP, BLACK * KNIGHT, BLACK * ROOK
    ];
    b[1] = new Array(8).fill(BLACK * PAWN);

    return b;
  }

  clone() {
    const p = new Position();
    p.board = this.board.map(row => row.slice());
    p.sideToMove = this.sideToMove;
    p.castlingRights = { ...this.castlingRights };
    p.enPassantSquare = this.enPassantSquare ? { ...this.enPassantSquare } : null;
    p.halfmoveClock = this.halfmoveClock;
    p.fullmoveNumber = this.fullmoveNumber;
    return p;
  }
}
class Move {
  constructor(fromFile, fromRank, toFile, toRank, options = {}) {
    this.fromFile = fromFile;
    this.fromRank = fromRank;
    this.toFile = toFile;
    this.toRank = toRank;

    this.promotion = options.promotion || null; // piece type
    this.isEnPassant = !!options.isEnPassant;
    this.isCastling = !!options.isCastling;
    this.capturedPiece = options.capturedPiece || null; // filled when making move
  }
}
function inBounds(f, r) {
  return f >= 0 && f < 8 && r >= 0 && r < 8;
}

function pieceColor(piece) {
  if (piece === EMPTY) return 0;
  return piece > 0 ? WHITE : BLACK;
}
Position.prototype.generatePseudoLegalMoves = function() {
  const moves = [];
  const side = this.sideToMove;

  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      const piece = this.board[r][f];
      if (piece === EMPTY) continue;
      if (pieceColor(piece) !== side) continue;

      const type = pieceType(piece);
      if (type === PAWN) {
        this.generatePawnMoves(f, r, moves);
      } else if (type === KNIGHT) {
        this.generateKnightMoves(f, r, moves);
      } else if (type === BISHOP) {
        this.generateSlidingMoves(f, r, moves, [
          [1,1], [1,-1], [-1,1], [-1,-1]
        ]);
      } else if (type === ROOK) {
        this.generateSlidingMoves(f, r, moves, [
          [1,0], [-1,0], [0,1], [0,-1]
        ]);
      } else if (type === QUEEN) {
        this.generateSlidingMoves(f, r, moves, [
          [1,1], [1,-1], [-1,1], [-1,-1],
          [1,0], [-1,0], [0,1], [0,-1]
        ]);
      } else if (type === KING) {
        this.generateKingMoves(f, r, moves);
      }
    }
  }

  return moves;
};

Position.prototype.isSquareAttackedBy = function(f, r, attackerColor) {

  // --- Pawn attacks ---
  const pawnDir = attackerColor === WHITE ? -1 : 1;
  const pawnRanks = r + pawnDir;
  for (const df of [-1, 1]) {
    const pf = f + df;
    if (inBounds(pf, pawnRanks)) {
      const piece = this.board[pawnRanks][pf];
      if (piece === attackerColor * PAWN) return true;
    }
  }

  // --- Knight attacks ---
  const knightOffsets = [
    [1,2], [2,1], [-1,2], [-2,1],
    [1,-2], [2,-1], [-1,-2], [-2,-1]
  ];
  for (const [df, dr] of knightOffsets) {
    const nf = f + df, nr = r + dr;
    if (!inBounds(nf, nr)) continue;
    if (this.board[nr][nf] === attackerColor * KNIGHT) return true;
  }

  // --- Sliding attacks (Bishop/Queen) ---
  const bishopDirs = [[1,1],[1,-1],[-1,1],[-1,-1]];
  for (const [df, dr] of bishopDirs) {
    let nf = f + df, nr = r + dr;
    while (inBounds(nf, nr)) {
      const piece = this.board[nr][nf];
      if (piece !== EMPTY) {
        if (piece === attackerColor * BISHOP ||
            piece === attackerColor * QUEEN) return true;
        break;
      }
      nf += df; nr += dr;
    }
  }

  // --- Sliding attacks (Rook/Queen) ---
  const rookDirs = [[1,0],[-1,0],[0,1],[0,-1]];
  for (const [df, dr] of rookDirs) {
    let nf = f + df, nr = r + dr;
    while (inBounds(nf, nr)) {
      const piece = this.board[nr][nf];
      if (piece !== EMPTY) {
        if (piece === attackerColor * ROOK ||
            piece === attackerColor * QUEEN) return true;
        break;
      }
      nf += df; nr += dr;
    }
  }

  // --- King attacks ---
  const kingOffsets = [
    [1,0], [-1,0], [0,1], [0,-1],
    [1,1], [1,-1], [-1,1], [-1,-1]
  ];
  for (const [df, dr] of kingOffsets) {
    const nf = f + df, nr = r + dr;
    if (!inBounds(nf, nr)) continue;
    if (this.board[nr][nf] === attackerColor * KING) return true;
  }

  return false;
};


Position.prototype.inCheck = function(color) {
  let kingFile = -1, kingRank = -1;

  // find king
  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      if (this.board[r][f] === color * KING) {
        kingFile = f;
        kingRank = r;
        break;
      }
    }
  }

  return this.isSquareAttackedBy(kingFile, kingRank, -color);
};


Position.prototype.generateLegalMoves = function() {
  const pseudo = this.generatePseudoLegalMoves();
  const legal = [];

  for (const m of pseudo) {
    const clone = this.clone();
    clone.makeMove(m);
    if (!clone.inCheck(this.sideToMove)) { // original side
      legal.push(m);
    }
  }

  return legal;
};

Position.prototype.generatePawnMoves = function(f, r, moves) {
  const side = this.sideToMove;
  const dir = side === WHITE ? -1 : 1;
  const startRank = side === WHITE ? 6 : 1;
  const promotionRank = side === WHITE ? 0 : 7;

  const oneStepR = r + dir;
  if (inBounds(f, oneStepR) && this.board[oneStepR][f] === EMPTY) {
    // normal move or promotion
    if (oneStepR === promotionRank) {
      [QUEEN, ROOK, BISHOP, KNIGHT].forEach(promo => {
        moves.push(new Move(f, r, f, oneStepR, { promotion: promo }));
      });
    } else {
      moves.push(new Move(f, r, f, oneStepR));
    }

    // two-step from start
    if (r === startRank) {
      const twoStepR = r + 2 * dir;
      if (this.board[twoStepR][f] === EMPTY) {
        moves.push(new Move(f, r, f, twoStepR));
      }
    }
  }

  // captures
  for (const df of [-1, 1]) {
    const cf = f + df;
    const cr = r + dir;
    if (!inBounds(cf, cr)) continue;

    const target = this.board[cr][cf];

    // normal capture
    if (target !== EMPTY && pieceColor(target) === -side) {
      if (cr === promotionRank) {
        [QUEEN, ROOK, BISHOP, KNIGHT].forEach(promo => {
          moves.push(new Move(f, r, cf, cr, { promotion: promo }));
        });
      } else {
        moves.push(new Move(f, r, cf, cr));
      }
    }

    // en passant
    if (this.enPassantSquare &&
        this.enPassantSquare.file === cf &&
        this.enPassantSquare.rank === cr &&
        target === EMPTY) {
      moves.push(new Move(f, r, cf, cr, { isEnPassant: true }));
    }
  }
};
Position.prototype.makeMove = function(move) {
  const fromPiece = this.board[move.fromRank][move.fromFile];
  const side = this.sideToMove;
  // reset en passant by default
  this.enPassantSquare = null;

  // handle en passant capture
  if (move.isEnPassant) {
    const dir = side === WHITE ? -1 : 1;
    const capRank = move.toRank - dir;
    move.capturedPiece = this.board[capRank][move.toFile];
    this.board[capRank][move.toFile] = EMPTY;
  } else {
    move.capturedPiece = this.board[move.toRank][move.toFile];
  }

  // move piece
  this.board[move.fromRank][move.fromFile] = EMPTY;

  let placedPiece = fromPiece;

  // promotion
  if (move.promotion) {
    placedPiece = side * move.promotion;
  }

  this.board[move.toRank][move.toFile] = placedPiece;

  // pawn two-step → set en passant square
  if (pieceType(fromPiece) === PAWN && Math.abs(move.toRank - move.fromRank) === 2) {
    const epRank = (move.fromRank + move.toRank) / 2;
    this.enPassantSquare = { file: move.fromFile, rank: epRank };
  }

  if (move.isCastling) {
  const rank = move.fromRank; // king's rank (0 for black, 7 for white)

  if (move.toFile === 6) { // king-side
    const rookFrom = 7;
    const rookTo = 5;
    this.board[rank][rookTo] = this.board[rank][rookFrom];
    this.board[rank][rookFrom] = EMPTY;
  } else if (move.toFile === 2) { // queen-side
    const rookFrom = 0;
    const rookTo = 3;
    this.board[rank][rookTo] = this.board[rank][rookFrom];
    this.board[rank][rookFrom] = EMPTY;
  }
      // if king moves, remove both rights
if (pieceType(fromPiece) === KING) {
  if (side === WHITE) {
    this.castlingRights.whiteKingSide = false;
    this.castlingRights.whiteQueenSide = false;
  } else {
    this.castlingRights.blackKingSide = false;
    this.castlingRights.blackQueenSide = false;
  }
}

// if rook moves or is captured, remove that side's right
if (pieceType(fromPiece) === ROOK) {
  if (side === WHITE) {
    if (move.fromFile === 0 && move.fromRank === 7) this.castlingRights.whiteQueenSide = false;
    if (move.fromFile === 7 && move.fromRank === 7) this.castlingRights.whiteKingSide = false;
  } else {
    if (move.fromFile === 0 && move.fromRank === 0) this.castlingRights.blackQueenSide = false;
    if (move.fromFile === 7 && move.fromRank === 0) this.castlingRights.blackKingSide = false;
  }
}
}



  // update clocks
  if (pieceType(fromPiece) === PAWN || move.capturedPiece !== EMPTY) {
    this.halfmoveClock = 0;
  } else {
    this.halfmoveClock++;
  }

  if (side === BLACK) {
    this.fullmoveNumber++;
  }

  // switch side
  this.sideToMove = -side;
};
Position.prototype.generateKnightMoves = function(f, r, moves) {
  const side = this.sideToMove;
  const offsets = [
    [1,2], [2,1], [-1,2], [-2,1],
    [1,-2], [2,-1], [-1,-2], [-2,-1]
  ];

  for (const [df, dr] of offsets) {
    const nf = f + df;
    const nr = r + dr;
    if (!inBounds(nf, nr)) continue;

    const target = this.board[nr][nf];
    if (target === EMPTY || pieceColor(target) === -side) {
      moves.push(new Move(f, r, nf, nr));
    }
  }
};
Position.prototype.generateSlidingMoves = function(f, r, moves, directions) {
  const side = this.sideToMove;

  for (const [df, dr] of directions) {
    let nf = f + df;
    let nr = r + dr;

    while (inBounds(nf, nr)) {
      const target = this.board[nr][nf];

      if (target === EMPTY) {
        moves.push(new Move(f, r, nf, nr));
      } else {
        if (pieceColor(target) === -side) {
          moves.push(new Move(f, r, nf, nr));
        }
        break; // blocked
      }

      nf += df;
      nr += dr;
    }
  }
};

Position.prototype.generateKingMoves = function(f, r, moves) {
  const side = this.sideToMove;
  const offsets = [
    [1,0], [-1,0], [0,1], [0,-1],
    [1,1], [1,-1], [-1,1], [-1,-1]
  ];

  for (const [df, dr] of offsets) {
    const nf = f + df;
    const nr = r + dr;
    if (!inBounds(nf, nr)) continue;

    const target = this.board[nr][nf];
    if (target === EMPTY || pieceColor(target) === -side) {
      moves.push(new Move(f, r, nf, nr));
    }
  }

  this.generateCastlingMoves(f, r, moves);
};
Position.prototype.generateCastlingMoves = function(f, r, moves) {
  const side = this.sideToMove;

  const kingSide = side === WHITE
    ? this.castlingRights.whiteKingSide
    : this.castlingRights.blackKingSide;

  const queenSide = side === WHITE
    ? this.castlingRights.whiteQueenSide
    : this.castlingRights.blackQueenSide;

  // King must not be in check
  if (this.inCheck(side)) return;

  // KING SIDE CASTLING
  if (kingSide) {
    // squares between king and rook must be empty
    if (this.board[r][f+1] === EMPTY &&
        this.board[r][f+2] === EMPTY) {

      // squares king passes through must not be attacked
      if (!this.isSquareAttackedBy(f+1, r, -side) &&
          !this.isSquareAttackedBy(f+2, r, -side)) {

        moves.push(new Move(f, r, f+2, r, { isCastling: true }));
      }
    }
  }

  // QUEEN SIDE CASTLING
  if (queenSide) {
    if (this.board[r][f-1] === EMPTY &&
        this.board[r][f-2] === EMPTY &&
        this.board[r][f-3] === EMPTY) {

      if (!this.isSquareAttackedBy(f-1, r, -side) &&
          !this.isSquareAttackedBy(f-2, r, -side)) {

        moves.push(new Move(f, r, f-2, r, { isCastling: true }));
      }
    }
  }

};
Position.prototype.generateLegalMoves = function() {
  const pseudo = this.generatePseudoLegalMoves();
  const legal = [];

  for (const move of pseudo) {
    const clone = this.clone();
    clone.makeMove(move);

    // after move, sideToMove has flipped
    if (!clone.inCheck(-clone.sideToMove)) {
      legal.push(move);
    }
  }

  return legal;
};

function pieceType(piece) {
  return Math.abs(piece);
}

let position;
let engine;
  class ChessEngine {
  constructor() {
     this.position = null;
  this.searching = false;

  this.bestMove = null;
  this.bestScore = -Infinity;

  this.rootMoves = [];
  this.currentRootIndex = 0;

  this.stack = [];

  this.nodeBudgetPerFrame = 30000000000; // you already found this sweet spot

  // iterative deepening
  this.maxDepth = 1;
  this.targetDepth = DIFFICULTY[currentDifficulty].depth;

  // heuristics
  this.killers = Array.from({ length: 64 }, () => [null, null]);
  this.history = {};
  }



  tick() {
    let nodes = 0;
    while (nodes < this.nodeBudgetPerFrame && this.searching) {
      if (!this.stepSearch()) {
        this.searching = false;
        break;
      }
      nodes++;
    }
  }
}
ChessEngine.prototype.startSearch = function(pos) {
  this.position = pos.clone();
  this.searching = true;

  this.bestMove = null;
  this.bestScore = -Infinity;

  this.rootMoves = this.position.generateLegalMoves();

  // simple capture-first ordering
  this.rootMoves.sort((a, b) => {
    const ca = a.capturedPiece !== EMPTY ? 1 : 0;
    const cb = b.capturedPiece !== EMPTY ? 1 : 0;
    return cb - ca;
  });
 // -------------------------
  // Null Move Pruning block
  // -------------------------
  if (!inCheckNow &&
      depth >= NULL_MOVE_MIN_DEPTH &&
      hasNonPawnMaterial(position.sideToMove)) {

    const R = NULL_MOVE_R;
    const nullDepth = depth - 1 - R;

    makeNullMove();
    const score = -stepSearch(nullDepth, -beta, -beta + 1, ply + 1);
    unmakeNullMove();

    if (score >= beta) {
      // Fail-high: prune
      return beta;
    }
  }


  this.currentRootIndex = 0;
  this.stack = [];

  if (this.rootMoves.length > 0) {
    this.pushRootMove(this.rootMoves[0]);
  }
};

ChessEngine.prototype.pushRootMove = function(move) {
  const newPos = this.position.clone();
  newPos.makeMove(move);
  const moves = newPos.generateLegalMoves();

  const frame = new SearchFrame(
    newPos,
    this.maxDepth - 1,
    -Infinity,
    Infinity,
    moves,
    0,
    false,
    null
  );

  frame.rootMove = move;
  this.stack.push(frame);
};



ChessEngine.prototype.stepSearch = function() {
  // If stack empty → move to next root move
  if (this.stack.length === 0) {
    this.currentRootIndex++;
    if (this.currentRootIndex >= this.rootMoves.length) {
      return false; // search finished at this depth
    }
    this.pushRootMove(this.rootMoves[this.currentRootIndex]);
    return true;
  }

  let frame = this.stack[this.stack.length - 1];

  // Terminal node or depth 0
  if (frame.depth === 0 || frame.moves.length === 0) {
    const score = this.evaluate(frame.position);
    this.propagateScore(frame, score);
    this.stack.pop();
    return true;
  }

  // Still moves to explore
  if (frame.moveIndex < frame.moves.length) {
    const move = frame.moves[frame.moveIndex++];

    const newPos = frame.position.clone();
    newPos.makeMove(move);

    const childMoves = newPos.generatePseudoLegalMoves();
    const childDepth = frame.depth - 1;

    const child = new SearchFrame(
      newPos,
      childDepth,
      frame.alpha,
      frame.beta,
      childMoves,
      0,
      !frame.isMaxPlayer,
      { parent: frame }
    );

    child.rootMove = frame.rootMove;
    this.stack.push(child);
    return true;
  }

  // No moves left → return bestScore
  const finalScore = frame.bestScore;
  this.propagateScore(frame, finalScore);
  this.stack.pop();
  return true;
};




ChessEngine.prototype.updateFrameBest = function(frame, score, move) {
  if (frame.isMaxPlayer) {
    if (score > frame.bestScore) frame.bestScore = score;
    if (score > frame.alpha) frame.alpha = score;
  } else {
    if (score < frame.bestScore) frame.bestScore = score;
    if (score < frame.beta) frame.beta = score;
  }

  // alpha-beta cutoff
  if (frame.alpha >= frame.beta) {
    // killer + history
    if (move) {
      const ply = frame.depth;
      const killers = this.killers[ply];

      const key = moveKey(move);
      this.history[key] = (this.history[key] || 0) + ply * ply;

      if (!killers[0] || moveKey(killers[0]) !== key) {
        killers[1] = killers[0];
        killers[0] = move;
      }
    }

    frame.moveIndex = frame.moves.length;
  }
};


ChessEngine.prototype.propagateScore = function(frame, score) {
  if (!frame.parentInfo || !frame.parentInfo.parent) {
    // root frame
    if (score > this.bestScore) {
      this.bestScore = score;
      this.bestMove = frame.rootMove;
    }
    return;
  }

  const parent = frame.parentInfo.parent;
  this.updateFrameBest(parent, score, frame.lastMove);
};


ChessEngine.prototype.evaluate = function(pos) {
  let score = 0;

  const pieceValues = {
    [PAWN]: 100,
    [KNIGHT]: 320,
    [BISHOP]: 330,
    [ROOK]: 500,
    [QUEEN]: 900,
    [KING]: 20000
  };

  const PST = {
    [PAWN]: [
      [0,0,0,0,0,0,0,0],
      [5,5,5,5,5,5,5,5],
      [1,1,2,3,3,2,1,1],
      [0,0,1,2,2,1,0,0],
      [0,0,1,2,2,1,0,0],
      [1,1,2,3,3,2,1,1],
      [5,5,5,5,5,5,5,5],
      [0,0,0,0,0,0,0,0]
    ],
    [KNIGHT]: [
      [-5,-4,-3,-3,-3,-3,-4,-5],
      [-4,-2,0,0,0,0,-2,-4],
      [-3,0,1,1,1,1,0,-3],
      [-3,0,1,2,2,1,0,-3],
      [-3,0,1,2,2,1,0,-3],
      [-3,0,1,1,1,1,0,-3],
      [-4,-2,0,0,0,0,-2,-4],
      [-5,-4,-3,-3,-3,-3,-4,-5]
    ],
    [BISHOP]: [
      [1,0,0,-1,-1,0,0,1],
      [-2,1,1,1,1,1,1,-2],
      [-2,1,2,2,2,2,1,-2],
      [-2,1,2,0,0,2,1,-2],
      [-2,1,2,0,0,2,1,-2],
      [-2,1,2,2,2,2,1,-2],
      [-2,1,1,1,1,1,1,-2],
      [1,0,0,-1,-1,0,0,1]
    ],
    [ROOK]: [
      [2,1,1,1,1,1,1,2,],
      [2,1,1,1,1,1,1,2],
      [2,1,2,0,0,2,1,2],
      [2,1,0,-1,-1,0,1,2],
      [2,1,0,-1,-1,0,1,2],
      [2,1,2,0,0,2,1,2],
      [2,1,1,1,1,1,1,2],
      [2,1,1,1,1,1,1,2]
    ],
    [QUEEN]: [
  [-20,-10,-10, -5, -5,-10,-10,-20],
  [-10,  0,  0,  0,  0,  0,  0,-10],
  [-10,  0,  5,  5,  5,  5,  0,-10],
  [ -5,  0,  5,  5,  5,  5,  0, -5],
  [ -5,  0,  5,  5,  5,  5,  0, -5],
  [-10,  0,  5,  5,  5,  5,  0,-10],
  [-10,  0,  0,  0,  0,  0,  0,-10],
  [-20,-10,-10, -5, -5,-10,-10,-20]
],


  };

  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      const p = pos.board[r][f];
      if (p === EMPTY) continue;

      const color = pieceColor(p);
      const type = pieceType(p);

      score += pieceValues[type] * color;

      if (PST[type]) {
        score += PST[type][r][f] * color;
      }
    }
  }

  // normalize from side to move perspective
  return score * (pos.sideToMove === WHITE ? 1 : -1);
};


// simple frame class so engine compiles
class SearchFrame {
  constructor(position, depth, alpha, beta, moves, moveIndex, isMaxPlayer, parentInfo) {
    this.position = position;
    this.depth = depth;
    this.alpha = alpha;
    this.beta = beta;
    this.moves = moves;
    this.moveIndex = moveIndex;
    this.isMaxPlayer = isMaxPlayer;
    this.bestScore = isMaxPlayer ? -Infinity : Infinity;
    this.parentInfo = parentInfo;
    this.rootMove = null;
  }
}
let dragging = false;
let dragPiece = null;
let dragFrom = null;
let dragX = 0;
let dragY = 0;
let highlightedMoves = [];
let aiside;
function setup() {
  createCanvas(600, 600);
  position = new Position();   // full rules engine
  engine = new ChessEngine();  // the incremental search engine
  aiside = BLACK
}

function drawCheckHighlight() {
  const tile = width / 8;

  const side = position.sideToMove;
  if (!position.inCheck(side)) return;

  // find king
  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      if (position.board[r][f] === side * KING) {
        fill(255, 0, 0, 120);
        noStroke();
        rect(f * tile, r * tile, tile, tile);
        return;
      }
    }
  }
}

function draw() {
  background(220);
  drawBoard();
  drawLastMoveHighlight();
  drawCheckHighlight();
  drawHighlights();
  drawPieces(position);
 // initZobrist();
// zobristKey = computeZobristKey(currentPosition);
  if (pendingPromotionMove) {
  drawPromotionMenu();
}
if (position.sideToMove !== humanSide &&
    !engine.searching &&
    engine.bestMove == null) {
  engine.maxDepth = 1;      // reset depth for new move
  engine.targetDepth = DIFFICULTY[currentDifficulty].depth;
  engine.startSearch(position);
}

if (engine.searching) engine.tick();

if (position.sideToMove !== humanSide &&
    !engine.searching &&
    engine.bestMove) {

  let move = engine.bestMove;

// add noise
if (DIFFICULTY[currentDifficulty].noise > 0) {
  const noise = DIFFICULTY[currentDifficulty].noise;
  if (Math.random() < noise) {
    const i = Math.floor(Math.random() * engine.rootMoves.length);
    move = engine.rootMoves[i];
  }
}

// add blunder chance
if (Math.random() < DIFFICULTY[currentDifficulty].blunder) {
  const i = Math.floor(Math.random() * engine.rootMoves.length);
  move = engine.rootMoves[i];
}

position.makeMove(move);
  lastMove = {
    fromFile: move.fromFile,
    fromRank: move.fromRank,
    toFile:   move.toFile,
    toRank:   move.toRank
  };
  engine.bestMove = null;
}
}
function isAITurn() {
  return position.sideToMove === aiside;
}
ChessEngine.prototype.startSearch = function(pos) {
  this.position = pos.clone();     // snapshot of current board
  this.searching = true;

  this.bestMove = null;
  this.bestScore = -Infinity;

  this.rootMoves = pos.generateLegalMoves();
  this.currentRootIndex = 0;

  this.stack = [];

  if (this.rootMoves.length > 0) {
    this.pushRootMove(this.rootMoves[0]);
  }
};
ChessEngine.prototype.tick = function() {
  let nodes = 0;
  while (nodes < this.nodeBudgetPerFrame && this.searching) {
    if (!this.stepSearch()) {
      // finished this depth
      this.searching = false;
      break;
    }
    nodes++;
  }

  // if finished this depth and can go deeper, restart search
  if (!this.searching && this.maxDepth < this.targetDepth) {
    this.maxDepth++;
    this.startSearch(this.position);
  }
};



let selectedSquare = null;

function mousePressed() {
  const sq = squareFromMouse(mouseX, mouseY);
  if (!sq) return;

  if (!isHumanTurn()) return;
if (pendingPromotionMove) {
  const tile = width / 8;
  const x = pendingPromotionMove.toFile * tile;
  const y = pendingPromotionMove.toRank * tile;

  for (let i = 0; i < 4; i++) {
    const bx = x;
    const by = y + i * tile;

    if (mouseX >= bx && mouseX < bx + tile &&
        mouseY >= by && mouseY < by + tile) {

      // finalize promotion
      pendingPromotionMove.promotion = {
        "q": QUEEN,
        "r": ROOK,
        "b": BISHOP,
        "n": KNIGHT
      }[promotionChoices[i]];

      position.makeMove(pendingPromotionMove);
      pendingPromotionMove = null;
      dragPiece = null;
      dragFrom = null;
      return;
    }
  }

  // click outside menu → cancel menu
  pendingPromotionMove = null;
  return;
}

  const piece = position.board[sq.rank][sq.file];
  if (piece !== EMPTY && pieceColor(piece) === humanSide) {
    dragging = true;
    dragPiece = piece;
    dragFrom = sq;
    dragX = mouseX;
    dragY = mouseY;

    // compute legal moves for highlighting
    highlightedMoves = position.generateLegalMoves().filter(m =>
      m.fromFile === sq.file && m.fromRank === sq.rank
    );
  }
}

function mouseDragged() {
  if (dragging) {
    dragX = mouseX;
    dragY = mouseY;
  }
}
function mouseReleased() {
  if (!dragging) return;
  if (!isHumanTurn()) return;

  const sq = squareFromMouse(mouseX, mouseY);
  dragging = false;

  // clear highlights
  highlightedMoves = [];

  if (!sq) {
    dragPiece = null;
    dragFrom = null;
    return;
  }

  const legal = position.generateLegalMoves();
  for (const m of legal) {
    if (m.fromFile === dragFrom.file &&
        m.fromRank === dragFrom.rank &&
        m.toFile === sq.file &&
        m.toRank === sq.rank) {

      // promotion?
if (pieceType(dragPiece) === PAWN && (m.toRank === 0 || m.toRank === 7)) {
  pendingPromotionMove = m;
  return; // stop here, wait for user choice
}

position.makeMove(m);
      lastMove = {
  fromFile: m.fromFile,
  fromRank: m.fromRank,
  toFile:   m.toFile,
  toRank:   m.toRank
};
dragPiece = null;
dragFrom = null;
return;

    }
  }

  dragPiece = null;
  dragFrom = null;
}




function handleHumanClick(f, r) {
  if (!selectedSquare) {
    // select piece
    const piece = position.board[r][f];
    if (piece !== EMPTY && pieceColor(piece) === WHITE) {
      selectedSquare = { f, r };
    }
  } else {
    // attempt move
    const moves = position.generateLegalMoves();
    for (const m of moves) {
      if (m.fromFile === selectedSquare.f &&
          m.fromRank === selectedSquare.r &&
          m.toFile === f &&
          m.toRank === r) {

        position.makeMove(m);
        selectedSquare = null;
        return;
      }
    }

    // invalid → deselect
    selectedSquare = null;
  }
}
function drawBoard() {
  const tileSize = width / 8;
  stroke(0)

  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      if ((r + f) % 2 === 0) fill(200,120,0);
      else fill(100,45,0);

      rect(f * tileSize, r * tileSize, tileSize, tileSize);
    }
  }
  noStroke()
  // files (a–h) along bottom
  textAlign(CENTER, CENTER);
  textSize(16);
  fill(0); // or contrasting color

  for (let f = 0; f < 8; f++) {
    const fileChar = String.fromCharCode('a'.charCodeAt(0) + f);
    const x = f * tileSize + tileSize / 2;
    const y = 8 * tileSize - 10; // slightly above bottom edge
    text(fileChar, x, y);
  }

  // ranks (1–8) along left side
  for (let r = 0; r < 8; r++) {
    const rankChar = (8 - r).toString();
    const x = 10; // slightly right of left edge
    const y = r * tileSize + tileSize / 2;
    text(rankChar, x, y);
  }
}

function drawPieces(pos) {
  const tileSize = width / 8;

  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      const piece = pos.board[r][f];
      if (piece === EMPTY) continue;

      // Skip drawing the piece being dragged
      if (dragging &&
          dragFrom &&
          dragFrom.file === f &&
          dragFrom.rank === r) {
        continue;
      }

      drawPiece(piece, f * tileSize, r * tileSize, tileSize);
    }
  }

  // Draw dragged piece on top
  if (dragging && dragPiece !== null) {
    const tileSize = width / 8;
    drawPiece(dragPiece, dragX - tileSize / 2, dragY - tileSize / 2, tileSize);
  }
}

function drawPiece(piece, x, y, size) {
  const col = pieceColor(piece);
  const type = pieceType(piece);

  const symbols = {
    [PAWN]:   col === WHITE ? "♙" : "♙",
    [KNIGHT]: col === WHITE ? "♘" : "♞",
    [BISHOP]: col === WHITE ? "♗" : "♝",
    [ROOK]:   col === WHITE ? "♖" : "♜",
    [QUEEN]:  col === WHITE ? "♕" : "♛",
    [KING]:   col === WHITE ? "♔" : "♚"
  };

  textAlign(CENTER, CENTER);
  textSize(size * 0.8);
  fill(col === WHITE ? 255 : 0);
  text(symbols[type], x + size/2, y + size/2);
}


function squareFromMouse(x, y) {
  const tile = width / 8;
  const f = Math.floor(x / tile);
  const r = Math.floor(y / tile);

  if (f < 0 || f > 7 || r < 0 || r > 7) return null;
  return { file: f, rank: r };
}
function drawHighlights() {
  const tile = width / 8;

  // highlight selected square
  if (dragFrom) {
    fill(255, 255, 0, 120);
    noStroke();
    rect(dragFrom.file * tile, dragFrom.rank * tile, tile, tile);
  }

  // highlight legal moves
  for (const m of highlightedMoves) {
    const x = m.toFile * tile + tile / 2;
    const y = m.toRank * tile + tile / 2;

    fill(0, 0, 0, 120);
    noStroke();
    ellipse(x, y, tile * 0.3);
  }
}
function moveScore(engine, frame, move) {
  let score = 0;

  // 1. MVV-LVA for captures
  if (move.capturedPiece !== EMPTY) {
    const victim = pieceType(move.capturedPiece);
    const attacker = pieceType(move.piece);
    score += 100000 + victim * 10 - attacker;
  }

  // 2. Promotions
  if (move.promotion) score += 90000;

  // 3. Killer moves
  if (engine.killers && engine.killers[frame.depth]) {
    const k0 = engine.killers[frame.depth][0];
    const k1 = engine.killers[frame.depth][1];
    if (k0 && moveKey(k0) === moveKey(move)) score += 50000;
    if (k1 && moveKey(k1) === moveKey(move)) score += 50000;
  }

  // 4. History heuristic (if you have it)
  if (engine.history) {
    const h =
      engine.history[move.fromRank]?.[move.fromFile]?.[move.toRank]?.[move.toFile] || 0;
    score += h;
  }

  // 5. Centralization for quiet moves
  if (move.capturedPiece === EMPTY && !move.promotion) {
    const center =
      (4 - Math.abs(move.toFile - 3.5)) + (4 - Math.abs(move.toRank - 3.5));
    score += center;
  }

  return score;
}


function moveKey(move) {
  if (!move) return "null";
  return `${move.fromFile}${move.fromRank}${move.toFile}${move.toRank}`;
}


function moveScore(engine, frame, move) {
  let score = 0;

  // MVV-LVA for captures
  if (move.capturedPiece !== EMPTY) {
    const victim = pieceType(move.capturedPiece);
    const attacker = pieceType(move.piece);
    score += 1000 + 10 * victim - attacker;
  }

  // promotions
  if (move.promotion) score += 900;

  // killer moves
  const killers = engine.killers[frame.depth] || [];
  if (killers[0] && moveKey(killers[0]) === moveKey(move)) score += 5000;
  if (killers[1] && moveKey(killers[1]) === moveKey(move)) score += 4000;

  // history heuristic
  const key = moveKey(move);
  score += engine.history[key] || 0;

  // quiet centralization
  if (move.capturedPiece === EMPTY && !move.promotion) {
    const centerBonus =
      (4 - Math.abs(move.toFile - 3.5)) +
      (4 - Math.abs(move.toRank - 3.5));
    score += centerBonus;
  }

  return score;
}
function drawPromotionMenu() {
  const tile = width / 8;
  const x = pendingPromotionMove.toFile * tile;
  const y = pendingPromotionMove.toRank * tile;

  // background box
  fill(255, 255, 255, 230);
  stroke(0);
  rect(x, y, tile, tile * 4);

  textAlign(CENTER, CENTER);
  textSize(tile * 0.7);

  const symbols = {
    "q": position.sideToMove === WHITE ? "♕" : "♛",
    "r": position.sideToMove === WHITE ? "♖" : "♜",
    "b": position.sideToMove === WHITE ? "♗" : "♝",
    "n": position.sideToMove === WHITE ? "♘" : "♞"
  };

  for (let i = 0; i < 4; i++) {
    fill(255);
    rect(x, y + i * tile, tile, tile);
    fill(0);
    text(symbols[promotionChoices[i]], x + tile / 2, y + tile / 2 + i * tile);
  }
}
ChessEngine.prototype.quiescenc = function(pos, alpha, beta) {
  // hard cap to avoid p5 "infinite loop"
  this.qNodes++;
  if (this.qNodes > this.maxQNodes) {
    return this.evaluate(pos);
  }

  let standPat = this.evaluate(pos);

  if (standPat >= beta) return beta;
  if (standPat > alpha) alpha = standPat;

  const moves = pos.generatePseudoLegalMoves().filter(m => m.capturedPiece !== EMPTY);

  const frame = { depth: 0 };
  orderMoves(this, pos, moves, frame);

  for (const move of moves) {
    const newPos = pos.clone();
    newPos.makeMove(move);

    const score = -this.quiescence(newPos, -beta, -alpha);

    if (score >= beta) return beta;
    if (score > alpha) alpha = score;
  }

  return alpha;
};
ChessEngine.prototype.quiescence = function(pos, alpha, beta) {
  // not used in this minimal core
  return this.evaluate(pos);
};


ChessEngine.prototype.seeLosesMaterial = function(pos, move) {
  const newPos = pos.clone();
  newPos.makeMove(move);

  const color = pieceColor(move.piece);
  const enemy = -color;
  const f = move.toFile;
  const r = move.toRank;

  // if enemy can capture the moved piece
  const attackedByEnemy = newPos.isSquareAttacked(f, r, enemy);
  if (!attackedByEnemy) return false;

  // if we can also defend/recapture, don't treat it as a losing move
  const defendedByUs = newPos.isSquareAttacked(f, r, color);
  if (defendedByUs) return false;

  return true; // hanging
};

Position.prototype.isSquareAttacked = function(file, rank, byColor) {
  const moves = this.generatePseudoLegalMoves();

  for (const m of moves) {
    if (pieceColor(m.piece) !== byColor) continue;

    if (m.toFile === file && m.toRank === rank) {
      return true;
    }
  }

  return false;
};
Position.prototype.isSquareAttacked = function(file, rank, byColor) {
  const moves = this.generatePseudoLegalMoves();

  for (const m of moves) {
    if (pieceColor(m.piece) !== byColor) continue;
    if (m.toFile === file && m.toRank === rank) return true;
  }

  return false;
};
ChessEngine.prototype.nullMovePrune = function(frame) {
  const pos = frame.position;

  // 1. Don't null move in check
  if (pos.inCheck(pos.sideToMove)) return null;

  // 2. Don't null move in endgames (zugzwang danger)
  let material = 0;
  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      const p = pos.board[r][f];
      if (p === EMPTY) continue;
      const t = pieceType(p);
      if (t !== KING && t !== PAWN) material++;
    }
  }
  if (material <= 4) return null; // endgame → disable null move

  // 3. Depth must be high enough
  if (frame.depth < 3) return null;

  // 4. Make null move
  const newPos = pos.clone();
  newPos.sideToMove = -newPos.sideToMove;

  // 5. Reduced depth (R = 2)
  const R = 2;
  const score = -this.quiescence(newPos, -frame.beta, -frame.beta + 1);

  // 6. Fail-high → prune
  if (score >= frame.beta) return score;

  return null;
};
Position.prototype.hash = function() {
  let h = 0;
  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      const p = this.board[r][f];
      if (p !== EMPTY) {
        h = (h * 31 + p * 7 + r * 3 + f) | 0;
      }
    }
  }
  return h;
};
function orderMoves(engine, pos, moves, frame) {
  for (const m of moves) {
    m.order = moveScore(engine, frame, m);
  }
  moves.sort((a, b) => b.order - a.order);
  for (let m of moves) {
  if (m.isCapture) {
    m.see = SEE(m);
  } else {
    m.see = -99999999; // quiet moves go last
  }
}
moves.sort((a, b) => b.see - a.see);
}
function drawLastMoveHighlight() {
  if (!lastMove) return;

  const tile = width / 8;

  // from-square (yellow)
  fill(255, 255, 0, 120);
  noStroke();
  rect(lastMove.fromFile * tile, lastMove.fromRank * tile, tile, tile);

  // to-square (green)
  fill(0, 255, 0, 120);
  noStroke();
  rect(lastMove.toFile * tile, lastMove.toRank * tile, tile, tile);
}

function isHumanTurn() {
  return position.sideToMove === humanSide;
}

function isAITurn() {
  return position.sideToMove !== humanSide;
}

function random64() {
  // Simple 64-bit random using BigInt
  return (BigInt(Math.floor(Math.random() * 0xFFFFFFFF)) << 32n) ^
         BigInt(Math.floor(Math.random() * 0xFFFFFFFF));
}

function initZobrist() {
  zobristPiece = Array(64).fill(0).map(() => []);
  for (let sq = 0; sq < 64; sq++) {
    for (let p = 0; p < 16; p++) { // assume max 16 piece types (adjust)
      zobristPiece[sq][p] = random64();
    }
  }

  zobristSide = random64();

  // Castling: encode your castling rights as 0..15 bitmask, or fewer
  zobristCastling = [];
  for (let cr = 0; cr < 16; cr++) {
    zobristCastling[cr] = random64();
  }

  // En passant: 0..7 = file, 8 = none
  zobristEnPassant = [];
  for (let f = 0; f < 9; f++) {
    zobristEnPassant[f] = random64();
  }
}
function computeZobristKey(position) {
  let key = 0n;

  for (let sq = 0; sq < 64; sq++) {
    const piece = position.board[sq]; // your piece code or PIECE_NONE
    if (piece !== PIECE_NONE) {
      key ^= zobristPiece[sq][piece];
    }
  }

  if (position.sideToMove === 'b') {
    key ^= zobristSide;
  }

  key ^= zobristCastling[position.castlingRights]; // 0..15
  key ^= zobristEnPassant[position.enPassantFile]; // 0..8

  return key;
}
function hasNonPawnMaterial(side) {
  // Adapt to your piece codes
  // Example: 1=WP, 2=WN, 3=WB, 4=WR, 5=WQ, 6=WK, 7=BP, ...
  for (let sq = 0; sq < 64; sq++) {
    const p = position.board[sq];
    if (p != EMPTY) continue;

    const isWhite = (p >= 1 && p <= 6);
    const isBlack = (p >= 7 && p <= 12);

    if ((side === 'w' && isWhite) || (side === 'b' && isBlack)) {
      const type = p % 6; // 1 pawn, 2 knight, 3 bishop, 4 rook, 5 queen, 0 king
      if (type !== 1 && type !== 0) {
        return true; // has non-pawn, non-king material
      }
    }
  }
  return false;
}
function makeNullMove() {
  zobristStack.push(zobristKey);

  // Remove old EP from key
  const oldEp = position.enPassantFile;
  if (oldEp !== 8) {
    zobristKey ^= zobristEnPassant[oldEp];
  }

  // No new EP square
  position.enPassantFile = 8;

  // Flip side
  position.sideToMove = (position.sideToMove === 'w') ? 'b' : 'w';
}

function unmakeNullMove() {
  // Restore everything from stack
  zobristKey = zobristStack.pop();
  // Also restore sideToMove, enPassantFile, etc. from your usual position stack
  // If you don't have a full position stack, you can:
  // - store sideToMove and enPassantFile in your own null-move stack
}
function SEE(move) {
  const from = move.from;
  const to = move.to;

  let board = position.board;

  let attacker = move.piece;
  let victim = move.captured;

  if (!victim) return 0; // no capture = no SEE

  // Gains list
  let gains = [];
  gains.push(PIECE_VALUE[victim]);

  let side = position.sideToMove;
  let attackers = getAttackers(to); // you must implement this

  let depth = 0;
  let currentVictim = attacker;

  while (true) {
    // Remove the current attacker from the board
    removePiece(currentVictim, from, to);

    side = (side === 'w') ? 'b' : 'w';

    let nextAttacker = findLeastValuableAttacker(side, to);
    if (!nextAttacker) break;

    gains.push(PIECE_VALUE[currentVictim] - gains[depth]);
    depth++;

    currentVictim = nextAttacker;
  }

  // Undo board changes
  undoSEE();

  // Minimax the gains
  for (let i = gains.length - 2; i >= 0; i--) {
    gains[i] = Math.min(gains[i], -gains[i + 1]);
  }

  return gains[0];
}

