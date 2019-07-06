// vim:et:sw=2
//
// "$Id$"
//
// Checkers game for the Fast Light Tool Kit (FLTK).
//
// Hours of fun: the FLTK checkers game!
// Based on a very old algorithm, but it still works!
//
// Copyright 1998-2017 by Bill Spitzak and others.
//
// This library is free software. Distribution and use rights are outlined in
// the file "COPYING" which should have been included with this file.  If this
// file is missing or damaged, see the license at:
//
//     http://www.fltk.org/COPYING.php
//
// Please report all bugs and problems on the following page:
//
//     http://www.fltk.org/str.php
//

const char* copyright = 
"Checkers game\n"
"Copyright (C) 1997-2010 Bill Spitzak    spitzak@d2.com\n"
"Original Pascal code:\n"
"Copyright 1978, Oregon Minicomputer Software, Inc.\n"
"2340 SW Canyon Road, Portland, Oregon 97201\n"
"Written by Steve Poulsen 18-Jan-79\n"
"\n"
"This program is free software; you can redistribute it and/or modify "
"it under the terms of the GNU General Public License as published by "
"the Free Software Foundation; either version 2 of the License, or "
"(at your option) any later version.\n"
"\n"
"This program is distributed in the hope that it will be useful, "
"but WITHOUT ANY WARRANTY; without even the implied warranty of "
"MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the "
"GNU General Public License for more details.\n"
"\n"
"You should have received a copy of the GNU Library General Public "
"License along with this library; if not, write to the Free Software "
"Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 "
"USA.";

// Define FLTK to get the fltk interface
// Define VT100 to get the VT100 interface
// Define both to get a program that takes a -t switch

#define FLTK
#define VT100

#undef check

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <time.h>

#ifdef VT100
#include <ctype.h>	// toupper
#endif

////////////////////////////////////////////////////////////////
// The algorithim:

int maxevaluate=2500;		// max number of moves to examine on a turn
int maxnodes = 2500;		// maximum number of nodes in search tree
int maxply = 20;		// maximum depth to look ahead
char forcejumps = 1;		// is forced jumps rule in effect?

// scoring parameters: (all divided by 5 from original code)
// some signs seem to be backwards, marked them with (-) in comment
const int spiece = 800;		// value of a piece
const int sking = 1200;		// value of a king
const int sadvan = 160;		// value of mypieces/theirpieces-1
// const int smobil = ?		// moves *enemy* can make w/o being jumped
const int sallpin = 80;		// mobil == 0
const int sdeny = 10;		// moves enemy can make that will be jumped
const int spin = 32;		// enemy pieces that have no move except jumped
const int sthreat = -10;	// enemy pieces we can jump if not moved (-)
const int sgrad = 1;		// score of piece positions
const int sback = 10;		// back row occupied so enemy can't make king
const int smoc2 = 200;		// more mobility, more center
const int smoc3 = -8;		// less mobility, less center
const int smoc4 = -80;		// more mobility, less center
const int smode2 = -14;		// less mobility, less denied
const int smode3 = -40;		// more mobility, more denied (-)
const int sdemmo = -20;		// more denied, more moves (-)
const int scent = 10;		// pieces in center
const int skcent = 100;		// kings in center

const int depthpenalty=4;	// guess
const int noise=2;		// values less or eq to this apart are eq

// const int sattackking = 4;	// not used
// const int sattackpiece = 3;

struct node {
  node *father;
  node *son;             // best son
  node *brother;         // next brother
  short int value;       // value of this board position to player making move
  unsigned char from,to; // the move to reach this board
  long int jump;         // bit map of locations jumped
  unsigned char mobil;
  unsigned char deny;
  unsigned char pin;
  unsigned char threat;
  short int gradient;
  unsigned who:1;        // 0 = black's move, 1 = white's move
  unsigned king:1;       // 1 = move causes piece to be kinged
  unsigned back:1;
  unsigned moc2:1;
  unsigned moc3:1;
  unsigned moc4:1;
  unsigned mode2:1;
  unsigned mode3:1;
  unsigned demmo:1;
};

int nodes;		// count of nodes

/*	Board positions:	Border positions:

	      WHITE		  00  01  02  03  04
	  05  06  07  08	04  XX  XX  XX  XX
	09  10  11  12		  XX  XX  XX  XX  13
	  14  15  16  17	13  XX  XX  XX  XX
	18  19  20  21		  XX  XX  XX  XX  22
	  23  24  25  26	22  XX  XX  XX  XX
	27  28  29  30		  XX  XX  XX  XX  31
	  32  33  34  36	31  XX  XX  XX  XX
	36  37  38  39		  XX  XX  XX  XX  40
	      BLACK		40  41  42  43  44

*/

typedef char piece;

// Define bitmask used to represent a square's contents and enumerate some
// useful combinations (e.g., BLACKKING == BLACK|KING) for convenience.
// Note: BLUE is used for border squares to make it easy to distinguish an
// invalid move target from an empty square.
#define EMPTY 0
#define BLACK 1
#define WHITE 2
#define KING 4
#define BLACKKING 5
#define WHITEKING 6
#define BLUE 8

const piece flip[9] = {
  EMPTY, WHITE, BLACK, 0, 0, WHITEKING, BLACKKING, 0, BLUE};

// Sparse array of board index offsets representing all possible move vectors
// for each piece type.
// Note: Board indices selected so that all 4 non-jump diagonal moves can be
// accomplished by adding/subtracting 4 or 5 from the current position index.
// Array indexed by the piece type bitmask/enumeration above.
// Note: The order of the offsets within the inner array is mostly
// insignificant, except that any zeroes must come last, since the move
// generator in movepiece() treats 0 as a terminator.
const int offset[9][4] = {	// legal move directions
  {0,0,0,0},    // EMPTY
  {-5,-4,0,0},  // BLACK
  {4,5,0,0},    // WHITE
  {0,0,0,0},    // N/A
  {0,0,0,0},    // N/A (king must be black or white)
  {4,5,-4,-5},  // BLACKKING
  {4,5,-4,-5},  // WHITEKING
  {0,0,0,0},    // N/A
  {0,0,0,0}     // BLUE (no piece)
};

piece b[45];             // current board state being considered

int evaluated;           // number of moves evaluated this turn

char centralsquares[45]; // flag array marking the 8 central squares
char is_protected[45];

piece flipboard[45];     // swapped if enemy is black
piece *tb;               // pointer to real or swapped board
#define FRIEND BLACK
#define FRIENDKING BLACKKING
#define ENEMY WHITE
#define ENEMYKING WHITEKING

char check(int target,int direction) {
  // see if enemy at target can be jumped from direction by our piece
  int dst = target-direction;
  if (tb[dst]) return(0);
  int src = target+direction;
  if (tb[src] == FRIENDKING);
  else if (direction < 0 || tb[src] != FRIEND) return(0);
  piece aa = tb[target]; piece bb = tb[src];
  tb[target] = EMPTY; tb[src] = EMPTY;
  int safe =
    (   (tb[src-4]&FRIEND && tb[src-8]&ENEMY)
     || (tb[src-5]&FRIEND && tb[src-10]&ENEMY)
     || (tb[dst-4]&ENEMY && !tb[dst+4])
     || (tb[dst-5]&ENEMY && !tb[dst+5])
     || (tb[src+4]&FRIEND && tb[src+8]==ENEMYKING)
     || (tb[src+5]&FRIEND && tb[src+10]==ENEMYKING)
     || (tb[dst+4]==ENEMYKING && !tb[dst-4])
     || (tb[dst+5]==ENEMYKING && !tb[dst-5]));
  tb[target] = aa; tb[src] = bb;
  return(safe);
}

int deniedmoves,undeniedmoves;
void analyzemove(int direction,int src) {
  int target = src+direction;
  if (!tb[target]) {
    if (!tb[target+direction]) is_protected[target] = 1;
    piece a = tb[src]; tb[src] = EMPTY;
    if (check(target,4) || check(target,5) ||
	check(target,-4) || check(target,-5) ||
	(tb[src+4]&ENEMY && check(src+4,4)) ||
	(tb[src+5]&ENEMY && check(src+5,5)) ||
	(tb[src-4]&ENEMY && check(src-4,-4)) ||
	(tb[src-5]&ENEMY && check(src-5,-5)))
      deniedmoves++;
    else undeniedmoves++;
    tb[src] = a;
  }
}

// Evaluate board for the user whose node is input, assigning the input node's
// score to the node. If "print" arg is set, print detailed breakdown of
// scoring components.
// Precondition: Sequence of moves up to and including the input node has
// already been applied to the board.
void evaluateboard(node *n,int print) {

  // Evaluate logic assumes current player is black; thus, if most recent move
  // is actually white's, we must first "flip" the board (i.e., swap color of
  // all pieces), swapping back when evaluation is complete.
  if (!n->who) tb = b;	// move was black's
  else {
    for (int i=0; i<45; i++) flipboard[44-i] = flip[(int)b[i]];
    tb = flipboard;
  }

  memset(is_protected,0,sizeof(is_protected));
  int friendpieces = 0;
  int enemypieces = 0;
  int friendkings = 0;
  int enemykings = 0;
  int friendkcent = 0;
  int friendcent = 0;
  int enemykcent = 0;
  int enemycent = 0;
  n->mobil = n->deny = n->pin = n->threat = 0;

  int i;
  for (i=5; i<40; i++) switch(tb[i]) {
  case ENEMYKING:
    enemykings++;
    enemykcent += centralsquares[i];
    deniedmoves = 0;
    undeniedmoves = 0;
    if (i>8) {
      analyzemove(-4,i);
      analyzemove(-5,i);
    }
    goto J1;
  case ENEMY:
    deniedmoves = 0;
    undeniedmoves = 0;
  J1:	enemypieces++;
    enemycent += centralsquares[i];
    if (i<36) {
      analyzemove(4,i);
      analyzemove(5,i);
    }
    if (deniedmoves && !undeniedmoves) n->pin++;
    n->deny += deniedmoves;
    n->mobil += undeniedmoves;
    break;
  case FRIENDKING:
    friendkings++;
    friendkcent += centralsquares[i];
    if (tb[i+4]&ENEMY && !tb[i+8] && !(tb[i+4]==ENEMYKING && !tb[i-4]))
      n->threat++;
    if (tb[i+5]&ENEMY && !tb[i+10] && !(tb[i+5]==ENEMYKING && !tb[i-5]))
      n->threat++;
  case FRIEND:
    friendpieces++;
    friendcent += centralsquares[i];
    if (tb[i-4]&ENEMY && !tb[i-8] && tb[i+4]) n->threat++;
    if (tb[i-5]&ENEMY && !tb[i-10] && tb[i+5]) n->threat++;
    break;
  }

  int gradient[40];
  for (i=4; i<9; i++) gradient[i] = tb[i] ? 0 : 32;
  int total = 0;
  for (i=9; i<40; i++) {
    int x = (gradient[i-4]+gradient[i-5])/2;
    if (tb[i]==FRIEND) total += x;
    gradient[i] = (tb[i]&FRIEND || (!tb[i] && !is_protected[i])) ? x : 0;
  }
  n->gradient = total;

  n->back = tb[39]==FRIEND && tb[37]==FRIEND && !enemykings;

  node* f = n->father;

  n->moc2 = f->mobil>n->mobil && friendcent>enemycent;
  n->moc3 = f->mobil<=n->mobil && friendcent<enemycent;
  n->moc4 = f->mobil>n->mobil && friendcent<enemycent;
  n->mode2 = f->mobil<=n->mobil && n->deny<f->deny;
  n->mode3 = f->mobil>n->mobil && n->deny>f->deny;
  n->demmo = n->deny>f->deny && f->deny+f->mobil>n->deny+n->mobil;

  total =
    spiece	* (friendpieces - enemypieces) +
    (sking-spiece) * (friendkings	- enemykings) +
    //	mobil?
    sdeny	* (n->deny	- f->deny) +
    spin	* (n->pin	- f->pin) +
    sthreat	* (n->threat	- f->threat) +
    sgrad	* (n->gradient	- f->gradient) +
    sback	* (n->back	- f->back) +
    smoc2	* (n->moc2	- f->moc2) +
    smoc3	* (n->moc3	- f->moc3) +
    smoc4	* (n->moc4	- f->moc4) +
    smode2	* (n->mode2	- f->mode2) +
    smode3	* (n->mode3	- f->mode3) +
    sdemmo	* (n->demmo	- f->demmo) +
    scent	* (friendcent	- enemycent) +
    (skcent-scent) * (friendkcent	- enemykcent);
  if (!n->mobil) total += sallpin;

  if (!enemypieces) total = 30000;
  else if (friendpieces > enemypieces)
    total += (sadvan*friendpieces)/enemypieces-sadvan;
  else total -= (sadvan*enemypieces)/friendpieces-sadvan;

  if (print) {
    printf("\tParent\tNew\tScore\n");
    printf("pieces\t%d\t%d\t%d\n",enemypieces,friendpieces,
	   spiece*(friendpieces-enemypieces));
    printf("kings\t%d\t%d\t%d\n",enemykings,friendkings,
	   (sking-spiece)*(friendkings-enemykings));
    printf("mobil\t%d\t%d\n",f->mobil,n->mobil);
    printf("deny\t%d\t%d\t%d\n",f->deny,n->deny,sdeny*(n->deny-f->deny));
    printf("pin\t%d\t%d\t%d\n",f->pin,n->pin,spin*(n->pin-f->pin));
    printf("threat\t%d\t%d\t%d\n",f->threat,n->threat,sthreat*(n->threat-f->threat));
    printf("grad\t%d\t%d\t%d\n",f->gradient,n->gradient,sgrad*(n->gradient-f->gradient));
    printf("back\t%d\t%d\t%d\n",f->back,n->back,sback*(n->back-f->back));
    printf("moc2\t%d\t%d\t%d\n",f->moc2,n->moc2,smoc2*(n->moc2-f->moc2));
    printf("moc3\t%d\t%d\t%d\n",f->moc3,n->moc3,smoc3*(n->moc3-f->moc3));
    printf("moc4\t%d\t%d\t%d\n",f->moc4,n->moc4,smoc4*(n->moc4-f->moc4));
    printf("mode2\t%d\t%d\t%d\n",f->mode2,n->mode2,smode2*(n->mode2-f->mode2));
    printf("mode3\t%d\t%d\t%d\n",f->mode3,n->mode3,smode3*(n->mode3-f->mode3));
    printf("demmo\t%d\t%d\t%d\n",f->demmo,n->demmo,sdemmo*(n->demmo-f->demmo));
    printf("cent\t%d\t%d\t%d\n",enemycent,friendcent,scent*(friendcent-enemycent));
    printf("kcent\t%d\t%d\t%d\n",enemykcent,friendkcent,skcent*(friendkcent-enemykcent));
    printf("total:\t\t\t%d\n",total);
  }
  else {
    n->value = total;
    evaluated++;
  }
}	// end of evaluateboard

// --------------------- Tree management -----------------

node *freelist;

// Return a fresh node, taking it from freelist if possible, using malloc if
// necessary.
// Explanation: freelist starts out empty and is built dynamically as nodes are
// freed. Consider that the first computer move is likely to allocate several
// thousand nodes, most of which will be discarded at the end of the move; thus,
// over the course of a typical game, we will malloc only a small percentage of
// the total number of nodes required.
node *newnode(void) {
  node *n;
  // Take a node from the freelist if possible...
  if (freelist) {
    n = freelist;
    freelist = n->brother;
  }
  // ...otherwise malloc it.
  else n = (node *)malloc(sizeof(node));
  memset(n,0,sizeof(node));
  nodes++;
  return(n);
}

// Un-parent a node without removing its children.
// Leaves the extracted node's father and son intact, though its father no
// longer has any knowledge of it.
void extract(node *n) {
  node* i = n->father;
  if (i) {
    node* j = i->son;
    if (j==n) i->son = n->brother;
    else while (j) {
      i = j; j = j->brother;
      if (j==n) {i->brother = n->brother; break;}
    }
  }
  n->brother = 0;
}

// Delete a node, returning it and all its descendants to the free list.
void killnode(node *x) {
  if (!x) return;
  node *y;
  for (y = x; ; y = y->brother) {
    nodes--;
    // Recurse...
    killnode(y->son); y->son = 0;
    if (!y->brother) break;
  }
  // Prepend input node and its siblings to the freelist.
  // See newnode() for details on freelist population.
  y->brother = freelist;
  freelist = x;
}

int seed;		// current random number

// Insert the input node as a child of its father, with the insert position
// determined by comparison of the node value.
// Note: If the values are close (within noise), roll the dice to decide
// whether to keep looking or stop and insert.
// Rationale: Make computer more human, thereby rendering the game less
// deterministic.
void insert(node *n) {
  int val = n->value;
  node **pp;
  for (pp = &(n->father->son); *pp; pp = &((*pp)->brother)) {
    int val1 = (*pp)->value;
    if (abs(val-val1) <= noise) {
      seed = (seed*13077+5051)%0100000;
      if ((seed & 070) >= 060) break;
    }
    else if (val > val1) break;
  }
  n->brother = *pp;
  *pp = n;
}

// --------------------------------------------------------------


// Generate a single level of nodes representing moves that can follow the move
// represented by input node, adding the generated nodes to parent as sorted
// siblings. Run evaluateboard() to assign scores to each added node.
// Jump Note: Handle a series of jumps in multiple recursive calls, whose nodes
// ultimately collapse into a single node with the jumps represented by set bits
// in that node's "jump" mask.
// Note: Other than jumps, there's no recursion here.
void movepiece(node* f, int i, node* jnode) {
  static char jumphappened;

  // Loop over possible move directions for the type of piece at board position i.
  for (int k=0; k<4; k++) {
    int direction = offset[(int)b[i]][k];
    // Have we already processed all supported directions for this piece type?
    if (!direction) break;
    // let j = candidate target square
    // Note: Off-board positions have value BLUE (and hence, will not be EMPTY).
    int j = i+direction;
    if (b[j] == EMPTY) {
      // Candidate square is empty
      // Create a new node if we're not in the middle of a jump sequence (which
      // an empty square would terminate) and the prospective node would not be
      // sibling to a mandatory jump.
      if (!jnode && (!forcejumps || !f->son || !f->son->jump)) {
        // Create a new node.
	node* n = newnode();
	n->father = f;
	n->who = !f->who;
	n->from = i;
	n->to = j;
        // Perform the move (temporarily).
	piece oldpiece = b[i]; b[i] = EMPTY;
	if (!(oldpiece&KING) && n->who ? (j>=36) : (j<=8)) {
	  n->king = 1;
	  b[j] = oldpiece|KING;
	}
	else b[j] = oldpiece;
        // Evaluate the move and insert it under its father at sorted location.
	evaluateboard(n,0);
	insert(n);
        // Undo the move.
	b[i] = oldpiece; b[j] = EMPTY;
      }
    } else if (((b[j]^b[i])&(WHITE|BLACK))==(WHITE|BLACK) && !b[j+direction]) {
      // -- Jump sequence beginning or continuing --
      // Squares i and j are occupied by opposite color pieces and the square
      // beyond j (i.e., the jump destination) is empty.
      // If jumps are mandatory and the current best move is not a jump, kill
      // it (and any siblings), since it can never trump a jump.
      if (forcejumps && f->son && !f->son->jump) {
	killnode(f->son);
	f->son = 0;
      }
      // Create a new jump node, but don't add yet.
      int jumploc = j;
      j += direction;
      node* n = newnode();
      n->father = f;
      n->who = !f->who;
      n->from = i;
      n->to = j;
      n->jump = (1<<(jumploc-10));
      // Move the piece to its new location, kinging if appropriate.
      piece oldpiece = b[i]; b[i] = EMPTY;
      if (!(oldpiece&KING) && n->who ? (j>=36) : (j<=8)) {
	n->king = 1;
	b[j] = oldpiece|KING;
      }
      else b[j] = oldpiece;
      if (jnode) {
        // This is not the first jump of the move: combine information from
        // previous jumps before recursing.
	n->from = jnode->from;
	n->jump |= jnode->jump;
	n->king |= jnode->king;
      }
      piece jumpedpiece = b[jumploc];
      b[jumploc] = EMPTY; // remove piece jumped
      jumphappened = 0;
      // Recurse to see whether more jumps are possible.
      // Explanation: movepiece() continues to recurse until there are no more
      // jumps, at which point, evaluateboard() is called to score the node and
      // the node is inserted in sorted position. The test of jumphappened
      // ensures that only the final node created during the recursion is
      // evaluated/inserted; the others are discarded with killnode() in the
      // postorder traversal, since they're needed only for the information they
      // carry in their from/jump/king fields, which is merged into each new
      // node created.
      // Important Note: All of the jump nodes are children of the same father
      // (the one preceding the first jump in the sequence); thus, the recursive
      // killnode() can be safely used on the throwaway nodes without affecting
      // the one we're keeping.
      // Note: The call that breaks the jump recursion terminates without adding
      // a node because of the !jnode test in the "if" condition above.
      movepiece(f,j,n);
      if (forcejumps && jumphappened) killnode(n);
      else {evaluateboard(n,0); insert(n);}
      // Undo the move
      b[i] = oldpiece; b[j] = EMPTY;
      b[jumploc] = jumpedpiece;
      jumphappened = 1;
    }
  }
}

// Ensure that the direct children of the input node exist and have been
// evaluated. No recursion is performed!
// Details: Loop over all pieces belonging to the opponent of input node,
// calling movepiece() for each. The job of movepiece() is to create and
// evaluate a child node for each of the piece's possible moves and insert
// these nodes in sorted order. At the end of the loop, f->son represents the
// input node's opponent's optimal move, and since its score was calculated from
// the perspective of the input node's opponent, we negate it before assigning
// to the input node.
void expandnode(node *f) {
  if (f->son || f->value > 28000) return;	// already done
  // Child moves are for input node's opponent.
  piece turn = f->who ? BLACK : WHITE;
  for (int i=5; i<40; i++) if (b[i]&turn) movepiece(f,i,0);
  if (f->son) {
    f->value = -f->son->value;
    // Depth Penalty: If 2 distinct board states have equal value, prefer the
    // one that can be reached in fewer moves.
    if (f->brother) f->value -= depthpenalty;
  }
  // If no more moves, return a value high enough to short-circuit iteration.
  else f->value = 30000;
}

// Execute the move represented by the input node, performing any jumps
// indicated by the node's jump bitmap, and converting piece to king if
// appropriate.
// Calling Context: This function is called in both exploratory (move selection)
// and real (move execution) contexts.
void makemove(node *n) {
  b[n->to] = b[n->from];
  if (n->king) b[n->to] |= KING;
  b[n->from] = EMPTY;
  // Remove any jumped pieces.
  if (n->jump) for(int i=0; i<32; i++) {
    if (n->jump & (1<<i)) b[10+i] = EMPTY;
  }
}

int didabort(void);

// Expand the input node recursively down to depth indicated by "level" (unless
// one of the limit thresholds is hit first), propagating scores calculated for
// leaf nodes upwards in the postorder traversal return path.
int fullexpand(node *f, int level) {
  // Impose limits on the recursion.
  // Logic: Stop when we've created max # of nodes or evaluated max # of moves
  // for a single turn.
  if (didabort() || nodes > maxnodes-(maxply*10) || evaluated > maxevaluate) return(0);
  // Expand a single level (possibly with multiple jumps).
  // Note: The work of constructing nodes representing candidate moves is done
  // by expandnode; fullexpand uses the nodes constructed by expandnode as part
  // of a higher-level strategy.
  // Performance Note: In many cases (specifically, when we end up going
  // deeper), the evaluation that occurs for f's children in expandnode() is
  // wasted, as it will be overwritten by what occurs in the loop over sons
  // below...
  expandnode(f);
  if (!f->son) return(1);
  // Save the board so we can restore after evaluating various states.
  piece oldboard[45];
  memmove(oldboard,b,sizeof(b));
  node* n = f->son;
  // Stop recursion when desired depth is reached. Note that calcmove first
  // calls fullexpand with level == 1, which means only direct children are
  // expanded; however, it keeps incrementing level and retrying as long as the
  // board value produced is less than a threshold. IOW, we look ahead only as
  // far as necessary to find a move that gives a sufficiently good advantage.
  // Note: !n->jump test ensures we treat a series of jumps as atomic.
  // Note: n->brother test reflects fact that a son with no brother is
  // practically zero-cost (no fanout), and thus, shouldn't count as a full
  // ply.
  if (!n->jump && n->brother) {if (level<1) return(1); level--;}
  // Convert list of siblings to array to simplify loop.
  int i;
  node* sons[32]; for (i=0; (sons[i++] = n); n = n->brother) {/*empty*/}
  int ret = 1;
  // Recursively expand all children of this node, extracting and re-inserting
  // each of the expanded nodes to make sibling order reflect the updated
  // scores.
  for (i=0; ret && (n = sons[i++]);) {
    // Make move (temporarily), to be restored after recursive expansion.
    // Optimization Note: This is rather inefficient: the memmove() copies
    // entire board, but because it occurs at every level, each copy undoes only
    // a single move. It would probably be more efficient to perform a more
    // targeted restore.
    makemove(n);
    ret = fullexpand(n,level);
    memmove(b,oldboard,sizeof(b));
    // Extract/insert node to allow it to find a location determined by its
    // updated score.
    extract(n);
    insert(n);
  }
  // At this point, the extract()/insert()'s in loop above has ensured that
  // son's value is the one that will propagate upwards.
  // Note: Call to expandnode() at start of this function also set f->value,
  // but only considering direct children.
  // Note: I don't like the duplication: it seems to me the recursion could be
  // done more intelligently.
  f->value = -f->son->value;
  return(ret);
}

// Go one level deeper along the "son" path (i.e., the current best at each
// level).
// Explanation: A prior call to fullexpand() has ensured a somewhat uniform
// expansion (limited by either nodes created or board states evaluated). At
// that point, root->son represents the *current* best move; however, instead
// of simply choosing it, we iteratively go a level deeper to see how the next
// move along the path that gave us the current best move affects things. Each
// time we descend and evaluate, we propagate the score upwards, doing an
// extract()/insert() at each level to ensure that the new information has the
// capacity to change the decisions made at higher levels if appropriate.
// Note: A call to descend() doesn't necessarily change the depth of the "son":
// if the newly added node makes the current best move worse, the
// extract()/insert() may move its parent away from the head position amongst
// its siblings (thereby moving the newly added node off the "son" path).
int descend(node *f) {
  static int depth;
  if (didabort() || nodes > maxnodes || depth >= maxply) return(0);
  if (f->son) {
    node* n = f->son;
    makemove(n);
    depth++;
    int ret = descend(n);
    depth--;
    extract(n);
    insert(n);
    f->value = -f->son->value;
    return(ret);
  }
  else {expandnode(f); return(1);}
}

char debug;

// Return the best move.
// Logic: root represents the most recently executed move. It will typically be
// somewhat expanded already, since the end of move logic doesn't delete nodes
// under the move that is ultimately selected. However, the tree will generally
// contain far fewer nodes than it did just before the last move was selected
// (since irrelevant nodes are pruned once a decision is made). Thus, we run
// fullexpand() in a loop, attempting to go deeper and deeper (albeit in a
// uniform fashion, unlike recurse()) until one of the following conditions is
// met:
// 1) sentinel high score (abs_val == 30000) has propagated upwards indicating
//    someone has no more moves
//    Rationale: Someone having no more moves is *very* good for the other
//    player.
// 2) fullexpand() returns 0 indicating either number of nodes created has
//    gotten within threshold of max or that maxevaluate nodes have been
//    evaluated
// At this point, the tree is fleshed out fairly uniformly down to some depth;
// however, instead of simply choosing root->son (the best so far), we use
// descend() to go deeper along the "son" path to see whether the choice can be
// refined. Each call to descend() recurses down the "son" path till it hits the
// leaf, whereupon it expands one level and re-evaluates the board. This
// evaluation represents an improvement over the previous prediction, as it
// takes one more move into account; thus, when the new score is propagated
// upwards (in the postorder path of the descend() traversal),
// extract()/insert() are performed at each level to ensure that the "son" path
// can change to reflect the additional information. As with the fullexpand()
// recursion, there are 2 ways to break the recursion:
// 1) sentinel high score
// 2) descend() returns 0 indicating either that maxnodes have been created or
//    max depth has been reached
//    Note: Unlike fullexpand() recursion, there's no check on # of node
//    evaluations here.
// Note: It's not expected that either the fullexpand() or descend() loops would
// ever be terminated by an actual (non-sentinel) score over 28000; termination
// typically occurs because one of the max parameters has been hit.
node *calcmove(node *root) {	// return best move after root
  expandnode(root);
  if (!root->son) return(0);	// no move due to loss
  if (debug) printf("calcmove() initial nodes = %d\n",nodes);
  evaluated = 0;
  // If only 1 child, there's no choice to be made: an only child is the best
  // move by definition.
  if (root->son->brother) {
    int x;
    for (x = 1; abs(root->value)<28000 && fullexpand(root,x); x++);
    piece saveboard[45]; memmove(saveboard,b,sizeof(b));
    while (abs(root->value)<28000) {
      x = descend(root);
      memmove(b,saveboard,sizeof(b));
      if (!x) break;
    }
  }
  if (debug) printf(" evaluated %d, nodes = %d\n", evaluated, nodes);
  return(root->son);
}

// the actual game state ----------------

node *root,*undoroot;

piece jumpboards[24][45];	// saved boards for undoing jumps
int nextjump;

char user;	// 0 = black, 1 = white
char playing;   // cleared when game over to stop move calculation and such
char autoplay;  // enables computer playing for both players

void newgame(void) {

  int n;
  // Set the initial state of each square: BLACK, WHITE, or...
  // BLUE:  invalid border position
  // EMPTY: valid empty square
  for (n=0; n<5; n++) b[n] = BLUE;
  for (n=5; n<18; n++) b[n] = WHITE;
  for (n=18; n<27; n++) b[n] = EMPTY;
  for (n=27; n<40; n++) b[n] = BLACK;
  for (n=40; n<45; n++) b[n] = BLUE;
  b[13] = b[22] = b[31] = BLUE;

  // Mark the 8 "central" squares to facilitate simple and efficient test in
  // evaluate(). (Apparently, Kings are more valuable in central positions.)
  centralsquares[15] = centralsquares[16] =
    centralsquares[19] = centralsquares[20] =
    centralsquares[24] = centralsquares[25] =
    centralsquares[28] = centralsquares[29] = 1;

  // set up initial search tree:
  // "nextjump" marks the top of the stack of saved board states required to
  // support undo. Only moves involving jumps require an element in the stack.
  nextjump = 0;
  // Get rid of undo tree from any previous game.
  killnode(undoroot);
  undoroot = root = newnode();

  // root is a nonexistent move just before the game's first move. Designating
  // it white's move ensures that first real move is black's.
  root->who = 1;
  user = 0;      // user always starts out black, but can switch any time
  playing = 1;
}

// Execute the input move, pruning (recursively) all of its (now obsolete)
// sibling nodes and making the executed node the new root, with the previous
// root retained in a singly-linked chain of nodes *above* root to support undo.
void domove(node* move) {
  // If this move contains jumps, "from" and "to" won't be sufficient to undo:
  // we must save the entire board in its *pre-move* state in a stack, which is
  // popped each time a move involving jumps is undone.
  if (move->jump) memmove(jumpboards[nextjump++],b,sizeof(b));
  makemove(move);      // execute!
  extract(move);       // extract to protect from kill
  killnode(root->son); // kill all but the executed move and its descendants
  // Important Note: old root is not killed, but kept connected to the move we
  // just made (which becomes the new root) to support undo; thus, the tree
  // above "root" is a singly-linked chain back to "undoroot".
  root->son = move;
  root = move;
  // If debugging, call evaluateboard() again with print arg set to display a
  // detailed breakdown of the score.
  if (debug) evaluateboard(move,1);
}

// Undo the most recent move.
node* undomove() {
  node *n = root;
  if (n == undoroot) return 0; // no more undo possible
  // If most recent move is a jump, the last element of jumpboards[] represents
  // the state of the entire board prior to the move; otherwise, reconstruct
  // the old board state using "from" and "to", un-kinging the moved piece if
  // the move made it a king.
  if (n->jump) memmove(b,jumpboards[--nextjump],sizeof(b));
  else {
    b[n->from] = b[n->to];
    if (n->king) b[n->from] &= (WHITE|BLACK);
    b[n->to] = EMPTY;
  }
  // Now that we've reversed the effects of the move being undone, rewind root
  // to preceding move and kill the undone node.
  root = n->father;
  // Note: There is no reason to keep the chain of nodes rooted at the undone
  // node. It contains only the nodes whose moves were actually chosen, not
  // necessarily the optimal moves. If we were to do a full expansion on the
  // father of the undone node, the resulting "son" path might look
  // completely different. Moreover, although the scores cached on the "son"
  // path were correct when those nodes were selected, they will most likely
  // need to change at least once as part of full expansion before another move
  // is selected. (Recall that a score is calculated only for leaf nodes, with
  // leaf scores propagating upwards.) Finally, note that there's a very good
  // chance that the chain of nodes would have been pruned after the very next
  // move anyways, since if we're undoing a node, it's very likely we want to
  // choose a different path.
  killnode(n);
  root->son = 0;
  // If game was over before the undo, root->value will have one of the large
  // abs value sentinels (eg, +/-30000), but this is no longer valid, since the
  // node we just discarded most likely had siblings that were discarded when
  // the move that led to end of game was chosen. root->value will be
  // recalculated before it's used for move selection, but for now, just set it
  // to something that can't be mistaken for game over.
  root->value = 0;	// prevent it from thinking game is over
  playing = 1;
  // Var "user" indicates the color of (non-computer) player: 0=black 1=white
  // Black always moves first by rule; the implementation guarantees this by
  // setting undoroot->who = 1 (white). Undos always occur in pairs (computer
  // and player) on player's turn, and there is no mechanism for changing
  // players on an undo. Thus, if user has swapped sides (to white) before
  // rewinding to start of game (undoroot), the final undomove will be a nop,
  // effectively swapping player back to black (as at start of game). In such
  // cases, the user=0 here gets "user" var back in sync with gameplay.
  // Note: It would be possible, when user has switched sides, to have the
  // gameplay begin with computer after a rewind (meaning first move would occur
  // immediately after the final undo), but it's probably better to have a
  // rewind to start work more like a new game, forcing user to switch back to
  // white manually before making his first move if that's what he wants.
  if (root == undoroot) user = 0;
  return n;
}

// usermoves() macro uses _usermoves[] to map valid board move target indices
// 5-39 to their corresponding col letter (A-H) and 1-based row index (1-8).
// Ex: Square 5 (B1)
//   usermoves(5, 1) => 'B'
//   usermoves(5, 2) => '1'
const char _usermoves[] =
"B1D1F1H1A2C2E2G2??B3D3F3H3A4C4E4G4??B5D5F5H5A6C6E6G6??B7D7F7H7A8C8E8G8??";
#define usermoves(x,y) _usermoves[2*((x)-5)+(y)-1]

void dumpnode(node *n, int help) {
  int x = n->from;
  int y = n->to;
  if (help) printf("%c%c %c%c\t- ",
		   usermoves(x,1),usermoves(x,2),
		   usermoves(y,1),usermoves(y,2));
  printf("%s %ss from %c%c to %c%c",
	 n->who ? "White" : "Black",
	 n->jump ? "jump" : "move",
	 usermoves(x,1),usermoves(x,2),
	 usermoves(y,1),usermoves(y,2));
  if (n->jump) {
    for (int i=0; i<32; i++) if (n->jump & (1<<i))
      printf(", %c%c",usermoves(10+i,1),usermoves(10+i,2));
    printf(" removed");
  }
  printf(" (%+d).\n",n->value);
}

int abortflag;

////////////////////////////////////////////////////////////////
// VT100 Interface:
#ifdef VT100

void positioncursor(int i) {
  printf("\033[%d;%dH",
	 usermoves(i,2)-'0'+1,
	 2*(usermoves(i,1)-'A')+1);
}

void outpiecename(piece n) {
  printf(n&BLACK ? "\033[1;7m" : "\033[1m");
  putchar(" BW??BW??"[n]);
  putchar(" BW??KK??"[n]);
  printf("\033[0m");
}

void VT100board(void) {
  printf("\033<\033[H\033[J\033[10r");
  int l = 0;
  puts(" A B C D E F G H");
  for (int i=0; i<4; i++) {
    int j = 9*i+5;
    int k;
    for (k=0; k<4; k++) {
      printf("\033[7m  \033[0m");
      outpiecename(b[j+k]);
    }
    l++;
    printf("%d\n",l);
    j += 4;
    for (k=0; k<4; k++) {
      outpiecename(b[j+k]);
      printf("\033[7m  \033[0m");
    }
    l++;
    printf("%d\n",l);
  }
}

void VT100move(node *n, int) {
  if (!n) return;
  printf("\0337");
  positioncursor(n->from);
  outpiecename(b[n->from]);
  positioncursor(n->to);
  outpiecename(b[n->to]);
  if (n->jump) for(int i=0; i<32; i++) {
    if (n->jump & (1<<i)) {
      positioncursor(10+i);
      outpiecename(b[10+i]);
    }
  }
  printf("\0338");
}

int decode(char *m) {
  int i;
  for(i=5; i<=40; i++)
    if (toupper(m[0])==usermoves(i,1) && m[1]==usermoves(i,2)) return(i);
  return(0);
}

#include <signal.h>

static void sigint(...) {
  abortflag = 1;
  signal(SIGINT,sigint);
}

void fixexit(int x) {
  printf("\0337\033[r\0338");
  exit(x);
}

// Returns a son, or 0 if no move specified, or root to cause "help"
node *getusermove(void) {
  int i,j;
  node *t;
  char line[100],*m1,*m2;

  if (playing)
    printf("\033[1m%s's move?\033[0m ",root->who ? "Black" : "White");
  else
    printf("\033[1mCommand?\033[0m ");
  abortflag = 0;
  if (!fgets(line, sizeof(line), stdin)) {
    putchar('\n');
    if (feof(stdin)) fixexit(0);
    return 0;
  }
  for (m1 = line; *m1 && *m1<=' '; m1++);
  if (!*m1) return(0);
  m2 = m1+1;
  if (*m2) m2++;
  for (; *m2 && *m2<'0'; m2++);
  if (playing && m1[1]>='0' && m1[1]<='9') {
    i = decode(m1);
    j = decode(m2);
    if (i && j) for (t = root->son; t; t = t->brother)
      // This is the nominal return path, taken when user enters a row/col
      // corresponding to one of the valid moves (children of root).
      if (t->from == i && t->to == j) return(t);
    puts("Valid moves are:");
    m1[0] = 'L';
  }
  switch(toupper(m1[0])) {
  case 0: return(0);
  case 'A':
    if (playing) autoplay = 1;
    return(root);
  case 'C':
    puts(copyright);
    break;
  case 'D':
    debug = !debug;
    printf("Debug is now %s.", debug ? "on" : "off");
    break;
  case 'F':
    forcejumps = !forcejumps;
    printf("Forced jumps rule is now %s.",forcejumps ? "on" : "off");
    killnode(root->son); root->son = 0;
    return(0);
  case 'L':
    expandnode(root);
    if (playing) for (t = root->son; t; t = t->brother) dumpnode(t,1);
    break;
  case 'M':
    return(playing ? root : 0);
  case 'N':
    newgame();
    VT100board();
    return(0);
  case 'P':
    printf("I expect the following moves:\n");
    for (t = root->son; t; t = t->son) dumpnode(t,0);
    break;
  case 'Q':
    fixexit(0);
  case 'R':
    VT100board();
    break;
  case 'S':
    user = !user;
    return(root);
  case 'U':
    VT100move(undomove(),1);
    VT100move(undomove(),1);
    return(0);
  case '+':
    maxevaluate = maxnodes = 2*maxevaluate;
    goto J2;
  case '-':
    if (maxevaluate > 1)
      maxevaluate = maxnodes = maxevaluate/2;
  J2: printf("Moves evaluated set to %d.",maxevaluate);
    break;
  default:
    puts(
	 "A(utoplay)\n"
	 "C(opyright)\n"
	 "D(ebug on/off)\n"
	 "F(orce jumps rule on/off)\n"
	 "L(ist legal moves)\n"
	 "M(ake a move for me)\n"
	 "N(ew game)\n"
	 "P(redict next few moves)\n"
	 "Q(uit)\n"
	 "R(edraw screen)\n"
	 "S(witch sides)\n"
	 "U(ndo)\n"
	 "+	- smarter\n"
	 "-	- stupider");
    expandnode(root);
    for (t = root->son; t; t = t->brother) dumpnode(t,1);
  }
  return(0);
}

// Main game loop for terminal-based game.
int VT100main() {
  signal(SIGINT,sigint);
  VT100board();
  for (;;) {
    if (playing) {
      // Note: At this point, node tree will generally
      // contain only the preceding move and its descendants.
      expandnode(root);
      if (!root->son) {
	printf("%s has no move.  Game over.",root->who ? "Black" : "White");
	playing = autoplay = 0;
      }
    }
    node* move;
    if (playing && (autoplay || root->who == user)) {
      move = calcmove(root);
      if (move->value <= -30000) {
 	printf("%s resigns.", move->who ? "White" : "Black");
 	move = 0;
 	playing = autoplay = 0;
      }
    } else {
      move = getusermove();
      // Special Case: If getusermove() returns root, it means user has
      // requested help by entering 'M' in lieu of a valid move.
      if (move == root) move = calcmove(root);
    }
    if (move) {
      dumpnode(move,0);
      // Partial Understanding Note: domove performs the move, then clears out
      // the node tree, leaving only move as both root and son.
      domove(move);
      VT100move(move,0);
    }
  }
}

#endif

////////////////////////////////////////////////////////////////
// fltk interface:
#ifdef FLTK

#include <FL/Fl.H>
#include <FL/Fl_Double_Window.H>
#include <FL/Fl_PNG_Image.H>
#include <FL/fl_draw.H>
#include <FL/Fl_Menu_Item.H>
#include <FL/fl_ask.H>

//----------------------------------------------------------------
// Checkers pieces with built in transparency/drop shadows
#include "pixmaps/black_checker_png.h"
#include "pixmaps/white_checker_png.h"
#include "pixmaps/black_checker_king_png.h"
#include "pixmaps/white_checker_king_png.h"

Fl_PNG_Image *png[4];

void make_pieces() {
  if (png[0]) return;
  int which = 0;
  png[which++] = new Fl_PNG_Image(NULL, (const unsigned char *)pixmaps_black_checker_png,      sizeof(pixmaps_black_checker_png));
  png[which++] = new Fl_PNG_Image(NULL, (const unsigned char *)pixmaps_white_checker_png,      sizeof(pixmaps_white_checker_png));
  png[which++] = new Fl_PNG_Image(NULL, (const unsigned char *)pixmaps_black_checker_king_png, sizeof(pixmaps_black_checker_king_png));
  png[which++] = new Fl_PNG_Image(NULL, (const unsigned char *)pixmaps_white_checker_king_png, sizeof(pixmaps_white_checker_king_png));
}

#define ISIZE 62	// old: 56

// Draws piece of input type at specified offset, but only if at least part of
// the piece is within the current clip region.
void draw_piece(int which, int x, int y) {
  if (!fl_not_clipped(x,y,ISIZE,ISIZE)) return;
  switch (which) {
    case BLACK: which = 0; break;
    case WHITE: which = 1; break;
    case BLACKKING: which = 2; break;
    case WHITEKING: which = 3; break;
    default: return;
  }
  png[which]->draw(x,y);
}

//----------------------------------------------------------------

class Board : public Fl_Double_Window {
  void draw();
  int handle(int);
public:
  void drag_piece(int, int, int);
  void drop_piece(int);
  void animate(node* move, int backwards);
  void computer_move(int);
  Board(int w, int h) : Fl_Double_Window(w,h,"FLTK Checkers") {color(15);}
};

#define BOXSIZE 52
#define BORDER 4
#define BOARDSIZE (8*BOXSIZE+BORDER)
#define BMOFFSET 5

static int erase_this;  // real location of dragging piece, don't draw it
static int dragging;	// piece being dragged
static int dragx;	// where it is
static int dragy;
static int showlegal;	// show legal moves

int squarex(int i) {return (usermoves(i,1)-'A')*BOXSIZE+BMOFFSET;}
int squarey(int i) {return (usermoves(i,2)-'1')*BOXSIZE+BMOFFSET;}

void Board::draw() {
  make_pieces(); // do-nothing after first call
  // -- draw the board itself
  fl_draw_box(box(),0,0,w(),h(),color());
  // -- draw all dark tiles
  fl_color((Fl_Color)10 /*107*/);
  int x; for (x=0; x<8; x++) for (int y=0; y<8; y++) {
    // Optimization Note: Could skip drawing this and other stuff when
    // fl_not_clipped() returns false.
    if (!((x^y)&1)) fl_rectf(BORDER+x*BOXSIZE, BORDER+y*BOXSIZE,
			     BOXSIZE-BORDER, BOXSIZE-BORDER);
  }
  // -- draw outlines around the fileds
  fl_color(FL_DARK3);
  for (x=0; x<9; x++) {
    fl_rectf(x*BOXSIZE,0,BORDER,h());
    fl_rectf(0,x*BOXSIZE,w(),BORDER);
  }
  // Draw all pieces except for the one currently being dragged (indicated by
  // "erase_this"), which will be drawn later.
  for (int j = 5; j < 40; j++) if (j != erase_this) {
    draw_piece(b[j], squarex(j), squarey(j));
  }
  // Are we showing all legal moves?
  // Note: showlegal can have 3 values:
  // 0: show nothing
  // 1: (set by "legal" menu item)
  //    show currently available moves
  // 2: (set by "predict" menu item)
  //    show all moves along the optimal move path (as far as it's been calculated)
  if (showlegal) {
    fl_color(FL_WHITE);
    node* n;
    // Draw white arrows between from/to squares for all legal moves.
    for (n = root->son; n; n = showlegal==2 ? n->son : n->brother) {
      int x1 = squarex(n->from)+BOXSIZE/2-5;
      int y1 = squarey(n->from)+BOXSIZE/2-5;
      int x2 = squarex(n->to)+BOXSIZE/2-5;
      int y2 = squarey(n->to)+BOXSIZE/2-5;
      fl_line(x1,y1,x2,y2);
      fl_push_matrix();
      fl_mult_matrix(x2-x1,y2-y1,y1-y2,x2-x1,x2,y2);
      fl_begin_polygon();
      fl_vertex(0,0);
      fl_vertex(-.3, .1);
      fl_vertex(-.3, -.1);
      fl_end_polygon();
      fl_pop_matrix();
    }
    // Number the arrows drawn above.
    // showlegal==1 - lower number = better move
    // showlegal==2 - lower number = earlier move
    int num = 1;
    fl_color(FL_BLACK);
    fl_font(FL_BOLD,10);
    for (n = root->son; n; n = showlegal==2 ? n->son : n->brother) {
      int x1 = squarex(n->from)+BOXSIZE/2-5;
      int y1 = squarey(n->from)+BOXSIZE/2-5;
      int x2 = squarex(n->to)+BOXSIZE/2-5;
      int y2 = squarey(n->to)+BOXSIZE/2-5;
      char buf[20]; sprintf(buf,"%d",num);
      fl_draw(buf, x1+int((x2-x1)*.85)-3, y1+int((y2-y1)*.85)+5);
      num++;
    }
  }
  // Draw the dragged piece at its current location (cached in static vars on
  // each call to drag_piece().
  if (dragging) draw_piece(dragging, dragx, dragy);
}

// drag the piece on square j to dx dy, or undo drag if j is zero:
// Note: dx/dy are the offsets from the origin of the piece being dragged.
void Board::drag_piece(int j, int dx, int dy) {
  dy = (dy&-2) | (dx&1); // make halftone shadows line up
  if (j != erase_this) drop_piece(erase_this); // should not happen
  if (!erase_this) { // pick up old piece
    // Initiate drag of piece on square j.
    dragx = squarex(j); dragy = squarey(j);
    // Save index of square whose piece we should skip in the draw loop.
    erase_this = j;
    // Note: I believe this is somewhat redundant, as we could always obtain
    // the piece mask from b[erase_this].
    dragging = b[j];
  }
  // If current drag position is different from saved position, invalidate
  // square at both positions to ensure that both the uncovered and
  // newly-covered regions are redrawn.
  // Note: Simply calling damage(FL_DAMAGE_ALL) would be sufficient to engender
  // call to draw(), but would give us no way to avoid drawing pieces
  // unnecessarily.
  // Optimization Note: Currently, only draw_piece() considers damage bits: it
  // won't bother drawing a piece that isn't within current clipping region.
  // draw() itself, however, draws the entire board unconditionally. Docs
  // suggests that clipping provides some performance benefit even when
  // application logic doesn't use damage information to skip drawing
  // operations, but it would probably be better if draw() skipped drawing
  // portions of the board that don't need it. (Typically, a region of the
  // board needs to be redrawn only when pieces are being moved over it.)
  if (dx != dragx || dy != dragy) {
    damage(FL_DAMAGE_ALL, dragx, dragy, ISIZE, ISIZE);
    damage(FL_DAMAGE_ALL, dx, dy, ISIZE, ISIZE);
  }
  dragx = dx;
  dragy = dy;
}

// drop currently dragged piece on square j
void Board::drop_piece(int j) {
  if (!erase_this) return; // should not happen!
  erase_this = 0;
  dragging = 0;
  int x = squarex(j);
  int y = squarey(j);
  if (x != dragx || y != dragy) {
    damage(4, dragx, dragy, ISIZE, ISIZE);
    damage(4, x, y, ISIZE, ISIZE);
  }
}

// show move (call this *before* the move, *after* undo):
void Board::animate(node* move, int backwards) {
  if (showlegal) {showlegal = 0; redraw();}
  if (!move) return;
  int f = move->from;
  int t = move->to;
  if (backwards) {int x = f; f = t; t = x;}
  int x1 = squarex(f);
  int y1 = squarey(f);
  int x2 = squarex(t);
  int y2 = squarey(t);
  const int STEPS=233335;
  for (int j=0; j<STEPS; j++) {
    int x = x1+(x2-x1)*j/STEPS;
    int y = y1+(y2-y1)*j/STEPS;
    drag_piece(move->from,x,y);
    Fl::flush();
  }
  drop_piece(t);
  if (move->jump) redraw();
}

int busy; // causes pop-up abort menu

void Board::computer_move(int help) {
  if (!playing) return;
  cursor(FL_CURSOR_WAIT);
  Fl::flush();
  busy = 1; abortflag = 0;
  // Determine computer's best move.
  node* move = calcmove(root);
  busy = 0;
  if (move) {
    if (!help && move->value <= -30000) {
      fl_message("%s resigns", move->who ? "White" : "Black");
      playing = autoplay = 0;
      cursor(FL_CURSOR_DEFAULT);
      return;
    }
    animate(move,0);
    domove(move);
  }
  expandnode(root);
  if (!root->son) {
    fl_message("%s has no move", root->who ? "Black" : "White");
    playing = autoplay = 0;
  }
  if (!autoplay) cursor(FL_CURSOR_DEFAULT);
}

extern Fl_Menu_Item menu[];
extern Fl_Menu_Item busymenu[];

int Board::handle(int e) {
  if (busy) {
    // Computer is calculating its move.
    const Fl_Menu_Item* m;
    switch(e) {
    case FL_PUSH:
      // User is attempting to move, but it's not his turn. Popup the busy menu...
      // Note: I'm thinking it would be difficult to click this quickly.
      m = busymenu->popup(Fl::event_x(), Fl::event_y(), 0, 0, 0);
      if (m) m->do_callback(this, (void*)m);
      return 1;
    case FL_SHORTCUT:
      m = busymenu->test_shortcut();
      if (m) {m->do_callback(this, (void*)m); return 1;}
      return 0;
    default:
      return 0;
    }
  }
  node *t, *n;
  static int deltax, deltay;
  int dist;
  const Fl_Menu_Item* m;
  switch (e) {
  case FL_PUSH:
    if (Fl::event_button() > 1) {
      // Popup context menu
      m = menu->popup(Fl::event_x(), Fl::event_y(), 0, 0, 0);
      if (m) m->do_callback(this, (void*)m);
      return 1;
    }
    if (playing) {
      // User's turn and he's about to initiate a drag. Expand the root so we
      // know what moves are legal.
      // Note: root will generally already be expanded, since the preceding
      // computer move would have expanded several moves into the future, and
      // the moves descended from the move selected aren't pruned.
      expandnode(root);
      // Loop over legal moves...
      for (t = root->son; t; t = t->brother) {
        // Get coords of this move's starting square.
	int x = squarex(t->from);
	int y = squarey(t->from);
        // Was the mouse down inside current move's square?
	if (Fl::event_inside(x,y,BOXSIZE,BOXSIZE)) {
          // Found the piece! Cache mouse click offset relative to its square.
          // Explanation: As piece is dragged, distance between mouse pointer
          // and click point determines the piece's current location.
	  deltax = Fl::event_x()-x;
	  deltay = Fl::event_y()-y;
	  drag_piece(t->from,x,y);
	  return 1;
	}
      }
    }
    return 0;
  case FL_SHORTCUT:
    m = menu->test_shortcut();
    if (m) {m->do_callback(this, (void*)m); return 1;}
    return 0;
  case FL_DRAG:
    drag_piece(erase_this, Fl::event_x()-deltax, Fl::event_y()-deltay);
    return 1;
  case FL_RELEASE:
    // find the closest legal move he dropped it on:
    // Loop over all possible moves (children of root) looking for one whose
    // destination square is sufficiently close to the (dragged) location and
    // closer than any others.
    dist = 50*50; n = 0;
    for (t = root->son; t; t = t->brother) if (t->from==erase_this) {
      // Calculate distance between 
      int d1 = Fl::event_x()-deltax-squarex(t->to);
      int d = d1*d1;
      d1 = Fl::event_y()-deltay-squarey(t->to);
      d += d1*d1;
      if (d < dist) {dist = d; n = t;}
    }
    // If none of the candidate moves is consistent with the drop location,
    // call drop_piece() with the *old* square index to cancel the drag; else
    // call it with "to" to complete the drag. Note that the index determines
    // which location (in addition to current) is "damaged" for redraw.
    if (!n) {drop_piece(erase_this); return 1;} // none found
    drop_piece(n->to);
    // Complete the move.
    domove(n);
    if (showlegal) {showlegal = 0; redraw();}
    if (n->jump) redraw();
    computer_move(0);
    return 1;
  default:
    return 0;
  }
}

void quit_cb(Fl_Widget*, void*) {exit(0);}

int FLTKmain(int argc, char** argv) {
  Fl::visual(FL_DOUBLE|FL_INDEX);
  Board b(BOARDSIZE,BOARDSIZE);
  b.color(FL_BACKGROUND_COLOR);
  b.callback(quit_cb);
  b.show(argc,argv);
  return Fl::run();
} 

void autoplay_cb(Fl_Widget*bp, void*) {
  if (autoplay) {autoplay = 0; return;}
  if (!playing) return;
  Board* b = (Board*)bp;
  autoplay = 1;
  while (autoplay) {b->computer_move(0); b->computer_move(0);}
}

#include <FL/Fl_Box.H>
Fl_Window *copyright_window;
void copyright_cb(Fl_Widget*, void*) {
  if (!copyright_window) {
    copyright_window = new Fl_Window(400,270,"Copyright");
    copyright_window->color(FL_WHITE);
    Fl_Box *b = new Fl_Box(20,0,380,270,copyright);
    b->labelsize(10);
    b->align(FL_ALIGN_LEFT|FL_ALIGN_INSIDE|FL_ALIGN_WRAP);
    copyright_window->end();
  }
  copyright_window->hotspot(copyright_window);
  copyright_window->set_non_modal();
  copyright_window->show();
}

void debug_cb(Fl_Widget*, void*v) {
  debug = !debug;
  ((Fl_Menu_Item*)v)->flags =
    debug ? FL_MENU_TOGGLE|FL_MENU_VALUE : FL_MENU_TOGGLE;
}

void forced_cb(Fl_Widget*b, void*v) {
  forcejumps = !forcejumps;
  ((Fl_Menu_Item*)v)->flags =
    forcejumps ? FL_MENU_TOGGLE|FL_MENU_VALUE : FL_MENU_TOGGLE;
  killnode(root->son); root->son = 0;
  if (showlegal) {expandnode(root); b->redraw();}
}

void move_cb(Fl_Widget*pb, void*) {
  Board* b = (Board*)pb;
  if (playing) b->computer_move(1);
  if (playing) b->computer_move(0);
}

void newgame_cb(Fl_Widget*b, void*) {
  showlegal = 0;
  newgame();
  b->redraw();
}

void legal_cb(Fl_Widget*pb, void*) {
  if (showlegal == 1) {showlegal = 0; ((Board*)pb)->redraw(); return;}
  if (!playing) return;
  expandnode(root);
  showlegal = 1; ((Board*)pb)->redraw();
}

void predict_cb(Fl_Widget*pb, void*) {
  if (showlegal == 2) {showlegal = 0; ((Board*)pb)->redraw(); return;}
  if (playing) expandnode(root);
  showlegal = 2; ((Board*)pb)->redraw();
}

void switch_cb(Fl_Widget*pb, void*) {
  user = !user;
  ((Board*)pb)->computer_move(0);
}

// Undo last 2 moves: player and computer.
void undo_cb(Fl_Widget*pb, void*) {
  Board* b = (Board*)pb;
  b->animate(undomove(),1);
  b->animate(undomove(),1);
}

//--------------------------

#include <FL/Fl_Slider.H>
#include <FL/Fl_Value_Output.H>

Fl_Window *intel_window;
Fl_Value_Output *intel_output;

void intel_slider_cb(Fl_Widget*w, void*) {
  double v = ((Fl_Slider*)w)->value();
  int n = int(v*v);
  intel_output->value(n);
  maxevaluate = maxnodes = n;
}

void intel_cb(Fl_Widget*, void*) {
  if (!intel_window) {
    intel_window = new Fl_Window(200,25,"Checkers Intelligence");
    Fl_Slider* s = new Fl_Slider(60,0,140,25);
    s->type(FL_HOR_NICE_SLIDER);
    s->minimum(1); s->maximum(500); s->value(50);
    s->callback(intel_slider_cb);
    intel_output = new Fl_Value_Output(0,0,60,25);
    intel_output->value(maxevaluate);
    intel_window->resizable(s);
  }
  intel_window->hotspot(intel_window);
  intel_window->set_non_modal();
  intel_window->show();
}

//---------------------------

void stop_cb(Fl_Widget*, void*) {abortflag = 1;}

void continue_cb(Fl_Widget*, void*) {}

Fl_Menu_Item menu[] = {
  {"Autoplay", 'a', autoplay_cb},
  {"Legal moves", 'l', legal_cb},
  {"Move for me", 'm', move_cb},
  {"New game", 'n', newgame_cb},
  {"Predict", 'p', predict_cb},
  {"Switch sides", 's', switch_cb},
  {"Undo", 'u', undo_cb, 0, FL_MENU_DIVIDER},
  {"Forced jumps rule", 'f', forced_cb, 0, FL_MENU_TOGGLE|FL_MENU_VALUE},
  {"Debug", 'd', debug_cb, (void *)"d", FL_MENU_TOGGLE},
  {"Intelligence...", 'i', intel_cb, 0, FL_MENU_DIVIDER},
  {"Copyright", 'c', copyright_cb},
  {"Quit", 'q', quit_cb},
  {0}};

Fl_Menu_Item busymenu[] = {
  {"Stop", '.', stop_cb},
  {"Autoplay", 'a', autoplay_cb},
  {"Continue", 0, continue_cb},
  {"Debug", 'd', debug_cb, (void *)"d", FL_MENU_TOGGLE},
  {"Intelligence...", 'i', intel_cb},
  {"Copyright", 'c', copyright_cb},
  {"Quit", 'q', quit_cb},
  {0}};

#endif

////////////////////////////////////////////////////////////////
// parts shared by both interface:

#ifdef FLTK
#ifdef VT100
#define BOTH
#endif
#endif

#ifdef BOTH
int terminal;
int arg(int, char **argv, int &i) {
  if (argv[i][1] == 't') {terminal = 1; i++; return 1;}
  return 0;
}
#endif

int didabort(void) {
#ifdef FLTK
#ifdef BOTH
  if (!terminal)
#endif
    Fl::check();
#endif
  if (abortflag) {
    autoplay = 0;
    abortflag = 0;
    return 1;
  }
  return(0);
}

int main(int argc, char **argv) {
  seed = time(0);
  newgame();
#ifdef BOTH
  fl_register_images();
  int i = 1;
  if (Fl::args(argc, argv, i, arg) < argc) {
    fprintf(stderr," -t : use VT100 display\n", Fl::help);
    exit(1);
  }
  if (!fl_getenv("DISPLAY")) terminal = 1;
  if (!terminal)
#endif
#ifdef FLTK
    return FLTKmain(argc,argv);
#endif
#ifdef VT100
  return VT100main();
#endif
}

//
// End of "$Id$".
//
