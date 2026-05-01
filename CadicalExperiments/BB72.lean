import Mathlib.Data.BitVec
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide

set_option maxRecDepth 9999999

def HX : BitVec (36 * 72) :=
  0x1000008200c0020000080000410840010000040000208c0000800080000010460000400040000008230000200020000004118000100080400002000300080040200001002100040020100000803000020012000000401800010009000000200c0000800480000010060000408201000000000c0020410080000000840010208040000000c0000810480000000060000408240000000030000204120000000018000102080400080000300001040200040002100000820100020003000000412000010001800000209000008000c0000010480000400060000008201000200000c0000410080010000840000208040008000c0000010480000400060000008240000200030000004120000100018000002080400080000300001040200040002100000820100020003000000412000010001800000209000008000c000001048000040006

def N : BitVec (42 * 72) :=
  0x120920800000000000090490400000000000048248200000000000804904100000000000402482080000000000201241040000000000124104020000000000092082010000000000049041008000000000824820004000000000412410002000000000209208001000000000db6000000d80000000b6d000000b40000000e7ca000005280000002a8500000f1400000029e880000f22000000cf9440000a11000000600020000120800000eb6010000d10400000491a08000e20200000268504000710100000ade882000b200800000f9441000810040000590c00000e30020000cb4c00000230010000826c00000430008000a6fc00000730004000efdc00000b30002000cb4c00000d300010006dce000009200008006f8700000910000400896980000c2000020044b4c0000610000100459040000620000080a2c8000003100000404b3218000e10000020c05b0c0002200000106225860001100000080db8c300082000000486dc6100041000000224a430000720000001

def loc_constraints_ith
  (loc0 loc1 loc2 loc3 loc4 : BitVec 7)
  (errs : BitVec 72)
  (i : ℕ) :=
  errs[i]! = (loc0 = i ∨ loc1 = i ∨ loc2 = i ∨ loc3 = i ∨ loc4 = i)

def loc_constraints_aux
  (loc0 loc1 loc2 loc3 loc4 : BitVec 7)
  (errs : BitVec 72)
  (c : ℕ) :=
  match c with
  | 0 => loc_constraints_ith loc0 loc1 loc2 loc3 loc4 errs 0
  | c' + 1 =>
    loc_constraints_ith loc0 loc1 loc2 loc3 loc4 errs c ∧
    loc_constraints_aux loc0 loc1 loc2 loc3 loc4 errs c'

def loc_constraints
  (loc0 loc1 loc2 loc3 loc4 : BitVec 7)
  (errs : BitVec 72) :=
  loc_constraints_aux loc0 loc1 loc2 loc3 loc4 errs 71

def row_parity_constraint_aux
  (errs : BitVec 72) (r : ℕ) (c : ℕ) :=
  let k := 72 * r + c
  match c with
  | 0 => errs[c]! && HX[k]!
  | c' + 1 => (errs[c]! && HX[k]!) ^^ row_parity_constraint_aux errs r c'

def row_parity_constraint (errs : BitVec 72) (r : ℕ) :=
  ¬(row_parity_constraint_aux errs r 71)

def parity_constraints_aux (errs : BitVec 72) (r : ℕ) :=
  match r with
  | 0 => row_parity_constraint errs 0
  | r' + 1 => row_parity_constraint errs r ∧ parity_constraints_aux errs r'

def parity_constraints (errs : BitVec 72) :=
  parity_constraints_aux errs 35

def row_stabilizer_constraint_aux
  (errs : BitVec 72) (r : ℕ) (c : ℕ) :=
  let k := 72 * r + c
  match c with
  | 0 => (errs[c]! && N[k]!)
  | c' + 1 => (errs[c]! && N[k]!) ^^ row_stabilizer_constraint_aux errs r c'

def row_stabilizer_constraint (errs : BitVec 72) (r : ℕ) :=
  row_stabilizer_constraint_aux errs r 71

def stabilizer_constraints_aux
  (errs : BitVec 72) (r : ℕ) :=
  match r with
  | 0 => row_stabilizer_constraint errs 0
  | r' + 1 => row_stabilizer_constraint errs r' ∨
      stabilizer_constraints_aux errs r'

def stabilizer_constraints
  (errs : BitVec 72) :=
  stabilizer_constraints_aux errs 41

set_option maxHeartbeats 0 in
-- heavy unfolding
lemma bb72_test
  (loc0 loc1 loc2 loc3 loc4 : BitVec 7)
  (errs : BitVec 72) :
  ¬ (
    loc_constraints loc0 loc1 loc2 loc3 loc4 errs /\
    parity_constraints errs /\
    stabilizer_constraints errs)
  := by
  simp (maxSteps := 9999999) only [loc_constraints, loc_constraints_aux, loc_constraints_ith,
    Nat.lt_add_one, getElem!_pos, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, eq_iff_iff,
    Nat.reduceLT, Nat.cast_one, Nat.zero_lt_succ,
    Nat.cast_zero, parity_constraints, parity_constraints_aux, row_parity_constraint,
    row_parity_constraint_aux,
    Nat.reduceMul, HX, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false, Bool.and_true,
    mul_one, mul_zero, add_zero,
    bne_self_eq_false, Bool.bne_false, Bool.false_bne, bne_iff_ne, ne_eq, Decidable.not_not,
    zero_add,
    stabilizer_constraints, stabilizer_constraints_aux, row_stabilizer_constraint,
    row_stabilizer_constraint_aux, N,
    or_self, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Bool.decide_or, Bool.or_eq_true,
    not_and, not_or, and_imp]
  bv_check "bb72.lrat"

#print axioms bb72_test
