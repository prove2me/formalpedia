-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCounts_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:18:46.632988+00:00
-- url     : https://prove2.me/submissions/9566b3ef-1dba-4cc7-bcae-1b9474b5b3af

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_graphCountTail_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_matrix_apply_trace

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete prime-field matrix application used by both search predicates.
All row/column counts and operands are runtime data for the same 359-label
program. The format is the actual scalar-frame stream, not a free matrix
oracle. Input recoding is kept separate from this application theorem. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp
open scoped BigOperators

theorem scalarWord_eq (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    MatrixWordEncoding.word p x = SubexpEnumerationPayload.scalarBits x := by
  simp [MatrixWordEncoding.word, MatrixWordEncoding.width, SubexpLiftRing.baseWidth,
    SubexpEnumerationPayload.scalarBits, SubexpEnumerationPayload.scalarWidth]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramParity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The Walsh parity counter uses the same fixed matrix/support code as the
ternary checker. Its output is a physical unary counter, not an abstract sum. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

theorem binaryCell_nonzero (x : ZMod 2) :
    ((binaryCell x).1 || (binaryCell x).2) = decide (x ≠ 0) := by
  fin_cases x <;> decide

theorem binaryCell_encoding (x : ZMod 2) :
    [(binaryCell x).1, (binaryCell x).2] = SubexpEnumerationPayload.scalarBits x := by
  have hw : SubexpEnumerationPayload.scalarWidth 2 = 2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem scalarFrames_binary (xs : List (ZMod 2)) :
    scalarFrames xs = framedCellStream (xs.map binaryCell) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change Encoding.frame (MatrixWordEncoding.word 2 x) ++ scalarFrames xs = _
      rw [scalarWord_eq, ← binaryCell_encoding, ih]
      rfl

theorem cellWeight_binary (xs : List (ZMod 2)) :
    cellWeight (xs.map binaryCell) = (xs.map fun x => if x ≠ 0 then 1 else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, cellWeight, binaryCell_nonzero,
        decide_eq_true_eq, List.sum_cons, ih]
      omega

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramBinaryWeight
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical support counter recognizes the exceptional zero Walsh
character exactly. This is independent of any graph goodness assumption. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open scoped BigOperators

theorem binary_weight_zero_iff {r : ℕ} (a : Cayley.Cube r) :
    cellWeight ((List.ofFn a).map binaryCell) = 0 ↔ a = 0 := by
  rw [cellWeight_binary,List.map_ofFn,List.sum_ofFn]
  constructor
  · intro hz
    change (∑ j : Fin r, if a j ≠ 0 then (1 : ℕ) else 0) = 0 at hz
    funext i
    have hi : (if a i ≠ 0 then 1 else 0 : ℕ) ≤
        ∑ j : Fin r, if a j ≠ 0 then 1 else 0 :=
      Finset.single_le_sum (f := fun j : Fin r => if a j ≠ 0 then (1 : ℕ) else 0)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hz] at hi
    change a i = 0
    by_contra h
    simp [h] at hi
  · rintro rfl
    simp

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed bit-code for one Walsh query up to the scalar inequalities: compute
all dot products mod2, count their support, and recognize the zero character. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

private theorem pair_embed (base : State 8 16) (first second : List Bool) :
    embedState id matrixWordStacks (extendPairState base first second) base =
      extendPairState base first second := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id
    (Fin.castAdd_injective _ _)
  · intro i; rfl
  · intro i; simp [extendPairState,i.isLt]
  · intros; rfl
  · intros; rfl

private theorem pair_embed_result (initial final : State 8 16) (first second : List Bool) :
    embedState id matrixWordStacks (extendPairState initial first second) final =
      extendPairState final first second := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id
    (Fin.castAdd_injective _ _)
  · intro i; rfl
  · intro i; simp [extendPairState,i.isLt]
  · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
  · intro j hj
    have hnot : ¬j.val < 16 := by
      intro h; exact hj ⟨⟨j.val,h⟩,Fin.ext rfl⟩
    simp [extendPairState,hnot]

theorem graphCounts_eval_oai {r D : ℕ} (s : Fin D → Cayley.Cube r) (a : Cayley.Cube r)
    (regs : Fin 8 → Bool) (qbits Dbits : List Bool) :
    ∃ (n : ℕ) (next : ScanState), n + 1 ≤ graphCountsBudget D r ∧
      Eval graphCountsCommand n (extendPairState (matrixInput s a regs) qbits Dbits) next ∧
      next.regs 7 = decide (a ≠ 0) ∧
      next.stacks 9 = List.replicate (WalshExistence.parityWeight s a) true ∧
      next.stacks 16 = qbits ∧ next.stacks 17 = Dbits := by
  obtain ⟨nm,rm,hnm,htm⟩ := matrix_apply_trace s a regs
  have hm := eval_call_lifted MatrixVectorProgram.matrixProgram id matrixWordStacks
    (extendPairState (matrixInput s a regs) qbits Dbits)
    Function.injective_id (Fin.castAdd_injective _ _) htm
  rw [pair_embed,pair_embed_result] at hm
  let y := WalshExistence.parityProducts s a
  let ys := (List.ofFn y).map binaryCell
  let xs := (List.ofFn a).map binaryCell
  have hy : (extendPairState (matrixOutput s a rm) qbits Dbits).stacks 8 = framedCellStream ys :=
    scalarFrames_binary _
  have hx : (extendPairState (matrixOutput s a rm) qbits Dbits).stacks 12 = framedCellStream xs :=
    scalarFrames_binary _
  obtain ⟨nt,out,hnt,ht,hflag,hcount,h16,h17⟩ := graphCountTail_eval ys xs
    (extendPairState (matrixOutput s a rm) qbits Dbits) hy hx (by rfl) (by rfl)
  have hyw : cellWeight ys = WalshExistence.parityWeight s a := by
    rw [cellWeight_binary,List.map_ofFn,List.sum_ofFn]
    change (∑ i : Fin D,if y i ≠ 0 then 1 else 0) = _
    rw [← Finset.sum_filter]
    simp [y,WalshExistence.parityWeight]
  refine ⟨nm+nt,out,?_,hm.seq ht,?_,?_,h16,h17⟩
  · have hw : MatrixWordEncoding.width 2 = 2 := by
      norm_num [MatrixWordEncoding.width,SubexpLiftRing.baseWidth]
    rw [hw] at hnm
    have hyl : ys.length = D := by simp [ys]
    have hxl : xs.length = r := by simp [xs]
    rw [hyl,hxl] at hnt
    unfold graphCountsBudget
    omega
  · apply hflag.trans
    exact decide_eq_decide.mpr (not_congr (binary_weight_zero_iff a))
  · simpa only [hyw] using hcount

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCounts_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCounts_eval_oai
