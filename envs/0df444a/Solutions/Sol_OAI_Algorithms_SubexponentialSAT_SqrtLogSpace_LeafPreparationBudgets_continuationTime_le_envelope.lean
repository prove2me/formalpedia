-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.continuationTime_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:11:29.542723+00:00
-- url     : https://prove2.me/submissions/5a566b5b-b830-4eed-9981-62b1ed9bc6c7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S172

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Space of the concrete sparse-code predicates

The local-code and Walsh predicates are polynomial-time bit programs. These bounds apply
to every candidate, including losing candidates, and every stack in each actual source
prefix. They are intended as the body estimates of bounded-memory enumeration; the
materialized candidate-family programs are not used here.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- Invalid two-bit ternary digits cost at most a square of the old complete
matrix-and-word domain. This power is independent of the input. -/
theorem local_attempts_le_square (t D : ℕ) :
    4 ^ (t * D) * 4 ^ D ≤ (3 ^ (t * D) * 3 ^ D) ^ 2 := by
  rw [← pow_add, ← pow_add]
  calc
    4 ^ (t * D + D) ≤ 9 ^ (t * D + D) := Nat.pow_le_pow_left (by decide) _
    _ = (3 ^ (t * D + D)) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm (t * D + D) 2, pow_mul]
      norm_num

/-- The graph's invalid high-bit words are also charged by a fixed square. -/
theorem graph_attempts_eq_square (D r : ℕ) :
    4 ^ (D * r) * 4 ^ r = (2 ^ (D * r) * 2 ^ r) ^ 2 := by
  rw [← pow_add, ← pow_add, ← pow_mul, Nat.mul_comm (D * r + r) 2, pow_mul]
  norm_num

/-- The local predicate has a fixed polynomial budget, independently of acceptance. -/
theorem local_budget (t D d : ℕ) :
    callbackBudget t D d =
      4000766 * (t * D) + 3595 * t + 713 * D + 43 * d + 1148 := by
  simp only [callbackBudget, wordBudget, wordInputSpan, wordTailBudget,
    OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrixBudget, OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.rowBudget,
    OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgram.termBudget]
  ring

/-- All scalar comparison and cleanup work is included in the Walsh predicate budget. -/
theorem graph_budget (D r qlen Dlen : ℕ) :
    graphCallbackBudget D r qlen Dlen =
      6379582 * (D * r) + 5729 * D + 895 * r + 65 * qlen + 65 * Dlen + 1588 +
        41300 * (2 * (qlen + Dlen + D) + 4) ^ 2 := by
  simp only [graphCallbackBudget, graphWordBudget, graphInputSpan, graphCountsBudget,
    OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrixBudget, OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.rowBudget,
    OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgram.termBudget]
  ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

/-- The streamed checker's retained workspace is a fixed linear polynomial
in its input words, dimensions, and one arithmetic callback budget. -/
theorem candidateSpace_le (A matrixDimension wordDimension callbackCost : ℕ) :
    candidateSpace A matrixDimension wordDimension callbackCost ≤
      20000 * (A + matrixDimension + wordDimension + callbackCost + 1) := by
  have hc : coreSpace (A + 5 * matrixDimension) wordDimension callbackCost ≤
      300 * (A + matrixDimension + wordDimension + callbackCost + 1) := by
    unfold coreSpace
    apply max_le <;> omega
  unfold candidateSpace matrixCheckSpace
  apply max_le
  · omega
  · apply max_le <;> omega

/-- New staging, validation, and complete inner checking add only a fixed
linear factor to the explicit original arithmetic and word-scan budget. -/
theorem candidateBudget_le (A matrixDimension wordDimension callbackCost streamCost : ℕ) :
    candidateBudget A matrixDimension wordDimension callbackCost streamCost ≤
      1000 * (A + matrixDimension + wordDimension + callbackCost + streamCost + 1) := by
  have hc : coreSpace (A + 5 * matrixDimension) wordDimension callbackCost ≤
      300 * (A + matrixDimension + wordDimension + callbackCost + 1) := by
    unfold coreSpace
    apply max_le <;> omega
  unfold candidateBudget matrixCheckTime
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupCostScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform numerical envelope for the actual finite code searches.
Search dimensions occur only in the exponential factor. Encoded metadata
lengths remain in a separate fixed polynomial factor. -/
namespace SubexponentialSAT.SqrtLog.CodeSetupCost
open Filter
open scoped Topology
open CostAssembly Asymptotic

theorem self_le_three_pow (n : ℕ) : n ≤ 3^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 1 ≤ 3^n := Nat.one_le_pow _ _ (by decide)
    omega

end SubexponentialSAT.SqrtLog.CodeSetupCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupCostPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Positive arithmetic normal forms for the exhaustive-search budgets.
The native-budget identities are established separately against25's actual
definitions. Here no machine execution is postulated. -/
namespace SubexponentialSAT.SqrtLog.CodeSetupCost

theorem localNumeric_bound (a w t D d U P Q Z : ℕ)
    (ha : a ≤ Z) (hw : w ≤ Z) (ht : t ≤ Z) (hD : D ≤ Z) (hd : d ≤ Z)
    (hU : U ≤ Z) (hP : P ≤ Z) (hQ : Q ≤ Z) :
    localNumeric a w t D d U P Q ≤ 1000000000000*(Z+1)^6 := by
  calc
    _ ≤ localNumeric Z Z Z Z Z Z Z Z := by
      unfold localNumeric generation localCandidate localVerifier localCallback localWord matrix2
      gcongr
    _ ≤ _ := by
      unfold localNumeric generation localCandidate localVerifier localCallback localWord matrix2
      ring_nf
      omega

theorem graphNumeric_bound (a w D r ql Dl U P Q Z : ℕ)
    (ha : a ≤ Z) (hw : w ≤ Z) (hD : D ≤ Z) (hr : r ≤ Z) (hq : ql ≤ Z) (hd : Dl ≤ Z)
    (hU : U ≤ Z) (hP : P ≤ Z) (hQ : Q ≤ Z) :
    graphNumeric a w D r ql Dl U P Q ≤ 1000000000000*(Z+1)^6 := by
  calc
    _ ≤ graphNumeric Z Z Z Z Z Z Z Z Z := by
      unfold graphNumeric generation graphCandidate graphVerifier graphCallback graphWord matrix2
      gcongr
    _ ≤ _ := by
      unfold graphNumeric generation graphCandidate graphVerifier graphCallback graphWord matrix2
      ring_nf
      omega

/-- The constants and polynomial in encoded lengths are included explicitly.
The two count arguments are the actual numbers of tested candidates. -/
theorem combinedNumeric_bound (a₂ a₃ w₂ w₃ t D d r ql Dl f g H W C : ℕ)
    (ht : t ≤ H) (hD : D ≤ H) (hd : d ≤ H) (hr : r ≤ H)
    (hq : ql ≤ W) (hDl : Dl ≤ W)
    (hC : 1000000000000*(f+g+1)+a₂+a₃+w₂+w₃ ≤ C) :
    f*localNumeric a₃ w₃ t D d (t*D) (3^D) (3^(t*D))+
      g*graphNumeric a₂ w₂ D r ql Dl (D*r) (2^r) (2^(D*r))+1 ≤ envelope C H W := by
  have ha₂ : a₂ ≤ C := by omega
  have ha₃ : a₃ ≤ C := by omega
  have hw₂ : w₂ ≤ C := by omega
  have hw₃ : w₃ ≤ C := by omega
  have hc : 1000000000000*(f+g)+1 ≤ C := by omega
  let E := C+(H+1)^2
  let Y := 3^E
  let Z := Y*(W+1)
  have hE : H ≤ E := by dsimp [E]; nlinarith
  have hE2 : H*H ≤ E := by dsimp [E]; nlinarith
  have hCE : C ≤ E := by dsimp [E]; omega
  have hCY : C ≤ Y := hCE.trans (self_le_three_pow E)
  have hHY : H ≤ Y := hE.trans (self_le_three_pow E)
  have hYY : 1 ≤ Y := Nat.one_le_pow _ _ (by decide)
  have hYZ : Y ≤ Z := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left Y (Nat.succ_pos W)
  have hWZ : W ≤ Z := (Nat.le_succ W).trans (by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (W+1) hYY)
  have hUZ : t*D ≤ Z := (Nat.mul_le_mul ht hD).trans (hE2.trans ((self_le_three_pow E).trans hYZ))
  have hVZ : D*r ≤ Z := (Nat.mul_le_mul hD hr).trans (hE2.trans ((self_le_three_pow E).trans hYZ))
  have hp : 3^D ≤ Z := (Nat.pow_le_pow_right (by decide) (hD.trans hE)).trans hYZ
  have hq' : 3^(t*D) ≤ Z := (Nat.pow_le_pow_right (by decide)
    ((Nat.mul_le_mul ht hD).trans hE2)).trans hYZ
  have hp' : 2^r ≤ Z := (Nat.pow_le_pow_left (by decide : 2 ≤ 3) r).trans
    ((Nat.pow_le_pow_right (by decide) (hr.trans hE)).trans hYZ)
  have hq'' : 2^(D*r) ≤ Z := (Nat.pow_le_pow_left (by decide : 2 ≤ 3) (D*r)).trans
    ((Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul hD hr).trans hE2)).trans hYZ)
  have hl := localNumeric_bound a₃ w₃ t D d (t*D) (3^D) (3^(t*D)) Z
    (ha₃.trans (hCY.trans hYZ)) (hw₃.trans (hCY.trans hYZ)) (ht.trans (hHY.trans hYZ)) (hD.trans (hHY.trans hYZ))
    (hd.trans (hHY.trans hYZ)) hUZ hp hq'
  have hg := graphNumeric_bound a₂ w₂ D r ql Dl (D*r) (2^r) (2^(D*r)) Z
    (ha₂.trans (hCY.trans hYZ)) (hw₂.trans (hCY.trans hYZ)) (hD.trans (hHY.trans hYZ)) (hr.trans (hHY.trans hYZ))
    (hq.trans hWZ) (hDl.trans hWZ) hVZ hp' hq''
  have hZ : 1 ≤ (Z+1)^6 := Nat.one_le_pow _ _ (Nat.succ_pos Z)
  have hcoeff : 1000000000000*(f+g)+1 ≤ Y := hc.trans hCY
  have hsum : f*localNumeric a₃ w₃ t D d (t*D) (3^D) (3^(t*D))+
      g*graphNumeric a₂ w₂ D r ql Dl (D*r) (2^r) (2^(D*r))+1 ≤ Y*(Z+1)^6 := by
    calc
      _ ≤ f*(1000000000000*(Z+1)^6)+g*(1000000000000*(Z+1)^6)+(Z+1)^6 :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left f hl)
          (Nat.mul_le_mul_left g hg)) hZ
      _ = (1000000000000*(f+g)+1)*(Z+1)^6 := by ring
      _ ≤ _ := Nat.mul_le_mul_right ((Z+1)^6) hcoeff
  have hz1 : 1 ≤ Z := hYY.trans hYZ
  have hz2 : Z+1 ≤ 3*Z := (Nat.add_le_add_left hz1 Z).trans (by
    simpa only [two_mul] using Nat.mul_le_mul_right Z (by decide : 2 ≤ 3))
  have hz : Z+1 ≤ 3*Y*(W+1) := by
    simpa only [Z,Nat.mul_assoc] using hz2
  calc
    _ ≤ Y*(Z+1)^6 := hsum
    _ ≤ Y*(3*Y*(W+1))^6 := by gcongr
    _ = 3^6*(3^E)^7*(W+1)^6 := by dsimp [Y]; ring
    _ = envelope C H W := by
      rw [← pow_mul,← pow_add]
      unfold envelope exponent E
      congr 2
      ring

end SubexponentialSAT.SqrtLog.CodeSetupCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeSearchBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-degree bounds for the actual streamed sparse-code search commands.
The time comparison uses the original complete numerical search envelope;
workspace is bounded separately by ordinary input words and dimensions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets
open SparseCodeSearch CodeChecks

/-- Every candidate and every invalid two-bit word is charged. -/
theorem streamedCodeTime_le (A md wd callback : ℕ) :
    timeBudget md (boundary A md)
      (candidateBudget (boundary A md) md wd callback
        (4 ^ wd * (callback + 110 * wd + 36) + 3))
      (candidateSpace (boundary A md) md wd callback) ≤
      4000000 * (A + md + wd + callback + 1) * (4 ^ md * 4 ^ wd) := by
  let S := A + md + wd + callback + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hB : boundary A md ≤ 7 * S := by dsimp [boundary, S]; omega
  have hsum : boundary A md + md + wd + callback + 1 ≤ 8 * S := by
    dsimp [boundary, S]
    omega
  have hC := candidateSpace_le (boundary A md) md wd callback
  have hC' : candidateSpace (boundary A md) md wd callback ≤ 160000 * S := by omega
  have hx : 1 ≤ 4 ^ wd := Nat.one_le_pow _ _ (by decide)
  have hy : 1 ≤ 4 ^ md := Nat.one_le_pow _ _ (by decide)
  have hscan : callback + 110 * wd + 36 ≤ 147 * S := by dsimp [S]; omega
  have hsw : 4 ^ wd * (callback + 110 * wd + 36) + 3 ≤ 150 * S * 4 ^ wd := by
    have hmul := Nat.mul_le_mul_left (4 ^ wd) hscan
    have hpos : 1 ≤ S * 4 ^ wd := by nlinarith
    nlinarith
  have hT := candidateBudget_le (boundary A md) md wd callback
    (4 ^ wd * (callback + 110 * wd + 36) + 3)
  have hST : S ≤ S * 4 ^ wd := by nlinarith
  have hT' : candidateBudget (boundary A md) md wd callback
      (4 ^ wd * (callback + 110 * wd + 36) + 3) ≤ 158000 * S * 4 ^ wd := by
    nlinarith
  have hmd : md ≤ S := by dsimp [S]; omega
  have hbody : candidateBudget (boundary A md) md wd callback
      (4 ^ wd * (callback + 110 * wd + 36) + 3) +
      7 * (boundary A md + candidateSpace (boundary A md) md wd callback) +
      10 + 42 * md + 12 ≤ 1300000 * S * 4 ^ wd := by nlinarith
  have hmain := Nat.mul_le_mul_left (4 ^ md) hbody
  have htail : 3 + 15 * md + 4 * boundary A md + 17 ≤ 63 * S := by omega
  have hprod : S ≤ S * (4 ^ md * 4 ^ wd) := by
    have hp : 1 ≤ 4 ^ md * 4 ^ wd := by nlinarith
    nlinarith
  dsimp [timeBudget]
  change _ ≤ 4000000 * S * (4 ^ md * 4 ^ wd)
  nlinarith

/-- The retained code-search workspace contains no enumeration-domain factor. -/
theorem streamedCodeSpace_le (A md wd callback : ℕ) :
    spaceBudget md (boundary A md)
      (candidateSpace (boundary A md) md wd callback) ≤
      10000000 * (A + md + wd + callback + 1) := by
  let S := A + md + wd + callback + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hB : boundary A md ≤ 7 * S := by dsimp [boundary, S]; omega
  have hsum : boundary A md + md + wd + callback + 1 ≤ 8 * S := by
    dsimp [boundary, S]
    omega
  have hC := candidateSpace_le (boundary A md) md wd callback
  have hmd : md ≤ S := by dsimp [S]; omega
  have hm : max (56 * (boundary A md + candidateSpace (boundary A md) md wd callback) + 10)
      (48 * boundary A md + 7 * (6 * md + 1) + 4) ≤ 9000000 * S := by
    apply max_le <;> omega
  dsimp [spaceBudget]
  change _ ≤ 10000000 * S
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets
open SparseCodeSearch CodeChecks

/-- Actual local-search storage is quadratic in ordinary dimensions and words. -/
theorem localCodeSpace_polynomial (A t D d : ℕ) :
    localSpace A t D d ≤ 100000000000000 * (A + t + D + d + 1) ^ 2 := by
  have h := streamedCodeSpace_le A (t * D) D (OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d)
  let S := A + t + D + d + 1
  have ht : t ≤ S := by dsimp [S]; omega
  have hD : D ≤ S := by dsimp [S]; omega
  have hd : d ≤ S := by dsimp [S]; omega
  have hA : A ≤ S := by dsimp [S]; omega
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hp : S ≤ S ^ 2 := by nlinarith
  have hm : t * D ≤ S ^ 2 := by nlinarith [Nat.mul_le_mul ht hD]
  change _ ≤ 100000000000000 * S ^ 2
  simpa only [localSpace] using (show spaceBudget (t * D) (boundary A (t * D))
    (candidateSpace (boundary A (t * D)) (t * D) D
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d)) ≤
      100000000000000 * S ^ 2 by
        calc
          _ ≤ _ := h
          _ ≤ _ := by rw [local_budget]; nlinarith)

/-- Graph-word comparisons contribute only a fixed quadratic storage bound. -/
theorem graphCodeSpace_polynomial (A D r ql Dl : ℕ) :
    graphSpace A D r ql Dl ≤ 100000000000000 * (A + D + r + ql + Dl + 1) ^ 2 := by
  have h := streamedCodeSpace_le A (D * r) r
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl)
  let S := A + D + r + ql + Dl + 1
  have hD : D ≤ S := by dsimp [S]; omega
  have hr : r ≤ S := by dsimp [S]; omega
  have hq : ql ≤ S := by dsimp [S]; omega
  have hd : Dl ≤ S := by dsimp [S]; omega
  have hA : A ≤ S := by dsimp [S]; omega
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hp : S ≤ S ^ 2 := by nlinarith
  have hm : D * r ≤ S ^ 2 := by nlinarith [Nat.mul_le_mul hD hr]
  have hs : 2 * (ql + Dl + D) + 4 ≤ 6 * S := by dsimp [S]; omega
  have hsq : (2 * (ql + Dl + D) + 4) ^ 2 ≤ 36 * S ^ 2 := by nlinarith
  change _ ≤ 100000000000000 * S ^ 2
  simpa only [graphSpace] using (show spaceBudget (D * r) (boundary A (D * r))
    (candidateSpace (boundary A (D * r)) (D * r) r
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl)) ≤
      100000000000000 * S ^ 2 by
        calc
          _ ≤ _ := h
          _ ≤ _ := by rw [graph_budget]; nlinarith)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets
open SparseCodeSearch CodeChecks
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost

private theorem localNumeric_lower (a w t D d U P Q : ℕ) (hP : 1 ≤ P) (hQ : 1 ≤ Q) :
    U + D + localCallback U t D d + 1 ≤ 2 * localNumeric a w t D d U P Q ∧
    Q * P ≤ localNumeric a w t D d U P Q := by
  let c := localCallback U t D d
  have hc : U + D + 1 ≤ c := by dsimp [c, localCallback, localWord, matrix2]; omega
  have hi : P * (c + 1) ≤ localCandidate U t D d P := by
    dsimp [localCandidate, localVerifier, c]
    nlinarith
  have ho : Q * localCandidate U t D d P ≤ localNumeric a w t D d U P Q := by
    unfold localNumeric
    nlinarith
  have hb : Q * P * (c + 1) ≤ localNumeric a w t D d U P Q := by
    have hm := Nat.mul_le_mul_left Q hi
    nlinarith
  have hpq : 1 ≤ Q * P := by nlinarith
  have hcs : c + 1 ≤ Q * P * (c + 1) := by nlinarith
  have hd : Q * P ≤ Q * P * (c + 1) := by nlinarith
  constructor
  · change U + D + c + 1 ≤ _
    omega
  · omega

private theorem graphNumeric_lower (a w D r ql Dl U P Q : ℕ)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) :
    U + r + graphCallback U D r ql Dl + 1 ≤ 2 * graphNumeric a w D r ql Dl U P Q ∧
    Q * P ≤ graphNumeric a w D r ql Dl U P Q := by
  let c := graphCallback U D r ql Dl
  have hc : U + r + 1 ≤ c := by dsimp [c, graphCallback, graphWord, matrix2]; omega
  have hi : P * (c + 1) ≤ graphCandidate U D r ql Dl P := by
    dsimp [graphCandidate, graphVerifier, c]
    nlinarith
  have ho : Q * graphCandidate U D r ql Dl P ≤ graphNumeric a w D r ql Dl U P Q := by
    unfold graphNumeric
    nlinarith
  have hb : Q * P * (c + 1) ≤ graphNumeric a w D r ql Dl U P Q := by
    have hm := Nat.mul_le_mul_left Q hi
    nlinarith
  have hpq : 1 ≤ Q * P := by nlinarith
  have hcs : c + 1 ≤ Q * P * (c + 1) := by nlinarith
  have hd : Q * P ≤ Q * P * (c + 1) := by nlinarith
  constructor
  · change U + r + c + 1 ≤ _
    omega
  · omega

private theorem localCallback_eq (t D d : ℕ) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d = localCallback (t * D) t D d := by
  rw [local_budget]
  unfold localCallback localWord matrix2
  ring

private theorem graphCallback_eq (D r ql Dl : ℕ) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl =
      graphCallback (D * r) D r ql Dl := by
  rw [graph_budget]
  unfold graphCallback graphWord matrix2
  ring

/-- The entire new local search is dominated by a fixed cubic power of the
original explicit worst-case budget, not by the old successful execution time. -/
theorem localCodeTime_le_numeric (A a w t D d : ℕ) :
    localTime A t D d ≤
      8000000 * (A + localNumeric a w t D d (t * D) (3 ^ D) (3 ^ (t * D)) + 1) ^ 3 := by
  let N := localNumeric a w t D d (t * D) (3 ^ D) (3 ^ (t * D))
  have hl := localNumeric_lower a w t D d (t * D) (3 ^ D) (3 ^ (t * D))
    (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by decide))
  have hs : A + t * D + D + OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d + 1 ≤
      2 * (A + N + 1) := by rw [localCallback_eq]; dsimp [N]; omega
  have hd : 4 ^ (t * D) * 4 ^ D ≤ N ^ 2 :=
    (local_attempts_le_square t D).trans (Nat.pow_le_pow_left hl.2 2)
  calc
    _ ≤ 4000000 * (A + t * D + D + OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d + 1) *
        (4 ^ (t * D) * 4 ^ D) := streamedCodeTime_le A (t * D) D _
    _ ≤ 4000000 * (2 * (A + N + 1)) * (A + N + 1) ^ 2 := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 4000000 hs)
        (hd.trans (Nat.pow_le_pow_left (by omega) 2))
    _ = _ := by dsimp [N]; ring

/-- Both graph tuple domains are charged, including all rejected candidates. -/
theorem graphCodeTime_le_numeric (A a w D r ql Dl : ℕ) :
    graphTime A D r ql Dl ≤
      8000000 * (A + graphNumeric a w D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r)) + 1) ^ 3 := by
  let N := graphNumeric a w D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r))
  have hl := graphNumeric_lower a w D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r))
    (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by decide))
  have hs : A + D * r + r + OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl + 1 ≤
      2 * (A + N + 1) := by rw [graphCallback_eq]; dsimp [N]; omega
  have hd : 4 ^ (D * r) * 4 ^ r ≤ N ^ 2 := by
    rw [graph_attempts_eq_square]
    exact Nat.pow_le_pow_left hl.2 2
  calc
    _ ≤ 4000000 * (A + D * r + r + OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl + 1) *
        (4 ^ (D * r) * 4 ^ r) := streamedCodeTime_le A (D * r) r _
    _ ≤ 4000000 * (2 * (A + N + 1)) * (A + N + 1) ^ 2 := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 4000000 hs)
        (hd.trans (Nat.pow_le_pow_left (by omega) 2))
    _ = _ := by dsimp [N]; ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeSearchNativeBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Numerical bounds for the actual graph-then-local code stage, including
all physical routing, saved outputs, and reused-bank cleanup. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
open SqrtLog SparseCodeSearch CodeSearchBudgets

/-- Unary entry metadata already pays for both retained matrix dimensions. -/
theorem searchBoundary_le (A m B : ℕ)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A) :
    NativeCode.graphBoundary A m B ≤ 7 * A + 1 ∧
    NativeCode.searchBoundary A m B ≤ 13 * A + 2 := by
  simp only [NativeCode.graphBoundary, NativeCode.searchBoundary, boundary]
  omega

/-- The actual graph/local sequence has a quadratic source-prefix bound
when its exact input metadata words fit in the supplied input bound. -/
theorem searchesSpace_le (A m B ql Dl : ℕ) (hA : 1 ≤ A)
    (hD : SparseCode.degree m B ≤ A)
    (ht : SparseCode.localRows m B ≤ A)
    (hd : SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ A)
    (hr : SparseCode.dimension m B ≤ A) (hq : ql ≤ A) (hDl : Dl ≤ A)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A) :
    NativeCode.searchesSpace A m B ql Dl ≤ 20000000000000000 * A ^ 2 := by
  have hb := searchBoundary_le A m B hg hl
  have hgb : NativeCode.graphBoundary A m B ≤ 8 * A := by omega
  have hsb : NativeCode.searchBoundary A m B ≤ 15 * A := by omega
  have hgg := graphCodeSpace_polynomial A (SparseCode.degree m B)
    (SparseCode.dimension m B) ql Dl
  have hll := localCodeSpace_polynomial (NativeCode.graphBoundary A m B)
    (SparseCode.localRows m B) (SparseCode.degree m B)
    (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1)
  have hgs : A + SparseCode.degree m B + SparseCode.dimension m B + ql + Dl + 1 ≤ 6 * A := by omega
  have hls : NativeCode.graphBoundary A m B + SparseCode.localRows m B +
      SparseCode.degree m B + (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1) + 1 ≤
      12 * A := by omega
  have hgg' := hgg.trans (Nat.mul_le_mul_left 100000000000000 (Nat.pow_le_pow_left hgs 2))
  have hll' := hll.trans (Nat.mul_le_mul_left 100000000000000 (Nat.pow_le_pow_left hls 2))
  have hp : A ≤ A ^ 2 := by nlinarith only [hA]
  have hgg'' : graphSpace A (SparseCode.degree m B) (SparseCode.dimension m B) ql Dl ≤
      20000000000000000 * A ^ 2 := by nlinarith only [hgg']
  have hll'' : localSpace (NativeCode.graphBoundary A m B) (SparseCode.localRows m B)
      (SparseCode.degree m B) (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1) ≤
      20000000000000000 * A ^ 2 := by nlinarith only [hll']
  have hbA : A ≤ 20000000000000000 * A ^ 2 := by nlinarith only [hp]
  have hbG : NativeCode.graphBoundary A m B ≤ 20000000000000000 * A ^ 2 := by nlinarith only [hgb, hp]
  have hbL : NativeCode.searchBoundary A m B ≤ 20000000000000000 * A ^ 2 := by nlinarith only [hsb, hp]
  unfold NativeCode.searchesSpace NativeCode.graphStageSpace NativeCode.localStageSpace
  exact max_le (max_le hbA (max_le (max_le hgg'' hbA) hbG))
    (max_le hbG (max_le (max_le hll'' hbG) hbL))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
open SqrtLog SparseCodeSearch CodeSearchBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost

/-- All actual routes, searches, retained outputs and clearing fit a fixed
cubic power of the original explicit numerical envelope. -/
theorem searchesTime_le_envelope (A m B ql Dl H W : ℕ)
    (ht : SparseCode.localRows m B ≤ H) (hD : SparseCode.degree m B ≤ H)
    (hd : SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H)
    (hr : SparseCode.dimension m B ≤ H) (hq : ql ≤ W) (hDl : Dl ≤ W)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A) :
    NativeCode.searchesTime A m B ql Dl ≤
      5000000000 * (A + envelope 3000000000000 H W + 1) ^ 3 := by
  let t := SparseCode.localRows m B
  let D := SparseCode.degree m B
  let d := D / (100 * B * SparseCode.logSize m) + 1
  let r := SparseCode.dimension m B
  let E := envelope 3000000000000 H W
  let X := A + E + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hA : A ≤ X := by dsimp [X]; omega
  have hX3 : X ≤ X ^ 3 := by nlinarith [Nat.one_le_pow 2 X hX]
  have he := combinedNumeric_bound 0 0 0 0 t D d r ql Dl 1 1 H W
    3000000000000 ht hD hd hr hq hDl (by norm_num)
  simp only [one_mul] at he
  have hle : localNumeric 0 0 t D d (t * D) (3 ^ D) (3 ^ (t * D)) ≤ E := by dsimp [E]; omega
  have hge : graphNumeric 0 0 D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r)) ≤ E := by dsimp [E]; omega
  have hb := searchBoundary_le A m B hg hl
  have hgb : NativeCode.graphBoundary A m B ≤ 8 * X := by omega
  have hL : NativeCode.graphBoundary A m B +
      localNumeric 0 0 t D d (t * D) (3 ^ D) (3 ^ (t * D)) + 1 ≤ 8 * X := by
    dsimp [X]
    omega
  have hG : A + graphNumeric 0 0 D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r)) + 1 ≤ X := by
    dsimp [X]
    omega
  have hlt := (localCodeTime_le_numeric (NativeCode.graphBoundary A m B) 0 0 t D d).trans
    (Nat.mul_le_mul_left 8000000 (Nat.pow_le_pow_left hL 3))
  have hgt := (graphCodeTime_le_numeric A 0 0 D r ql Dl).trans
    (Nat.mul_le_mul_left 8000000 (Nat.pow_le_pow_left hG 3))
  have hbound : boundary (NativeCode.graphBoundary A m B) (t * D) ≤ 15 * X := by
    change NativeCode.searchBoundary A m B ≤ _
    omega
  change _ ≤ 5000000000 * X ^ 3
  unfold NativeCode.searchesTime NativeCode.graphStageTime NativeCode.localStageTime
  change 5 * (9 * A + 8) + 3 +
      (graphTime A D r ql Dl + 1 + (105 * NativeCode.graphBoundary A m B + 155)) +
      (4 * (9 * NativeCode.graphBoundary A m B + 8) + 3 +
        (localTime (NativeCode.graphBoundary A m B) t D d + 1 +
          (105 * boundary (NativeCode.graphBoundary A m B) (t * D) + 155))) ≤ _
  nlinarith only [hlt, hgt, hX, hX3, hA, hgb, hbound]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual sparse-row serialization and its same-run source resource bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- Actual complete code-row production, after the graph-order inequality
has bounded its only exponential domain by the clause count. -/
theorem codeRows_explicitCost_le (r D t b Ld Lm S : ℕ) (hS : 1 ≤ S)
    (hr : r ≤ S) (hD : D ≤ S) (ht : t ≤ S) (hb : b ≤ S)
    (hdword : Ld ≤ S) (hmword : Lm ≤ S) (hvertices : 2 ^ r ≤ 2 * S) :
    SqrtLog.CodeRowsProgram.explicitCost r D t b Ld Lm ≤ 1000000 * S ^ 5 := by
  have hrow : SqrtLog.CodeRowsProgram.explicitRowCost r D b Ld Lm ≤ 200000 * S ^ 3 := by
    have h1 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
    have h2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
    have h0 : 1 ≤ S ^ 3 := one_le_pow₀ hS
    calc
      _ ≤ 7 * S + 35 * (S * S) + S * (2000 * (5 * S + 4) ^ 2 + 2) +
          2 * S + 4 * (S * S) + 23 := by
        unfold SqrtLog.CodeRowsProgram.explicitRowCost
        gcongr
        omega
      _ ≤ _ := by nlinarith
  have h1 : S ≤ S ^ 5 := Nat.le_self_pow (by decide) _
  have h2 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S ^ 3 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h0 : 1 ≤ S ^ 5 := one_le_pow₀ hS
  calc
    _ ≤ 2 * S * (2 * (35 * (S * S) + 7 * S + S * (200000 * S ^ 3 + 2) + 13) +
        8 * S + 10) + 13 * S + 18 := by
      unfold SqrtLog.CodeRowsProgram.explicitCost
      gcongr
    _ ≤ _ := by nlinarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

/-- Every numeric code dimension is already represented by a physical
unary word at the metadata boundary; its value is bounded by that word cap. -/
theorem metadata_value_bound {m occurrence A : ℕ} (a : Data)
    (hmeta : Metadata m occurrence a) (ha : ∀ i, (a.stacks i).length ≤ A)
    (j : Fin 7) : CodeParametersProgram.parameterValues m occurrence j ≤ A := by
  have h := ha (unaryMetadataPort j)
  rw [hmeta.unary j, List.length_replicate] at h
  exact h

/-- The stored vertex word is nonempty, so a true metadata boundary has a
positive physical bound even in a zero-dimensional code. -/
theorem metadata_bound_pos {m occurrence A : ℕ} (a : Data)
    (hmeta : Metadata m occurrence a) (ha : ∀ i, (a.stacks i).length ≤ A) : 1 ≤ A := by
  have h := metadata_value_bound a hmeta ha 6
  change 2 ^ SparseCode.dimension m occurrence ≤ A at h
  exact (Nat.one_le_pow _ _ (by decide)).trans h

theorem serializerTime_polynomial {r D t W S : ℕ} (dword mword width : List Bool)
    (hS : 1 ≤ S) (hW : W ≤ S) (hr : r ≤ S) (hD : D ≤ S) (ht : t ≤ S)
    (hdword : dword.length ≤ S) (hmword : mword.length ≤ S) (hwidth : width.length ≤ S)
    (hvertices : 2^r ≤ 2*S) :
    W + serializerTime r D t W dword mword width ≤ 10000030000 * S^5 := by
  have hcost := SparseCodeProgram.codeRows_explicitCost_le r D t width.length
    dword.length mword.length S hS hr hD ht hwidth hdword hmword hvertices
  have hpow : S ≤ S^5 := Nat.le_self_pow (by decide) _
  have hpos : 1 ≤ S^5 := one_le_pow₀ hS
  unfold serializerTime
  nlinarith


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeAssemblyBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeAssemblyBudgets
open SqrtLog NativeCodeAssembly CodeSearchNativeBudgets

/-- The serializer is polynomial in the physical metadata boundary, including
its unary vertex word and both complete retained code matrices. -/
theorem afterBoundary_le (A m B : ℕ) (dword mword width : List Bool)
    (hA : 1 ≤ A) (hr : SparseCode.dimension m B ≤ A)
    (hD : SparseCode.degree m B ≤ A) (ht : SparseCode.localRows m B ≤ A)
    (hdword : dword.length ≤ A) (hmword : mword.length ≤ A)
    (hwidth : width.length ≤ A) (hvertices : 2 ^ SparseCode.dimension m B ≤ A)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A) :
    afterBoundary A m B dword mword width ≤ 10000000000000000 * A ^ 5 := by
  have hb := (searchBoundary_le A m B hg hl).2
  have h := serializerTime_polynomial (r := SparseCode.dimension m B)
    (D := SparseCode.degree m B) (t := SparseCode.localRows m B)
    (W := NativeCode.searchBoundary A m B) (S := 15 * A) dword mword width
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  change afterBoundary A m B dword mword width ≤ _ at h
  nlinarith only [h]

open SqrtLog.CodeSetupCost in
/-- Both full searches and serialization fit one fixed fifth power of the
original explicit code envelope and the physical metadata size. -/
theorem afterTime_le_envelope (A m B qlen H W : ℕ) (dword mword width : List Bool)
    (hA : 1 ≤ A) (hrA : SparseCode.dimension m B ≤ A)
    (hDA : SparseCode.degree m B ≤ A) (htA : SparseCode.localRows m B ≤ A)
    (hdword : dword.length ≤ A) (hmword : mword.length ≤ A)
    (hwidth : width.length ≤ A) (hvertices : 2 ^ SparseCode.dimension m B ≤ A)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A)
    (ht : SparseCode.localRows m B ≤ H) (hD : SparseCode.degree m B ≤ H)
    (hd : SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H)
    (hr : SparseCode.dimension m B ≤ H) (hq : qlen ≤ W) (hDl : dword.length ≤ W) :
    afterTime A m B qlen dword mword width ≤
      20000000000000000 * (A + envelope 3000000000000 H W + 1) ^ 5 := by
  have hs := searchesTime_le_envelope A m B qlen dword.length H W ht hD hd hr hq hDl hg hl
  have hb := afterBoundary_le A m B dword mword width hA hrA hDA htA
    hdword hmword hwidth hvertices hg hl
  let X := A + envelope 3000000000000 H W + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hAX : A ≤ X := by dsimp [X]; omega
  have hp : X ^ 3 ≤ X ^ 5 := Nat.pow_le_pow_right hX (by decide)
  have hpA := Nat.pow_le_pow_left hAX 5
  change _ ≤ 20000000000000000 * X ^ 5
  unfold afterTime
  unfold afterBoundary at hb
  change NativeCode.searchesTime A m B qlen dword.length ≤ 5000000000 * X ^ 3 at hs
  nlinarith only [hs, hb, hp, hpA]

open SqrtLog.Statement
open Filter
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeAssemblyBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_LeafPreparationBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Numerical resources of the actual full leaf-preparation command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
open SqrtLog SqrtLog.LeafOuterProgram NativeLeafPreparation NativeCodeAssembly
open CodeAssemblyBudgets CodeSearchNativeBudgets

/-- The saved initial words and the produced metadata bound the actual
search-and-serialization phase without any search-count factor in space. -/
theorem metadata_code_bounds {m B A : ℕ} (prepared : Data)
    (hmeta : Metadata m B prepared) (ha : ∀ i, (prepared.stacks i).length ≤ A)
    (mword width : List Bool) (hmword : mword.length ≤ A) (hwidth : width.length ≤ A) :
    afterBoundary A m B (prepared.stacks 801) mword width ≤ 10000000000000000 * A ^ 5 ∧
    afterSpace A m B (prepared.stacks 800).length (prepared.stacks 801) mword width ≤
      20000000000000000 * A ^ 5 := by
  have hA := metadata_bound_pos prepared hmeta ha
  have hD := metadata_value_bound prepared hmeta ha 0
  have ht := metadata_value_bound prepared hmeta ha 1
  have hl := metadata_value_bound prepared hmeta ha 2
  have hd := metadata_value_bound prepared hmeta ha 3
  have hr := metadata_value_bound prepared hmeta ha 4
  have hg := metadata_value_bound prepared hmeta ha 5
  have hv := metadata_value_bound prepared hmeta ha 6
  change SparseCode.degree m B ≤ A at hD
  change SparseCode.localRows m B ≤ A at ht
  change SparseCode.localRows m B * SparseCode.degree m B ≤ A at hl
  change SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ A at hd
  change SparseCode.dimension m B ≤ A at hr
  change SparseCode.dimension m B * SparseCode.degree m B ≤ A at hg
  rw [Nat.mul_comm] at hg
  change 2 ^ SparseCode.dimension m B ≤ A at hv
  have hs := searchesSpace_le A m B (prepared.stacks 800).length (prepared.stacks 801).length
    hA hD ht hd hr (ha 800) (ha 801) hg hl
  have hb := afterBoundary_le A m B (prepared.stacks 801) mword width
    hA hr hD ht (ha 801) hmword hwidth hv hg hl
  have hp : A ^ 2 ≤ A ^ 5 := Nat.pow_le_pow_right hA (by decide)
  refine ⟨hb, ?_⟩
  unfold afterSpace
  exact max_le (hs.trans (Nat.mul_le_mul_left _ hp)) (by omega)

/-- The paid final clearing and zero-candidate constructor have fixed
bilinear cost in the actual depth and current physical word cap. -/
theorem finishTime_le (depth R : ℕ) :
    R + finishTime depth R ≤ 1000 * (depth + 1) * (R + 1) := by
  unfold finishTime
  nlinarith

open SqrtLog.CodeSetupCost in
/-- The paid whole continuation is a fixed sixth power of the original
complete code envelope plus the actual physical boundary and scalar depth. -/
theorem continuationTime_le_envelope_oai (m B L H wordCap : ℕ) (a prepared : Data)
    (ha : ∀ i, (a.stacks i).length ≤ L) (hmeta : Metadata m B prepared)
    (hp : ∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
      (a.stacks 782).length (a.stacks 786).length)
    (ht : SparseCode.localRows m B ≤ H) (hD : SparseCode.degree m B ≤ H)
    (hd : SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H)
    (hr : SparseCode.dimension m B ≤ H)
    (hq : (prepared.stacks 800).length ≤ wordCap)
    (hDl : (prepared.stacks 801).length ≤ wordCap) :
    let A := L + NativeLeafSetup.parameterTime m B L
      (a.stacks 782).length (a.stacks 786).length
    continuationTime m B L a prepared ≤
      30000000000000000000 *
        (A + SparseCode.distanceDenom m B + envelope 3000000000000 H wordCap + 1) ^ 6 := by
  intro A
  have hLA : L ≤ A := by dsimp [A]; omega
  have hA := metadata_bound_pos prepared hmeta hp
  have hDA := metadata_value_bound prepared hmeta hp 0
  have htA := metadata_value_bound prepared hmeta hp 1
  have hl := metadata_value_bound prepared hmeta hp 2
  have hrA := metadata_value_bound prepared hmeta hp 4
  have hg := metadata_value_bound prepared hmeta hp 5
  have hv := metadata_value_bound prepared hmeta hp 6
  change SparseCode.degree m B ≤ A at hDA
  change SparseCode.localRows m B ≤ A at htA
  change SparseCode.localRows m B * SparseCode.degree m B ≤ A at hl
  change SparseCode.dimension m B ≤ A at hrA
  change SparseCode.dimension m B * SparseCode.degree m B ≤ A at hg
  rw [Nat.mul_comm] at hg
  change 2 ^ SparseCode.dimension m B ≤ A at hv
  have hmword : (a.stacks 782).length ≤ A := (ha 782).trans hLA
  have hwidth : (a.stacks 768).length ≤ A := (ha 768).trans hLA
  have htime := afterTime_le_envelope A m B (prepared.stacks 800).length H wordCap
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768) hA hrA hDA htA
    (hp 801) hmword hwidth hv hg hl ht hD hd hr hq hDl
  have hb := (metadata_code_bounds prepared hmeta hp (a.stacks 782) (a.stacks 768)
    hmword hwidth).1
  let R := afterBoundary A m B (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  let X := A + SparseCode.distanceDenom m B + envelope 3000000000000 H wordCap + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h56 : X ^ 5 ≤ X ^ 6 := Nat.pow_le_pow_right hX (by decide)
  have h16 : X ≤ X ^ 6 := Nat.le_self_pow (by decide) X
  have h1 : 1 ≤ X ^ 5 := Nat.one_le_pow' _ _
  have hP : NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length ≤ X := by
    dsimp [X, A]
    omega
  have hdepth : SparseCode.distanceDenom m B + 1 ≤ X := by dsimp [X]; omega
  have hR : R ≤ 10000000000000000 * X ^ 5 := hb.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [X]; omega) 5))
  have hR1 : R + 1 ≤ 10000000000000001 * X ^ 5 := by omega
  have hf := (finishTime_le (SparseCode.distanceDenom m B) R).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 1000 hdepth) hR1)
  have htime' := htime.trans (Nat.mul_le_mul_left 20000000000000000
    (Nat.pow_le_pow_left (show A + envelope 3000000000000 H wordCap + 1 ≤ X by
      dsimp [X]; omega) 5))
  change _ ≤ 30000000000000000000 * X ^ 6
  unfold continuationTime
  change NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length +
    afterTime A m B (prepared.stacks 800).length (prepared.stacks 801)
      (a.stacks 782) (a.stacks 768) + finishTime (SparseCode.distanceDenom m B) R ≤ _
  nlinarith only [hP, htime', hf, h56, h16]

open SqrtLog.CodeSetupCost

open Filter SqrtLog.Asymptotic SqrtLog.Statement
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.continuationTime_le_envelope_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.continuationTime_le_envelope_oai
