-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:11:55.487956+00:00
-- url     : https://prove2.me/submissions/00001e61-c1e4-4af9-aec7-869223eb7629

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S172
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafSetup_canonicalParameterTime_polynomial

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DyadicWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A positive dyadic width for bounded tuple enumeration, including zero. -/

namespace SubexponentialSAT.DyadicWidth

theorem width_le_succ (m : ℕ) : width m ≤ m + 1 := by
  by_cases hm : m = 0
  · subst m
    norm_num [width]
  · have h := Nat.log_lt_self 2 hm
    unfold width
    omega

end SubexponentialSAT.DyadicWidth

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem degree_le (m B : ℕ) : degree m B ≤ m := min_le_left _ _

theorem eight_mul_le_degreeBound (m : ℕ) {B : ℕ} (hB : 0 < B) :
    8 * B ≤ degreeBound m B := by
  have hL : 1 ≤ logSize m := logSize_pos m
  have hq : B ≤ gapDenom m B := by unfold gapDenom; nlinarith
  have hqpos := gapDenom_pos m hB
  have hsq : gapDenom m B ≤ gapDenom m B ^ 2 := by nlinarith
  unfold degreeBound
  nlinarith

theorem dimensionFor_le (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : m ≤ D * 2 ^ r) : dimensionFor m D ≤ r := by
  simp only [dimensionFor, dite_eq_left hD]
  exact Nat.find_min' (exists_dimension m hD) hr

theorem dimensionFor_min (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : r < dimensionFor m D) : D * 2 ^ r < m := by
  simp only [dimensionFor, dite_eq_left hD] at hr
  exact Nat.lt_of_not_ge (Nat.find_min (exists_dimension m hD) hr)

theorem dimensionFor_self {m : ℕ} (hm : 0 < m) : dimensionFor m m = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact dimensionFor_le m hm (by simp)

theorem dimensionFor_edge_upper {m D : ℕ} (hm : 0 < m) (hD : 0 < D) (hDm : D ≤ m) :
    D * 2 ^ dimensionFor m D < 2 * m := by
  cases hr : dimensionFor m D with
  | zero => simp only [pow_zero, mul_one]; omega
  | succ r =>
    have hprev : D * 2 ^ r < m := dimensionFor_min m hD (by omega)
    simp only [pow_succ]
    nlinarith

theorem graph_edge_upper {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    2 ^ dimension m B * degree m B < 2 * m := by
  simpa [dimension, Nat.mul_comm] using
    dimensionFor_edge_upper hm (degree_pos hm hB) (degree_le m B)

theorem dimension_zero_of_small {m B : ℕ} (hm : 0 < m)
    (h : m ≤ degreeBound m B) : dimension m B = 0 := by
  simp [dimension, degree, min_eq_left h, dimensionFor_self hm]

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem localRows_upper (m B : ℕ) :
    8 * B * localRows m B ≤ degree m B + 8 * B := by
  have hh := Nat.div_mul_le_self (degree m B) (8 * B)
  unfold localRows
  nlinarith

theorem totalRows_le {n m B : ℕ} (hn : 0 < n) (hm : 0 < m) (hB : 0 < B)
    (hmb : m ≤ n * B) : totalRows m B ≤ 3 * n := by
  by_cases hlarge : degreeBound m B ≤ m
  · have hd : degree m B = degreeBound m B := min_eq_right hlarge
    have hbudget : 4 * B * localRows m B ≤ degree m B := by
      have htop := localRows_upper m B
      have hbig := eight_mul_le_degreeBound m hB
      rw [← hd] at hbig
      nlinarith
    have hedge := graph_edge_upper hm hB
    have hrows : totalRows m B * (2 * B) < n * (2 * B) := by
      calc
        _ = 2 ^ dimension m B * (4 * B * localRows m B) := by
          unfold totalRows
          ring
        _ ≤ 2 ^ dimension m B * degree m B := Nat.mul_le_mul_left _ hbudget
        _ < 2 * m := hedge
        _ ≤ n * (2 * B) := by nlinarith
    have : totalRows m B < n := Nat.lt_of_mul_lt_mul_right hrows
    omega
  · have hd : degree m B = m := min_eq_left (by omega)
    have hr : dimension m B = 0 := dimension_zero_of_small hm (by omega)
    have htop := localRows_upper m B
    rw [hd] at htop
    have hh : (8 * localRows m B) * B ≤ (n + 8) * B := by nlinarith
    have hrows : 8 * localRows m B ≤ n + 8 :=
      le_of_mul_le_mul_right hh hB
    simp only [totalRows, hr, pow_zero, mul_one]
    omega

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
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

/-- Space and retained output of preparation are bounded together by one
fixed sixth-degree polynomial. The exact depth is charged by value because
its zero candidate is physically materialized. -/
theorem continuation_bounds (m B L : ℕ) (a prepared : Data)
    (ha : ∀ i, (a.stacks i).length ≤ L) (hmeta : Metadata m B prepared)
    (hp : ∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
      (a.stacks 782).length (a.stacks 786).length) :
    let A := L + NativeLeafSetup.parameterTime m B L
      (a.stacks 782).length (a.stacks 786).length
    let Z := A + m + SparseCode.distanceDenom m B + 1
    max (L + 1) (continuationSpace m B L a prepared) ≤
      20000000000000000000 * Z ^ 6 ∧
    retainedBound m B L a prepared ≤ 20000000000000000000 * Z ^ 6 := by
  intro A Z
  have hLA : L ≤ A := by dsimp [A]; omega
  have hc := metadata_code_bounds prepared hmeta hp (a.stacks 782) (a.stacks 768)
    ((ha 782).trans hLA) ((ha 768).trans hLA)
  let R := afterBoundary A m B (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  have hR : R ≤ 10000000000000000 * Z ^ 5 := hc.1.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [Z]; omega) 5))
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have hA : A + 1 ≤ Z := by dsimp [Z]; omega
  have hm : m ≤ Z := by dsimp [Z]; omega
  have hd : SparseCode.distanceDenom m B + 1 ≤ Z := by dsimp [Z]; omega
  have h56 : Z ^ 5 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by decide)
  have h16 : Z ≤ Z ^ 6 := Nat.le_self_pow (by decide) Z
  have h26 : Z ^ 2 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : 1 ≤ Z ^ 5 := Nat.one_le_pow' _ _
  have hR1 : R + 1 ≤ 10000000000000001 * Z ^ 5 := by omega
  have hf := (finishTime_le (SparseCode.distanceDenom m B) R).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 1000 hd) hR1)
  have hf' : R + finishTime (SparseCode.distanceDenom m B) R ≤
      20000000000000000000 * Z ^ 6 := by nlinarith only [hf]
  have hspace : afterSpace A m B (prepared.stacks 800).length
      (prepared.stacks 801) (a.stacks 782) (a.stacks 768) ≤
        20000000000000000000 * Z ^ 6 := by
    have h := hc.2.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (show A ≤ Z by omega) 5))
    nlinarith only [h, h56]
  have hlinear : A + 1 ≤ 20000000000000000000 * Z ^ 6 := by nlinarith only [hA, h16]
  have hw : HashCandidates.digitWidth m ≤ 3 * m + 1 := DyadicWidth.width_le_succ _
  have hw' : HashCandidates.digitWidth m ≤ 4 * Z := by omega
  have hprod := Nat.mul_le_mul (show SparseCode.distanceDenom m B ≤ Z by omega) hw'
  have hretained : 2 * (SparseCode.distanceDenom m B * HashCandidates.digitWidth m) + 3 ≤
      20000000000000000000 * Z ^ 6 := by nlinarith only [hprod, h26, hZ, h16]
  constructor
  · change max (L + 1) (max (max (A + 1) _) (R + finishTime _ R)) ≤ _
    exact max_le (by omega) (max_le (max_le hlinear hspace) hf')
  · change max R _ ≤ _
    exact max_le (by nlinarith only [hR, h56]) hretained

/-- Startup, metadata production, both searches, serialization, final setup
and the retained initial history share one ordinary input-polynomial space
bound. Constants and degree are fixed before all runtime inputs. -/
theorem full_space_polynomial :
    ∃ C degree : ℕ, ∀ n m B W : ℕ, 0 < m → 0 < B →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (L + 1) (continuationSpace m B L a prepared) ≤
        C * (n + m + W + SparseCode.distanceDenom m B + 16) ^ degree ∧
      retainedBound m B L a prepared ≤
        C * (n + m + W + SparseCode.distanceDenom m B + 16) ^ degree := by
  obtain ⟨C, degree, hparameter⟩ := NativeLeafSetup.canonicalParameterTime_polynomial
  refine ⟨20000000000000000000 * (C + 1) ^ 6, (degree + 1) * 6, ?_⟩
  intro n m B W hm hB L a prepared ha hmeta hp
  let A := L + NativeLeafSetup.parameterTime m B L
    (a.stacks 782).length (a.stacks 786).length
  let X := n + m + W + SparseCode.distanceDenom m B + 16
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hA : A + 1 ≤ C * X ^ degree :=
    (hparameter n m B W _ _ hm hB (ha 782) (ha 786)).trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by dsimp [X]; omega) degree))
  have hexp : X ^ degree ≤ X ^ (degree + 1) := Nat.pow_le_pow_right hX (by omega)
  have hlinear : X ≤ X ^ (degree + 1) := by
    simpa using Nat.pow_le_pow_right hX (by omega : 1 ≤ degree + 1)
  have hZ : A + m + SparseCode.distanceDenom m B + 1 ≤ (C + 1) * X ^ (degree + 1) := by
    have h := hA.trans (Nat.mul_le_mul_left C hexp)
    have hrest : m + SparseCode.distanceDenom m B ≤ X := by dsimp [X]; omega
    nlinarith only [h, hlinear, hrest]
  have hc := continuation_bounds m B L a prepared ha hmeta hp
  have hbound := Nat.mul_le_mul_left 20000000000000000000 (Nat.pow_le_pow_left hZ 6)
  have heq : 20000000000000000000 * ((C + 1) * X ^ (degree + 1)) ^ 6 =
      (20000000000000000000 * (C + 1) ^ 6) * X ^ ((degree + 1) * 6) := by
    rw [mul_pow, ← pow_mul, Nat.mul_assoc]
  rw [heq] at hbound
  exact ⟨hc.1.trans hbound, hc.2.trans hbound⟩

/-- The physically expanded selector depth is polynomial in its actual
numeric parameters; its binary word length alone would not suffice. -/
theorem distanceDenom_polynomial (m B : ℕ) :
    SparseCode.distanceDenom m B ≤ 20000 * (B + m + 1) ^ 4 := by
  have hl : SparseCode.logSize m ≤ m + 1 := by
    unfold SparseCode.logSize
    exact Nat.add_le_add_right (Nat.log_le_self 2 m) 1
  have hB : B ≤ B + m + 1 := by omega
  have hlog : SparseCode.logSize m ≤ B + m + 1 := by omega
  have h := Nat.mul_le_mul (Nat.pow_le_pow_left hB 2) (Nat.pow_le_pow_left hlog 2)
  unfold SparseCode.distanceDenom
  nlinarith only [h]

/-- Eliminating the explicit depth leaves one polynomial in the actual
numeric occurrence, clause count, ambient size and incoming word bound. -/
theorem full_space_scalar_polynomial :
    ∃ C degree : ℕ, ∀ n m B W : ℕ, 0 < m → 0 < B →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (L + 1) (continuationSpace m B L a prepared) ≤
        C * (n + m + B + W + 16) ^ degree ∧
      retainedBound m B L a prepared ≤ C * (n + m + B + W + 16) ^ degree := by
  obtain ⟨C, degree, hfull⟩ := full_space_polynomial
  refine ⟨C * 20001 ^ degree, 4 * degree, ?_⟩
  intro n m B W hm hB L a prepared ha hmeta hp
  let X := n + m + B + W + 16
  have hx : B + m + 1 ≤ X := by dsimp [X]; omega
  have hdepth := (distanceDenom_polynomial m B).trans
    (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left hx 4))
  have hlin : n + m + W + 16 ≤ X ^ 4 :=
    (show n + m + W + 16 ≤ X by dsimp [X]; omega).trans
      (Nat.le_self_pow (by decide) X)
  have hsize : n + m + W + SparseCode.distanceDenom m B + 16 ≤ 20001 * X ^ 4 := by
    omega
  have h := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize degree)
  rw [mul_pow, ← pow_mul, ← Nat.mul_assoc] at h
  have hf := hfull n m B W hm hB a prepared ha hmeta hp
  exact ⟨hf.1.trans h, hf.2.trans h⟩

/-- Actual greedy scalar and physical master-word cap, with no execution-time term. -/
theorem greedy_scalar_sum_le (n m B W : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hB : 0 < B) (hmb : m ≤ n * B) :
    n + m + SparseCode.totalRows m B + SparseCode.degreeBound m B +
      SparseCode.distanceDenom m B + HashCandidates.digitWidth m +
      HashSelect.loopCap n m + W + 1 ≤
        1000000 * (n + m + B + W + 16) ^ 5 := by
  let S := n + m + B + W + 16
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hrows := SparseCode.totalRows_le hn hm hB hmb
  have hlog : SparseCode.logSize m ≤ S := by
    have h := Nat.log_le_self 2 m
    dsimp [SparseCode.logSize, S]
    omega
  have hBS : B ≤ S := by dsimp [S]; omega
  have hdegree : SparseCode.degreeBound m B ≤ 320000 * S ^ 5 := by
    have hh := Nat.mul_le_mul (Nat.pow_le_pow_left hBS 2) (Nat.pow_le_pow_left hlog 3)
    have he : SparseCode.degreeBound m B = 320000 * (B ^ 2 * SparseCode.logSize m ^ 3) := by
      unfold SparseCode.degreeBound SparseCode.gapDenom
      ring
    rw [he]
    calc
      _ ≤ 320000 * (S ^ 2 * S ^ 3) := Nat.mul_le_mul_left _ hh
      _ = _ := by ring
  have hdepth : SparseCode.distanceDenom m B ≤ 20000 * S ^ 5 := by
    apply (distanceDenom_polynomial m B).trans
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (show B + m + 1 ≤ S by dsimp [S]; omega) 4).trans
      (Nat.pow_le_pow_right hS (by decide))
  have hwidth : HashCandidates.digitWidth m ≤ 3 * m + 1 := DyadicWidth.width_le_succ _
  have hsize : Nat.size m ≤ m := Nat.size_le.mpr (Nat.lt_pow_self (by decide))
  have hrounds : HashSelect.loopCap n m ≤ 2 * (n + m + 1) := by
    unfold HashSelect.loopCap
    omega
  have hsmall : n + m + SparseCode.totalRows m B + HashCandidates.digitWidth m +
      HashSelect.loopCap n m + W + 1 ≤ 6 * S := by
    dsimp [S]
    omega
  have hpow : S ≤ S ^ 5 := Nat.le_self_pow (by decide) S
  change _ ≤ 1000000 * S ^ 5
  omega

/-- The actual preparation output determines a common cap before any greedy
round. Both preparation prefixes and this cap are ordinary fixed polynomials. -/
theorem prepared_common_bound_polynomial_oai :
    ∃ C degree : ℕ, ∀ n m B W : ℕ, 0 < n → 0 < m → 0 < B → m ≤ n * B →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : StructuredCalls.State 40 896, (∀ i, (a.stacks i).length ≤ L) →
      LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (max (L + 1) (continuationSpace m B L a prepared))
        (NativeLeafRun.commonBound n m B (retainedBound m B L a prepared)) ≤
          C * (n + m + B + W + 16) ^ degree := by
  obtain ⟨C, d, hprep⟩ := full_space_scalar_polynomial
  let K := 16 * 1000000 ^ 3 * (C + 1) ^ 15
  refine ⟨K + C, (d + 1) * 15, ?_⟩
  intro n m B W hn hm hB hmb L a prepared ha hmeta hp
  let X := n + m + B + W + 16
  let R := retainedBound m B L a prepared
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hh := hprep n m B W hm hB a prepared ha hmeta hp
  have hr : R ≤ C * X ^ d := hh.2
  have hlin : X ≤ X ^ (d + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ d + 1 by omega)
  have hdpow : X ^ d ≤ X ^ (d + 1) := Nat.pow_le_pow_right hX (by omega)
  have hsize : n + m + B + R + 16 ≤ (C + 1) * X ^ (d + 1) := by
    have hr' := hr.trans (Nat.mul_le_mul_left C hdpow)
    have hrest : n + m + B + 16 ≤ X := by dsimp [X]; omega
    nlinarith only [hr', hlin, hrest]
  have hcap : HashQueryInputBounds.commonCap n m B R ≤
      1000000 * ((C + 1) * X ^ (d + 1)) ^ 5 :=
    (greedy_scalar_sum_le n m B R hn hm hB hmb).trans
      (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hsize 5))
  have hcommon := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hcap 3)
  have heq : 16 * (1000000 * ((C + 1) * X ^ (d + 1)) ^ 5) ^ 3 =
      K * X ^ ((d + 1) * 15) := by
    dsimp [K]
    simp only [mul_pow, ← pow_mul, Nat.reduceMul, Nat.mul_assoc]
    norm_num only [Nat.reducePow, Nat.reduceMul, ← Nat.mul_assoc]
  rw [heq] at hcommon
  have he : d ≤ (d + 1) * 15 := by omega
  have hprepare := hh.1.trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX he))
  apply max_le
  · exact hprepare.trans (Nat.mul_le_mul_right _ (by dsimp [K]; omega))
  · exact hcommon.trans (Nat.mul_le_mul_right _ (by omega))


open SqrtLog.CodeSetupCost

open Filter SqrtLog.Asymptotic SqrtLog.Statement
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial_oai
