-- Prove2me | solution 1 for HodgeComputer.DiagonalPermutation.relative_primitive_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T05:01:49.540194+00:00
-- url     : https://prove2.me/submissions/661c2cb3-d64e-4d38-b026-aa4242b9a113
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_ReflectionChart_relative_primitive_of_canonical_trace
import Theorems.Thm_HodgeComputer_DiagonalPermutation_chart_and_target_irreducible
import Theorems.Thm_HodgeComputer_DiagonalPermutation_canonical_trace_primitive_exists
import Definitions.Def_HodgeComputerDiagonalPermutationQuotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace DiagTraceSketch
open MvPolynomial HodgeComputer.DiagonalPermutation HodgeComputer.ReflectionChart

private lemma diagSource_cubic :
    diagSource =
      (C 2 * X 2 ^ 3 - C 2 * X 1 ^ 3 * X 3 ^ 3) +
      (C 6 * X 2 ^ 3 + C 18 * X 0 * X 2 ^ 2 + C 6 * X 0 ^ 2 * X 2) * X 4 +
      (C 6 * X 0 * X 2 ^ 2 + C 18 * X 0 ^ 2 * X 2 + C 6 * X 0 ^ 3) * X 4 ^ 2 +
      (C 2 * X 0 ^ 3) * X 4 ^ 3 := by
  unfold diagSource
  ring

private lemma normalPoint_zero : eval normalPoint (squareLift diagWeighted) = 0 := by
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  have hi4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  simp [diagWeighted, diagEll, diagB, diagC, diagD, squareLift, normalPoint, eval_X, eval_C]
  norm_num [hi2, hi4, hi6]

private lemma normalPoint_ell_ne : eval normalPoint (squareLift diagEll) ≠ 0 := by
  simp [diagEll, squareLift, normalPoint]

private lemma diagEll_base (k : Fin 4) : pderiv k.succ diagEll = 0 := by
  fin_cases k <;>
    simp [diagEll, Derivation.leibniz, Derivation.leibniz_pow]

private lemma diagB_u : pderiv 4 diagB = 0 := by
  simp [diagB, Derivation.leibniz, Derivation.leibniz_pow]

private lemma diagC_u : pderiv 4 diagC = 0 := by
  simp [diagC, Derivation.leibniz, Derivation.leibniz_pow]

private lemma diagD_u : pderiv 4 diagD = 0 := by
  simp [diagD, Derivation.leibniz, Derivation.leibniz_pow]

end DiagTraceSketch

theorem solution :
    HodgeComputer.ReflectionChart.RelativePrimitive
      HodgeComputer.DiagonalPermutation.diagWeighted
      HodgeComputer.DiagonalPermutation.diagSource := by
  open DiagTraceSketch MvPolynomial HodgeComputer.DiagonalPermutation in
  exact HodgeComputer.ReflectionChart.relative_primitive_of_canonical_trace
    diagWeighted diagSource diagEll diagB diagC diagD
    (C 2 * X 2 ^ 3 - C 2 * X 1 ^ 3 * X 3 ^ 3)
    (C 6 * X 2 ^ 3 + C 18 * X 0 * X 2 ^ 2 + C 6 * X 0 ^ 2 * X 2)
    (C 6 * X 0 * X 2 ^ 2 + C 18 * X 0 ^ 2 * X 2 + C 6 * X 0 ^ 3)
    (C 2 * X 0 ^ 3)
    rfl diagSource_cubic chart_and_target_irreducible.2 normalPoint_zero normalPoint_ell_ne
    diagEll_base diagB_u diagC_u diagD_u
    (by simp [Derivation.leibniz, Derivation.leibniz_pow])
    (by simp [Derivation.leibniz, Derivation.leibniz_pow])
    (by simp [Derivation.leibniz, Derivation.leibniz_pow])
    (by simp [Derivation.leibniz, Derivation.leibniz_pow])
    canonical_trace_primitive_exists
