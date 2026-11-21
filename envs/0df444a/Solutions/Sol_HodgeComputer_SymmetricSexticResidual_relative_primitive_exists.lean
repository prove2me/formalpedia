-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.relative_primitive_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T05:01:47.537381+00:00
-- url     : https://prove2.me/submissions/b6dbb68b-b207-4d9d-8105-76c7da362b89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_ReflectionChart_relative_primitive_of_canonical_trace
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_chart_and_target_irreducible
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_canonical_trace_primitive_exists
import Definitions.Def_HodgeComputerSymmetricChart
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace SymTraceSketch
open MvPolynomial HodgeComputer.SymmetricSexticResidual HodgeComputer.ReflectionChart

private lemma symWeighted_cubic :
    symWeighted = symEll * X 4 ^ 3 + symB * X 4 ^ 2 + symC * X 4 + symD := by
  apply MvPolynomial.funext
  intro x
  simp [symWeighted, leftQuadric, rightQuadric, symEll, symB, symC, symD, eval_X, eval_C]
  ring

private lemma symSource_cubic :
    symSource = (X 1 * X 3 * X 2 ^ 2) + (-X 1 * X 3 * (X 2 ^ 2 + X 0 ^ 2)) * X 4 +
      (X 1 * X 3 * X 0 ^ 2) * X 4 ^ 2 + 0 * X 4 ^ 3 := by
  apply MvPolynomial.funext
  intro x
  simp [symSource, eval_X, eval_C]
  ring

private lemma normalPoint_zero : eval normalPoint (squareLift symWeighted) = 0 := by
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  have hi4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  simp [symWeighted, leftQuadric, rightQuadric, squareLift, normalPoint, eval_X, eval_C]
  norm_num [hi2, hi4, hi6]

private lemma normalPoint_ell_ne : eval normalPoint (squareLift symEll) ≠ 0 := by
  simp [symEll, squareLift, normalPoint]

private lemma symEll_base (k : Fin 4) : pderiv k.succ symEll = 0 := by
  fin_cases k <;>
    simp [symEll, Derivation.leibniz, Derivation.leibniz_pow, pderiv_C]

private lemma symB_u : pderiv 4 symB = 0 := by
  simp [symB, Derivation.leibniz, Derivation.leibniz_pow, pderiv_C]

private lemma symC_u : pderiv 4 symC = 0 := by
  simp [symC, Derivation.leibniz, Derivation.leibniz_pow, pderiv_C]

private lemma symD_u : pderiv 4 symD = 0 := by
  simp [symD, Derivation.leibniz, Derivation.leibniz_pow, pderiv_C]

end SymTraceSketch

theorem solution :
    HodgeComputer.ReflectionChart.RelativePrimitive
      HodgeComputer.SymmetricSexticResidual.symWeighted
      HodgeComputer.SymmetricSexticResidual.symSource := by
  open SymTraceSketch MvPolynomial HodgeComputer.SymmetricSexticResidual in
  exact HodgeComputer.ReflectionChart.relative_primitive_of_canonical_trace
    symWeighted symSource symEll symB symC symD
    (X 1 * X 3 * X 2 ^ 2) (-X 1 * X 3 * (X 2 ^ 2 + X 0 ^ 2)) (X 1 * X 3 * X 0 ^ 2) 0
    symWeighted_cubic symSource_cubic
    chart_and_target_irreducible.2 normalPoint_zero normalPoint_ell_ne
    symEll_base symB_u symC_u symD_u
    (by simp [Derivation.leibniz, Derivation.leibniz_pow])
    (by simp [Derivation.leibniz, Derivation.leibniz_pow])
    (by simp [Derivation.leibniz, Derivation.leibniz_pow])
    (by simp)
    canonical_trace_primitive_exists
