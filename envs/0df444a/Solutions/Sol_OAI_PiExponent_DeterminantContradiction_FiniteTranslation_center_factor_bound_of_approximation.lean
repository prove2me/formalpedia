-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_factor_bound_of_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:35:35.630422+00:00
-- url     : https://prove2.me/submissions/065a79a5-4100-4d25-bd89-e46124897a94

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_center_norm_le_of_rational_error
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_exp_bound_of_ceil_log

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) (i : Fin d.m) :
    ‖((r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I))‖ ≤
      Real.exp
        (Real.log (2 * (d.K : ℝ)) + nu -
          nu * MatrixArithmetic.logWeights (finiteDenominators d) i) := by
  have ha := d.approximations i.val
  have hk : r.1.val ≤ d.K := Nat.le_of_lt r.1.isLt
  have hq : 2 ≤ d.q i.val := ha.1
  calc
    ‖((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I))‖ ≤
        2 * (d.K : ℝ) * (d.q i.val : ℝ) ^ (-nu) := by
      simpa [MatrixArithmetic.rationalCenters, finiteNumerators,
        finiteDenominators] using
        (OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_norm_le_of_rational_error
          (d.p i.val) (d.q i.val) r.1.val d.K hnu
          (Nat.lt_of_lt_of_le (by decide : 0 < 2) hq) hk ha.2.2)
    _ ≤ Real.exp
        (Real.log (2 * (d.K : ℝ)) + nu -
          nu * MatrixArithmetic.logWeights (finiteDenominators d) i) := by
      simpa [MatrixArithmetic.logWeights, finiteDenominators] using
        (OAI.PiExponent.DeterminantContradiction.FiniteTranslation.exp_bound_of_ceil_log
          (d.q i.val) d.K hnu hq d.K_pos)