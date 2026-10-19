-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_estimate_of_tail_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:26:42.525978+00:00
-- url     : https://prove2.me/submissions/3bea2f68-ff7e-4e75-a7c3-8bc5334451d5

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_center_factor_bound_of_approximation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_center_product_aggregate_of_center_factor_bounds

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hsupport :
      (∑ i : Fin d.m,
        MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
          (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ)) :
    ‖∏ i : Fin d.m,
      (((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I)) ^
            (t.1.1 i - r.2.1 i.succ - t.2.1 i))‖ ≤
      Real.exp
        (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) +
          H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar)) := by
  apply OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds
    d hnu hH r t hsupport
  intro i
  exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_factor_bound_of_approximation
    d hnu hH r t i