-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:30:31.485517+00:00
-- url     : https://prove2.me/submissions/a460e1be-a770-4624-970c-8fe6086eb03b

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_center_product_aggregate_of_center_factor_bounds_weighted_product
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_center_product_aggregate_of_center_factor_bounds_exponent_budget

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hsupport :
      (∑ i : Fin d.m,
        MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
          (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ))
    (hcenter :
      ∀ i : Fin d.m,
        ‖((r.1.val : ℂ) *
          (MatrixArithmetic.rationalCenters (finiteNumerators d)
            (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I))‖ ≤
          Real.exp
            (Real.log (2 * (d.K : ℝ)) + nu -
              nu * MatrixArithmetic.logWeights (finiteDenominators d) i)) :
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
  let z : Fin d.m → ℂ := fun i =>
    (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I)
  let w : Fin d.m → ℝ := MatrixArithmetic.logWeights (finiteDenominators d)
  let e : Fin d.m → ℕ := fun i => t.1.1 i - r.2.1 i.succ - t.2.1 i
  let C : ℝ := Real.log (2 * (d.K : ℝ)) + nu
  have hK : (1 : ℝ) ≤ (d.K : ℝ) := by
    exact_mod_cast d.K_pos
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (Real.log_nonneg (by nlinarith)) hnu
  have hagg :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_weighted_product
      z w e C nu hnu hC (by
        intro i
        simpa [z, w, C] using hcenter i)
  have hbudget :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_exponent_budget
      d hnu hH r t hsupport
  calc
    ‖∏ i : Fin d.m, (z i) ^ (e i)‖ ≤
        Real.exp (C * (∑ i : Fin d.m, (e i : ℝ)) -
          nu * (∑ i : Fin d.m, w i * (e i : ℝ))) := by
      exact hagg
    _ ≤ Real.exp
        (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) +
          H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar)) := by
      apply Real.exp_le_exp.mpr
      simpa [z, w, e, C, weight] using hbudget