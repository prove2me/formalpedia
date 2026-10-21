-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.periodModel_mv_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:23:03.418+00:00
-- url     : https://prove2.me/submissions/25c6f84b-b6e4-454f-bc29-25ae80c60457

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_product_C_add_X_pow

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (j h : ℕ) (a A : Fin m → ℕ) :
    (periodModel j h a).coeff (InterpolationMatrix.exponentVector A) =
      PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        (1 + PowerSeries.X) ^ h *
        ∏ i, (PowerSeries.C ((j : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I)) +
          PowerSeries.log ℂ) ^ (a i - A i) := by
  rw [periodModel, MvPolynomial.coeff_C_mul,
    OAI.PiExponent.FinitePeriodCollision.coeff_product_C_add_X_pow]
  ring