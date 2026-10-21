-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_formal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:15:50.621584+00:00
-- url     : https://prove2.me/submissions/7300b453-bf49-4446-80c6-50783bdf242a

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_periodModel_mv_coeff
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
      ((periodModel j h a).coeff (InterpolationMatrix.exponentVector A)) =
      PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          ∏ i, (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (a i - A i)) := by
  exact congrArg (PowerSeries.coeff ell)
    (OAI.PiExponent.FinitePeriodCollision.periodModel_mv_coeff j h a A)