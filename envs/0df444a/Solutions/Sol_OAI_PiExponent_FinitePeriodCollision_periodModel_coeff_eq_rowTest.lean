-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_rowTest
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:09:32.569496+00:00
-- url     : https://prove2.me/submissions/243854a9-3bb5-4e0b-bd24-abd7bd265dc7

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_periodModel_coeff_eq_formal
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_formal_coeff_eq_rowTest

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
      ((periodModel j h a).coeff (InterpolationMatrix.exponentVector A)) =
      rowTest ell (fun t => analyticColumn h a A
        ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + Complex.log (1 + t))) := by
  calc
    PowerSeries.coeff ell
        ((periodModel j h a).coeff (InterpolationMatrix.exponentVector A)) =
        PowerSeries.coeff ell
          (PowerSeries.C
              (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
            (1 + PowerSeries.X) ^ h *
            ∏ i, (PowerSeries.C ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
              PowerSeries.log ℂ) ^ (a i - A i)) :=
      OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_formal
        j h ell a A
    _ = rowTest ell (fun t => analyticColumn h a A
        ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + Complex.log (1 + t))) :=
      OAI.PiExponent.FinitePeriodCollision.formal_coeff_eq_rowTest
        j h ell a A