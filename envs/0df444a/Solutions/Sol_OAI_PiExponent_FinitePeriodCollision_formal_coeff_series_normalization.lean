-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.formal_coeff_series_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:05:51.857463+00:00
-- url     : https://prove2.me/submissions/bd860431-abd2-4686-a2d0-f4ccaf1076f0

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          ∏ i, (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (a i - A i)) =
      PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (∑ i, (a i - A i))) := by
  let B : PowerSeries ℂ :=
    PowerSeries.C ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
      PowerSeries.log ℂ
  have hprod : (∏ i : Fin m, B ^ (a i - A i)) =
      B ^ (∑ i : Fin m, (a i - A i)) :=
    Finset.prod_pow_eq_pow_sum Finset.univ _ _
  change PowerSeries.coeff ell
      (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        (1 + PowerSeries.X) ^ h * ∏ i : Fin m, B ^ (a i - A i)) =
    PowerSeries.coeff ell
      (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        (1 + PowerSeries.X) ^ h * B ^ (∑ i : Fin m, (a i - A i)))
  rw [hprod]