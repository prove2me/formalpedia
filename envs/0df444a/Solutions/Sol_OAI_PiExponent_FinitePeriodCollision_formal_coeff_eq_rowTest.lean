-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.formal_coeff_eq_rowTest
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:02:41.87342+00:00
-- url     : https://prove2.me/submissions/f3456a75-bf4d-4763-9b30-5c7140371956

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_formal_coeff_series_normalization
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_rowTest_periodFunction_coeff
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_rowTest_congr_sphere
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_periodFunction_eq_analyticColumn_on_sphere
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
      rowTest ell (fun t => analyticColumn h a A
        ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          Complex.log (1 + t))) := by
  let b : ℂ := ((∏ i, (a i).choose (A i) : ℕ) : ℂ)
  let center : ℂ := (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  let d : ℕ := ∑ i, (a i - A i)
  have hf := OAI.PiExponent.FinitePeriodCollision.formal_coeff_series_normalization
    (j := j) (h := h) (ell := ell) (a := a) (A := A)
  have hc := OAI.PiExponent.FinitePeriodCollision.rowTest_periodFunction_coeff
    b center h d ell
  have hperiod := OAI.PiExponent.FinitePeriodCollision.periodFunction_eq_analyticColumn_on_sphere
    j h a A
  have hcongr := OAI.PiExponent.FinitePeriodCollision.rowTest_congr_sphere
    (f := fun t => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d)
    (g := fun t => analyticColumn h a A (center + Complex.log (1 + t)))
    ell hperiod
  dsimp [b, center, d] at hf hc hcongr ⊢
  calc
    _ = PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          (PowerSeries.C ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (∑ i, (a i - A i))) := hf
    _ = rowTest ell (fun t => ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
          (1 + t) ^ h *
          (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            Complex.log (1 + t)) ^ (∑ i, (a i - A i))) := hc.symm
    _ = rowTest ell (fun t => analyticColumn h a A
          ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
            Complex.log (1 + t))) := hcongr