-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_monomial_coeff_eq_zero_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:08:55.914388+00:00
-- url     : https://prove2.me/submissions/2510b249-ec7d-4677-b7d3-e747599febaa

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_coeff_eq_zero_of_weight_lt
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_mvPowerSeries_substitution_monomial_coeff_eq_zero_of_weight_lt

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ)
    (N : Fin m → ℕ) (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (a b : Fin (m + 1) → ℕ)
    (hab : (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
      (∑ i, Fin.cases v0 u i * (a i : ℝ))) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (seriesShear D
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0 := by
  have hL : ∀ i α,
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i →
        MvPowerSeries.coeff α (liftLogSeries m (D i)) = 0 := by
    intro i α hα
    exact OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_zero_of_weight_lt
      v0 u N D hv0 hN hD i α hα
  simpa only [seriesShear, MvPolynomial.aeval_monomial, map_one, one_mul] using
    (OAI.PiExponent.AdmissibleFormalInterpolation.mvPowerSeries_substitution_monomial_coeff_eq_zero_of_weight_lt
      v0 u (fun i => liftLogSeries m (D i)) hL a b hab)