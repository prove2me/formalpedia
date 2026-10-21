-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.mvPowerSeries_substitution_monomial_coeff_eq_zero_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:00:38.631005+00:00
-- url     : https://prove2.me/submissions/4ccd51c3-18b2-4fff-9846-1fd01e6a66c2

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_mvPowerSeries_aeval_monomial_coeff_eq_zero_of_weight_lt
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_substitution_generators_have_weighted_support

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ)
    (L : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hL : ∀ i α,
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i →
        MvPowerSeries.coeff α (L i) = 0)
    (a b : Fin (m + 1) → ℕ)
    (hab : (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
      (∑ i, Fin.cases v0 u i * (a i : ℝ))) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (MvPolynomial.aeval (Fin.cases (MvPowerSeries.X 0)
        (fun i => MvPowerSeries.X i.succ + L i))
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0 := by
  let F : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (MvPowerSeries.X 0) (fun i => MvPowerSeries.X i.succ + L i)
  have hF : ∀ (i : Fin (m + 1)) (α : Fin (m + 1) →₀ ℕ),
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < Fin.cases v0 u i →
      MvPowerSeries.coeff α (F i) = 0 := by
    intro i α hα
    exact OAI.PiExponent.AdmissibleFormalInterpolation.substitution_generators_have_weighted_support
      v0 u L hL i α hα
  have hmain := OAI.PiExponent.AdmissibleFormalInterpolation.mvPowerSeries_aeval_monomial_coeff_eq_zero_of_weight_lt
    (Fin.cases v0 u) F hF a b hab
  show MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (MvPolynomial.aeval F (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0
  exact hmain
