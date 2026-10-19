-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_subst_preserves_filtered_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T21:40:07.936456+00:00
-- url     : https://prove2.me/submissions/4bf421f6-78b3-411a-a8d1-83bdebeb9caf

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_subst_coeff_support

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators


theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (b j : ℝ))
    (B : ℝ) (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst sigma F) = 0 := by
  intro a ha
  by_contra hne
  have hs := OAI.PiExponent.LogarithmicJetIdeals.weighted_subst_coeff_support
    q hq sigma hsigma F a hne
  rcases hs with ⟨b, hb, hba⟩
  have hb_lt : (∑ j, q j * (b j : ℝ)) < B := lt_of_le_of_lt hba ha
  exact hb (hF b hb_lt)

