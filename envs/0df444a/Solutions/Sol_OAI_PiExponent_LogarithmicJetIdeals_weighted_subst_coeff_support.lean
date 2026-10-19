-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_subst_coeff_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T21:53:23.253988+00:00
-- url     : https://prove2.me/submissions/087dee4b-7189-4cda-9bd9-277e901d2b5b

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_support_witness
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_product_support_weight

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (b j : ℝ))
    (F : MvPowerSeries (Fin (m + 1)) ℂ) :
    ∀ a : Fin (m + 1) → ℕ,
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst sigma F) ≠ 0 →
      ∃ b : Fin (m + 1) → ℕ,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F ≠ 0 ∧
        (∑ j, q j * (b j : ℝ)) ≤ ∑ j, q j * (a j : ℝ) := by
  intro a ha
  obtain ⟨b, hF, hprod⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.subst_support_witness
      q hq sigma hsigma F a ha
  exact ⟨b, hF,
    OAI.PiExponent.LogarithmicJetIdeals.product_support_weight
      q hq sigma hsigma b a hprod⟩
