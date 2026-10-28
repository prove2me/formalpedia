-- Prove2me | solution 1 for KyleProduction.Monopoly.production_stage
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:43:05.716912+00:00
-- url     : https://prove2.me/submissions/5e0cf590-9aed-4fbd-90d1-4632af4fd172

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

open KyleProduction.Monopoly in
theorem solution (P : Params) (hS : P.Standing) (hm : 0 < postMean P) (q : ℝ)
    (hq : q ≠ qHat P) :
    P.ω * (q * (postMean P - q)) + |q| / 2 * kappa P <
      P.ω * (qHat P * (postMean P - qHat P)) + |qHat P| / 2 * kappa P := by
  obtain ⟨_, _, _, hω, _⟩ := hS
  have hk : 0 ≤ kappa P := Real.sqrt_nonneg _
  have hqh : 0 < qHat P := by unfold qHat; positivity
  have key : ∀ x : ℝ, P.ω * (x * (postMean P - x)) + x / 2 * kappa P =
      P.ω * qHat P ^ 2 - P.ω * (x - qHat P) ^ 2 := by
    intro x; unfold qHat; field_simp; ring
  rw [abs_of_pos hqh, key (qHat P)]
  have hne : 0 < (q - qHat P) ^ 2 := by
    have : q - qHat P ≠ 0 := sub_ne_zero.mpr hq
    positivity
  rcases le_or_gt 0 q with h0 | h0
  · rw [abs_of_nonneg h0, key q]
    nlinarith
  · rw [abs_of_neg h0]
    have h2 := key (-q)
    have h3 : 0 ≤ P.ω * (-q - qHat P) ^ 2 := by positivity
    have h4 : P.ω * q * postMean P < 0 := by
      have : P.ω * q < 0 := mul_neg_of_pos_of_neg hω h0
      exact mul_neg_of_neg_of_pos this hm
    have e : P.ω * (q * (postMean P - q)) + -q / 2 * kappa P =
        P.ω * (-q * (postMean P - -q)) + -q / 2 * kappa P + 2 * (P.ω * q * postMean P) := by
      ring
    rw [e]
    linarith
