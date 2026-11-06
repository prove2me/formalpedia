-- Prove2me | solution 1 for LindelofHypothesis.guth_maynard_density_estimate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T19:50:07.048798+00:00
-- url     : https://prove2.me/submissions/a7209eaf-6b1e-4e06-b4a1-c461c2a926a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_GuthMaynard_zero_density_estimate
import Theorems.Thm_LindelofHypothesis_ingham_density_estimate

open Complex Filter Asymptotics
open scoped ENNReal

namespace GMS1213

theorem mono_bound (σ : ℝ) (a b : ℝ) (hab : a ≤ b) (C : ℝ)
    (h : ∀ᶠ T in atTop, (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ a)) :
    ∃ C' : ℝ, ∀ᶠ T in atTop, (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (C' * T ^ b) := by
  refine ⟨max C 0, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with T hT hT1
  refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : (0:ℝ) ≤ T ^ a := Real.rpow_nonneg (by linarith) _
  calc C * T ^ a ≤ max C 0 * T ^ a := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max C 0 * T ^ b := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hab) (le_max_right _ _)

end GMS1213

theorem solution (σ : ℝ) (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (30 / 13 * (1 - σ) + ε)) := by
  rcases le_total σ (7/10) with h | h
  · obtain ⟨C, hC⟩ := LindelofHypothesis.ingham_density_estimate σ hσ₀ hσ₁ ε hε
    refine GMS1213.mono_bound σ _ _ ?_ C hC
    have : 3 / (2 - σ) * (1 - σ) ≤ 30 / 13 * (1 - σ) := by
      have h2 : 0 < 2 - σ := by linarith
      have h1 : 0 ≤ 1 - σ := by linarith
      apply mul_le_mul_of_nonneg_right _ h1
      rw [div_le_div_iff₀ h2 (by norm_num)]; linarith
    linarith
  · obtain ⟨C, hC⟩ := GuthMaynard.zero_density_estimate σ hσ₀ hσ₁ ε hε
    refine GMS1213.mono_bound σ _ _ ?_ C hC
    have : 15 * (1 - σ) / (3 + 5 * σ) ≤ 30 / 13 * (1 - σ) := by
      have h2 : 0 < 3 + 5 * σ := by linarith
      rw [div_le_iff₀ h2]; nlinarith
    linarith
