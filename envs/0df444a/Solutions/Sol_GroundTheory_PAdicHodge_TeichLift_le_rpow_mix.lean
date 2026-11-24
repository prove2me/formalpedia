-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.le_rpow_mix
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:21:01.535888+00:00
-- url     : https://prove2.me/submissions/6e20fa24-4635-4a74-b9d4-743ac8b101e8

import Mathlib


theorem solution {δ B t : ℝ} (hδ : 0 ≤ δ) (hδB : δ ≤ B) (ht : t ≤ 1) :
    δ ≤ B ^ (1 - t) * δ ^ t := by
  have hB := hδ.trans hδB
  calc
    δ = δ ^ (1-t) * δ ^ t := by rw [← Real.rpow_add' hδ (show 1-t+t ≠ 0 by linarith), sub_add_cancel, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hδ hδB (by linarith)) (Real.rpow_nonneg hδ _)
