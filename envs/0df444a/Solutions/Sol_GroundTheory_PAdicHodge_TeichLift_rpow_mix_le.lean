-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.rpow_mix_le
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:21:13.435024+00:00
-- url     : https://prove2.me/submissions/8ed3d4d3-2789-40e1-8614-d2027e748b36

import Mathlib


theorem solution {δ B t : ℝ} (hδ : 0 ≤ δ) (hδB : δ ≤ B) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    B ^ (1 - t) * δ ^ t ≤ B := by
  have hB := hδ.trans hδB
  calc
    _ ≤ B ^ (1-t) * B ^ t := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ hδB ht) (Real.rpow_nonneg hB _)
    _ = B := by rw [← Real.rpow_add_of_nonneg hB (sub_nonneg.mpr ht1) ht, sub_add_cancel, Real.rpow_one]
