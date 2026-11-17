-- Prove2me | solution 1 for Kyprianou.Ch01.geometricComplexGeneratingSeries
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:47:47.581715+00:00
-- url     : https://prove2.me/submissions/4a4e6bda-710e-43a8-adb1-11f1cd30c354

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

theorem solution (p z : ℂ)
    (hbound : ‖(1 - p) * z‖ < 1) :
    (∑' k : ℕ, p * (1 - p) ^ k * z ^ k) =
      p / (1 - (1 - p) * z) := by
  have hgeom : (∑' k : ℕ, ((1 - p) * z) ^ k) =
      1 / (1 - ((1 - p) * z)) := by
    simpa only [one_div] using (tsum_geometric_of_norm_lt_one hbound)
  calc
    (∑' k : ℕ, p * (1 - p) ^ k * z ^ k) =
      ∑' k : ℕ, p * (((1 - p) * z) ^ k) := by
        congr 1
        funext k
        rw [mul_pow]
        ring
    _ = p * (∑' k : ℕ, ((1 - p) * z) ^ k) := tsum_mul_left
    _ = p / (1 - (1 - p) * z) := by rw [hgeom]; ring
