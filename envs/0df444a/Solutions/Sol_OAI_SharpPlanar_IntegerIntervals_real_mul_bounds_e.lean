-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.real_mul_bounds_e
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T14:59:09.922305+00:00
-- url     : https://prove2.me/submissions/6db5c8f1-e7f4-47b4-873b-ef3456235cae

import Mathlib

theorem solution {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have interp : ∀ {u v w z : ℝ}, u ≤ w → w ≤ v →
      min (u * z) (v * z) ≤ w * z ∧ w * z ≤ max (u * z) (v * z) := by
    intro u v w z huv hwv
    by_cases hz : 0 ≤ z
    · have h1 : 0 ≤ z * (w - u) := mul_nonneg hz (sub_nonneg.mpr huv)
      have h2 : 0 ≤ z * (v - w) := mul_nonneg hz (sub_nonneg.mpr hwv)
      constructor
      · rw [min_le_iff]; left; nlinarith
      · rw [le_max_iff]; right; nlinarith
    · have hz' : z ≤ 0 := le_of_not_ge hz
      have h1 : z * (w - u) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hz' (sub_nonneg.mpr huv)
      have h2 : z * (v - w) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hz' (sub_nonneg.mpr hwv)
      constructor
      · rw [min_le_iff]; right; nlinarith
      · rw [le_max_iff]; left; nlinarith
  have hxy := interp (u := a) (v := b) (w := x) (z := y) hx.1 hx.2
  have hay : min (a * c) (a * d) ≤ a * y ∧
      a * y ≤ max (a * c) (a * d) := by
    simpa [mul_comm] using interp (u := c) (v := d) (w := y) (z := a) hy.1 hy.2
  have hby : min (b * c) (b * d) ≤ b * y ∧
      b * y ≤ max (b * c) (b * d) := by
    simpa [mul_comm] using interp (u := c) (v := d) (w := y) (z := b) hy.1 hy.2
  constructor
  · exact le_trans
      (le_min (le_trans (min_le_left _ _) hay.1)
        (le_trans (min_le_right _ _) hby.1)) hxy.1
  · exact le_trans hxy.2
      (max_le (le_trans hay.2 (le_max_left _ _))
        (le_trans hby.2 (le_max_right _ _)))
