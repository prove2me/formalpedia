-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneImaginaryKernelScalingPointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:15:03.225305+00:00
-- url     : https://prove2.me/submissions/45208e4b-8566-4432-a6f3-5422eff253e1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! Scaling the imaginary Lévy kernel moves the source compensation cutoff. -/
theorem solution
    (z r : ℝ) (hz : 0 < z) :
    ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2 =
      z ^ 2 * (((z * r) * (if z * r < z then (1 : ℝ) else 0) -
        Real.sin (z * r)) / (z * r) ^ 2) := by
  let f : ℝ → ℝ := fun u =>
    (u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2
  have hpoint (r : ℝ) :
      ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2 =
        z ^ 2 * f (z * r) := by
    by_cases hr : r = 0
    · subst r
      simp [f]
    · have heq : (if r < 1 then (1 : ℝ) else 0) =
          if z * r < z then (1 : ℝ) else 0 := by
        have hiff : r < 1 ↔ z * r < z := by
          constructor
          · intro h
            nlinarith [mul_pos hz (sub_pos.mpr h)]
          · intro h
            by_contra hnot
            have hrge : 1 ≤ r := le_of_not_gt hnot
            nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hrge)]
        simp [hiff]
      dsimp [f]
      rw [heq]
      have hz0 : z ≠ 0 := ne_of_gt hz
      field_simp
  exact hpoint r
