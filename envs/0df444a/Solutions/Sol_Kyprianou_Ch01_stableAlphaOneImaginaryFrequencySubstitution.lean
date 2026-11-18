-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneImaginaryFrequencySubstitution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:52:25.371594+00:00
-- url     : https://prove2.me/submissions/b365bdf8-80c7-419e-84c9-ca3b9c58590f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! Positive frequency rescaling shifts the original one-sided compensation cutoff from 1 to z. -/
theorem solution
    (z : ℝ) (hz : 0 < z) :
    (∫ r in Set.Ioi (0 : ℝ),
      ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2 ∂volume) =
      z * (∫ u in Set.Ioi (0 : ℝ),
        (u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2 ∂volume) := by
  let f : ℝ → ℝ := fun u =>
    (u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2
  have hchange := MeasureTheory.integral_comp_mul_left_Ioi f 0 hz
  simp only [mul_zero] at hchange
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
  calc
    (∫ r in Set.Ioi (0 : ℝ),
      ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2 ∂volume) =
        ∫ r in Set.Ioi (0 : ℝ), z ^ 2 * f (z * r) ∂volume := by
          congr 1
          funext r
          exact hpoint r
    _ = z ^ 2 * (∫ r in Set.Ioi (0 : ℝ), f (z * r) ∂volume) := by
      rw [integral_const_mul]
    _ = z ^ 2 * (z⁻¹ * (∫ u in Set.Ioi (0 : ℝ), f u ∂volume)) := by
      rw [hchange]
      simp [smul_eq_mul]
    _ = z * (∫ u in Set.Ioi (0 : ℝ), f u ∂volume) := by
      field_simp
