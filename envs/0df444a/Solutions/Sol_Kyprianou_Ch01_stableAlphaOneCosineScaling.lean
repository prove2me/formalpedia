-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineScaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:25:04.164606+00:00
-- url     : https://prove2.me/submissions/719ec8cc-1b3f-4a8c-adf0-4b4c1b4b36ed

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineIntegralValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! Homogeneity of the stable index-one real Lévy exponent. -/
theorem solution
    (z : ℝ) (hz : 0 < z) :
    (∫ r in Set.Ioi (0 : ℝ), (1 - Real.cos (z * r)) / r ^ 2 ∂volume) =
      Real.pi * z / 2 := by
  let f : ℝ → ℝ := fun r => (1 - Real.cos r) / r ^ 2
  have hchange := MeasureTheory.integral_comp_mul_left_Ioi f 0 hz
  simp only [mul_zero] at hchange
  have hpoint (r : ℝ) :
      (1 - Real.cos (z * r)) / r ^ 2 = z ^ 2 * f (z * r) := by
    by_cases hr : r = 0
    · subst r
      simp [f]
    · dsimp [f]
      have hz0 : z ≠ 0 := ne_of_gt hz
      field_simp
  calc
    (∫ r in Set.Ioi (0 : ℝ), (1 - Real.cos (z * r)) / r ^ 2 ∂volume) =
        ∫ r in Set.Ioi (0 : ℝ), z ^ 2 * f (z * r) ∂volume := by
          congr 1
          funext r
          exact hpoint r
    _ = z ^ 2 * (∫ r in Set.Ioi (0 : ℝ), f (z * r) ∂volume) := by
          rw [integral_const_mul]
    _ = z ^ 2 * (z⁻¹ * (∫ r in Set.Ioi (0 : ℝ), f r ∂volume)) := by
          rw [hchange]
          simp [smul_eq_mul]
    _ = Real.pi * z / 2 := by
          change z ^ 2 * (z⁻¹ *
            (∫ r in Set.Ioi (0 : ℝ), (1 - Real.cos r) / r ^ 2 ∂volume)) = _
          rw [Kyprianou.Ch01.stableAlphaOneCosineIntegralValue]
          field_simp
