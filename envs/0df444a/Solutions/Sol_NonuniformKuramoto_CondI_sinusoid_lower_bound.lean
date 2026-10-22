-- Prove2me | solution 1 for NonuniformKuramoto.CondI.sinusoid_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:02:42.013477+00:00
-- url     : https://prove2.me/submissions/0db9e24f-e556-45de-801d-33418027a90c

import Mathlib
set_option autoImplicit false

theorem solution (a b x y γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y = γ) (hγ : γ ≤ Real.pi) :
    min a b * Real.sin γ ≤ a * Real.sin x + b * Real.sin y := by
  have hsx : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith)
  have hsy : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy (by linarith)
  have hm0 : 0 ≤ min a b := le_min ha hb
  have h1 : Real.sin γ ≤ Real.sin x + Real.sin y := by
    rw [← hxy, Real.sin_add]
    have := Real.cos_le_one x
    have := Real.cos_le_one y
    nlinarith [mul_nonneg hsx hsy, mul_nonneg hsx (sub_nonneg.2 (Real.cos_le_one y)),
      mul_nonneg hsy (sub_nonneg.2 (Real.cos_le_one x))]
  calc min a b * Real.sin γ ≤ min a b * (Real.sin x + Real.sin y) := mul_le_mul_of_nonneg_left h1 hm0
    _ = min a b * Real.sin x + min a b * Real.sin y := by ring
    _ ≤ a * Real.sin x + b * Real.sin y := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (min_le_left _ _) hsx
      · exact mul_le_mul_of_nonneg_right (min_le_right _ _) hsy
