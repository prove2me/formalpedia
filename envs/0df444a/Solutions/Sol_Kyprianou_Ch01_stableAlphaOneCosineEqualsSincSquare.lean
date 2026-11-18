-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineEqualsSincSquare
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:13:02.463746+00:00
-- url     : https://prove2.me/submissions/da132281-4cd6-4c6b-b512-7f48e9e720fe

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
set_option autoImplicit false
/-! The absolutely integrable cosine deficit is exactly a sinc-squared integral. -/
theorem solution :
    (∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2) =
    ∫ x in Set.Ioi (0 : ℝ), (Real.sin x / x) ^ 2 := by
  have htrig (x : ℝ) :
      1 - Real.cos (2 * x) = 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hpoint (x : ℝ) (hx : x ≠ 0) :
      (1 - Real.cos (2 * x)) / (2 * x) ^ 2 =
        (1 / 2 : ℝ) * (Real.sin x / x) ^ 2 := by
    rw [htrig]
    field_simp
  have heq :
      (∫ x in Ioi (0 : ℝ),
        (1 - Real.cos (2 * x)) / (2 * x) ^ 2) =
        ∫ x in Ioi (0 : ℝ),
          (1 / 2 : ℝ) * (Real.sin x / x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpoint x (ne_of_gt hx)
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (fun x : ℝ => (1 - Real.cos x) / x ^ 2) 0
    (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero] at hscale
  rw [hscale] at heq
  rw [integral_const_mul] at heq
  simp only [smul_eq_mul] at heq
  norm_num at heq
  linarith
