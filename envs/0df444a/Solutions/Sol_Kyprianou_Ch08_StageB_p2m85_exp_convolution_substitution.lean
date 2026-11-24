-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_exp_convolution_substitution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:30:42.941987+00:00
-- url     : https://prove2.me/submissions/a659d706-e829-4330-a5f0-b07f7ea79706

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution
    (W : ℝ → ℝ) (φ z : ℝ) (hz : 0 ≤ z)
    (hzero : ∀ y, y < 0 → W y = 0) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-φ*t) *
      (Real.exp (-φ*(z-t)) * W (z-t))) =
      Real.exp (-φ*z) * ∫ y in (0 : ℝ)..z, W y := by
  have htrunc : (∫ t in Ioi (0 : ℝ), Real.exp (-φ*t) *
      (Real.exp (-φ*(z-t)) * W (z-t))) =
      ∫ t in Ioc (0 : ℝ) z, Real.exp (-φ*t) *
        (Real.exp (-φ*(z-t)) * W (z-t)) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun t ht => ht.1)
    intro t ht
    have h : z < t := lt_of_not_ge fun hle => ht.2 ⟨ht.1, hle⟩
    rw [hzero _ (sub_neg.mpr h), mul_zero, mul_zero]
  rw [htrunc, ← intervalIntegral.integral_of_le hz, ← intervalIntegral.integral_const_mul]
  have he : (∫ t in (0 : ℝ)..z, Real.exp (-φ*t) *
      (Real.exp (-φ*(z-t)) * W (z-t))) =
      ∫ t in (0 : ℝ)..z, Real.exp (-φ*z) * W (z-t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  have h := intervalIntegral.integral_comp_sub_left
    (f := fun y : ℝ => Real.exp (-φ*z) * W y) (a := (0 : ℝ)) (b := z) z
  simpa only [sub_self, sub_zero] using h
