-- Prove2me | solution 1 for Kyprianou.Ch01.queueExpJensenGap_ae_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:30:48.960196+00:00
-- url     : https://prove2.me/submissions/4dcefcb8-3204-4be7-8cce-bcefa48715b8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
set_option autoImplicit false

theorem solution
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (u v : ℝ) (huv : u ≠ v)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ∀ᵐ z ∂F,
      0 < (1 - Real.exp (-(a * u + b * v) * z)) -
        (a * (1 - Real.exp (-u * z)) +
         b * (1 - Real.exp (-v * z))) := by
  have hae : ∀ᵐ z ∂F, 0 < z := by
    apply (ae_iff).2
    have hz : F {z : ℝ | z ≤ 0} = 0 := hpositive
    simpa only [not_lt] using hz
  filter_upwards [hae] with z hz
  have hne : -u * z ≠ -v * z := by
    intro heq
    have hmul : (u - v) * z = 0 := by nlinarith
    rcases mul_eq_zero.mp hmul with hs | hs
    · exact huv (sub_eq_zero.mp hs)
    · exact (ne_of_gt hz) hs
  have h := strictConvexOn_exp.2
    (Set.mem_univ (-u * z)) (Set.mem_univ (-v * z))
    hne ha hb hab
  simp only [smul_eq_mul] at h
  have hlin : a * (-u * z) + b * (-v * z) =
      -(a * u + b * v) * z := by ring
  rw [hlin] at h
  nlinarith
