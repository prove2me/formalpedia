-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.scalar_min_shift_mono_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:50:31.679285+00:00
-- url     : https://prove2.me/submissions/5717fe7b-0c90-4304-bf9a-4321d8dde852

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (c s t y : ℝ) (hc : c ≤ 0)
    (hst : s ≤ t) :
    c * min s y - c * s ≤ c * min t y - c * t := by
  by_cases hs : s ≤ y
  · rw [min_eq_left hs]
    by_cases ht : t ≤ y
    · rw [min_eq_left ht]
      nlinarith
    · have hyt : y ≤ t := le_of_not_ge ht
      rw [min_eq_right hyt]
      nlinarith [mul_nonneg (neg_nonneg.mpr hc) (sub_nonneg.mpr hyt)]
  · have hys : y ≤ s := le_of_not_ge hs
    have hyt : y ≤ t := le_trans hys hst
    rw [min_eq_right hys, min_eq_right hyt]
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) (sub_nonneg.mpr hst)]
