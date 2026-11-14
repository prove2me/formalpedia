-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_6_size_condition
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:00:36.302943+00:00
-- url     : https://prove2.me/submissions/b4c88b88-e5eb-4448-85f9-5b3c97b3c8d0

import Mathlib
set_option autoImplicit false

theorem solution (ν a L n : ℝ) (hν : 0 ≤ ν) (ha : 0 < a) (hL : 0 < L) (hn : 0 < n)
    (hsize : 16*L^2*ν ≤ a^2*n) :
    Real.sqrt (ν*n) ≤ a*n/(4*L) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hm := mul_nonneg (le_of_lt hn) (sub_nonneg.mpr hsize)
    have hL0 : L ≠ 0 := ne_of_gt hL
    field_simp
    nlinarith [sq_nonneg (a*n)]
