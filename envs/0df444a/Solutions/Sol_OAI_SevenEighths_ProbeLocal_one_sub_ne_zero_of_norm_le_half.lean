-- Prove2me | solution 1 for OAI.SevenEighths.ProbeLocal.one_sub_ne_zero_of_norm_le_half
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:57:52.366336+00:00
-- url     : https://prove2.me/submissions/ab111244-ce4a-4b88-881b-2dc307005cc1

import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false

theorem solution (a : ℂ) (ha : ‖a‖ ≤ 1/2) : 1 - a ≠ 0 := by
  intro h
  have ha_eq : a = 1 := (sub_eq_zero.mp h).symm
  subst a
  norm_num at ha
