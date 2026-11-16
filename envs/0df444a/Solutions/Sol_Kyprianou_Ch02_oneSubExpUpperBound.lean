-- Prove2me | solution 1 for Kyprianou.Ch02.oneSubExpUpperBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:34:47.60586+00:00
-- url     : https://prove2.me/submissions/52e35394-80b6-43d7-9b94-394746aa35d8

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

theorem solution (x φ : ℝ)
    (hx : 0 ≤ x) (hφ : 0 < φ) :
    1 - Real.exp (-φ * x) ≤ max 1 φ * min 1 x := by
  have hlin := Real.add_one_le_exp (-φ * x)
  have hpositive := Real.exp_pos (-φ * x)
  by_cases hx1 : x ≤ 1
  case pos =>
    have hmax : φ ≤ max 1 φ := le_max_right 1 φ
    have hleft : 1 - Real.exp (-φ * x) ≤ φ * x := by
      nlinarith [hlin]
    have hright : φ * x ≤ max 1 φ * x :=
      mul_le_mul_of_nonneg_right hmax hx
    simpa [min_eq_right hx1] using le_trans hleft hright
  case neg =>
    have hlarge : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    have hmax : (1 : ℝ) ≤ max 1 φ := le_max_left 1 φ
    rw [min_eq_left hlarge]
    nlinarith [hpositive, hmax]
