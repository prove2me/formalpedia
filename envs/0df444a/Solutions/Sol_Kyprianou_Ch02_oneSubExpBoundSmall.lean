-- Prove2me | solution 1 for Kyprianou.Ch02.oneSubExpBoundSmall
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:59:45.081046+00:00
-- url     : https://prove2.me/submissions/944d1e01-4857-4be8-8499-28dc4a9558d9

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ 2 * (1 - Real.exp (-x)) := by
  have hexp : 1 + x ≤ Real.exp x := by
    nlinarith [Real.add_one_le_exp x]
  have hden : 0 < 1 + x := by linarith
  have hpos : 0 < Real.exp x := Real.exp_pos x
  have hmul : (1 + x) * Real.exp (-x) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ hpos).2 (by linarith [hexp])
  have hpoly : 1 ≤ (1 + x) * (1 - x / 2) := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]
  by_contra h
  have hgt : 0 < Real.exp (-x) - (1 - x / 2) := by linarith
  have hstrict : 0 < (1 + x) * (Real.exp (-x) - (1 - x / 2)) :=
    mul_pos hden hgt
  nlinarith [hstrict, hpoly, hmul]
