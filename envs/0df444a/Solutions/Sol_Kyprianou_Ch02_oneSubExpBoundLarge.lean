-- Prove2me | solution 1 for Kyprianou.Ch02.oneSubExpBoundLarge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:59:50.919216+00:00
-- url     : https://prove2.me/submissions/be938843-4869-4942-a443-cc712c6546ab

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

theorem solution (x : ℝ) (hx1 : 1 ≤ x) :
    1 ≤ 2 * (1 - Real.exp (-x)) := by
  have hexp1 : (2 : Real) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp (1 : Real)]
  have hepos : 0 < Real.exp (1 : Real) := Real.exp_pos _
  have hhalf : 2 * Real.exp (-1) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ hepos).2 (by nlinarith [hexp1])
  have he : Real.exp (-x) ≤ Real.exp (-(1 : Real)) :=
    Real.exp_le_exp.mpr (by linarith [hx1])
  linarith [hhalf, he]
