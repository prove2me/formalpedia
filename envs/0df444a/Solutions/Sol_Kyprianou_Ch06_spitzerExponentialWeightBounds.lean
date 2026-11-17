-- Prove2me | solution 1 for Kyprianou.Ch06.spitzerExponentialWeightBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:29:17.476636+00:00
-- url     : https://prove2.me/submissions/a46a2b48-13fd-487d-abe0-cef0992d7109

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
set_option autoImplicit false

theorem solution
    (p t : ℝ) (hp : 0 ≤ p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-p) ≤ Real.exp (-p * t) ∧
      Real.exp (-p * t) ≤ 1 := by
  constructor
  · apply Real.exp_le_exp.mpr
    have h : p * t ≤ p := by nlinarith [mul_le_mul_of_nonneg_left ht1 hp]
    nlinarith
  · have h : 0 ≤ p * t := mul_nonneg hp ht0
    have hExp : Real.exp (-p * t) ≤ Real.exp (0 : ℝ) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    simpa using hExp
