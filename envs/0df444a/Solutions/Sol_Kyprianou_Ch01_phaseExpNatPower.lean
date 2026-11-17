-- Prove2me | solution 1 for Kyprianou.Ch01.phaseExpNatPower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:29:50.911387+00:00
-- url     : https://prove2.me/submissions/371da6ea-4abf-4a68-bbfa-b7eb87eb7553

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

/-! A unit-modulus Fourier phase at integer jump size is an integer power. -/
theorem solution
    (xi : ℝ) (n : ℕ) :
    Complex.exp ((xi : ℂ) *
      (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I) =
      (Complex.exp ((xi : ℂ) * Complex.I)) ^ (n + 1) := by
  have harg :
      (xi : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I =
        (((n + 1 : ℕ) : ℂ) * ((xi : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [harg, Complex.exp_nat_mul]
