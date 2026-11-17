-- Prove2me | solution 1 for Kyprianou.Ch01.geometricFourierConvergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:42:26.310223+00:00
-- url     : https://prove2.me/submissions/fc22baaf-15dd-4046-b976-53e71a6db07e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

theorem solution
    (p : unitInterval.Elem) (hp : p ≠ 0) (xi : ℝ) :
    ‖(1 - ((p : ℝ) : ℂ)) *
      Complex.exp (Complex.I * (xi : ℂ))‖ < 1 := by
  have hpos : 0 < (p : ℝ) := by
    have hp0 : (p : ℝ) ≠ 0 := by
      intro hz
      apply hp
      exact Subtype.ext hz
    exact lt_of_le_of_ne p.property.1 (Ne.symm hp0)
  have hnonneg : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
  have hlt : 1 - (p : ℝ) < 1 := sub_lt_self 1 hpos
  have hnorm : ‖(1 - ((p : ℝ) : ℂ))‖ = 1 - (p : ℝ) := by
    norm_cast
    exact abs_of_nonneg hnonneg
  rw [norm_mul, hnorm, Complex.norm_exp_I_mul_ofReal]
  simpa using hlt
