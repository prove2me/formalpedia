-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicJumpCompoundPoissonExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T00:02:46.178277+00:00
-- url     : https://prove2.me/submissions/f736ecc6-b61a-4cfe-94e4-aef063bfd3d6

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpComplexExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

theorem solution (q z : ℂ) (hq : ‖q‖ < 1) (hqz : ‖q * z‖ < 1) :
    Complex.exp
      (∑' n : ℕ,
        ((q * z) ^ (n + 1) / ((n : ℂ) + 1) -
          q ^ (n + 1) / ((n : ℂ) + 1))) =
      (1 - q) / (1 - q * z) := by
  have hqne : 1 - q ≠ 0 := by
    intro h
    have hEq : q = 1 := (sub_eq_zero.mp h).symm
    have hbad : (1 : ℝ) < 1 := by simpa [hEq] using hq
    exact (lt_irrefl (1 : ℝ)) hbad
  have hqzne : 1 - q * z ≠ 0 := by
    intro h
    have hEq : q * z = 1 := (sub_eq_zero.mp h).symm
    have hbad : (1 : ℝ) < 1 := by simpa [hEq] using hqz
    exact (lt_irrefl (1 : ℝ)) hbad
  rw [Kyprianou.Ch01.logarithmicJumpComplexExponent q z hq hqz]
  rw [Complex.exp_sub, Complex.exp_log hqne, Complex.exp_log hqzne]
