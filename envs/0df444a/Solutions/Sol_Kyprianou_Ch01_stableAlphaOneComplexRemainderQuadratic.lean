-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneComplexRemainderQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:32:08.180199+00:00
-- url     : https://prove2.me/submissions/3f9f197c-c0ab-4291-8700-073538a7cc49

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex Real
set_option autoImplicit false
/-! Second-order Taylor remainder controls the compensated stable kernel. -/
theorem solution
    (z r : ℝ) (hsmall : |z * r| ≤ 1) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * ((z * r : ℝ) : ℂ)) +
      Complex.I * ((z * r : ℝ) : ℂ)‖ ≤ (z * r) ^ 2 := by
  have hnorm :
      ‖Complex.I * ((z * r : ℝ) : ℂ)‖ ≤ 1 := by
    simpa [norm_mul, Complex.norm_I] using hsmall
  have h := Complex.norm_exp_sub_one_sub_id_le hnorm
  have heq :
      (1 : ℂ) - Complex.exp (Complex.I * ((z * r : ℝ) : ℂ)) +
        Complex.I * ((z * r : ℝ) : ℂ) =
      -(Complex.exp (Complex.I * ((z * r : ℝ) : ℂ)) - 1 -
        Complex.I * ((z * r : ℝ) : ℂ)) := by ring
  rw [heq, norm_neg]
  have hh :
      ‖Complex.exp (Complex.I * ((z * r : ℝ) : ℂ)) - 1 -
        Complex.I * ((z * r : ℝ) : ℂ)‖ ≤ (|z| * |r|) ^ 2 := by
    simpa [norm_mul, Complex.norm_I] using h
  calc
    _ ≤ (|z| * |r|) ^ 2 := hh
    _ = (z * r) ^ 2 := by rw [← abs_mul, sq_abs]
