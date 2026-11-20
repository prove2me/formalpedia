-- Prove2me | solution 1 for Kyprianou.Ch01.complexHalfLogPrincipalSqrt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:37:50.643779+00:00
-- url     : https://prove2.me/submissions/049dd722-4eaa-424c-a167-0e82954b527a

import Mathlib
open Complex
set_option autoImplicit false

theorem solution (z : ℂ) (hz : z ≠ 0) :
    Complex.exp (((1 / 2 : ℝ) : ℂ) * Complex.log z) =
      Complex.sqrt z := by
  have hcast : (((1 / 2 : ℝ) : ℂ)) = (2 : ℂ)⁻¹ := by norm_num
  rw [hcast]
  calc
    Complex.exp ((2 : ℂ)⁻¹ * Complex.log z) =
      Complex.exp (Complex.log z / 2) := by congr 1; ring
    _ = Complex.sqrt z := (sqrt_eq_exp hz).symm
