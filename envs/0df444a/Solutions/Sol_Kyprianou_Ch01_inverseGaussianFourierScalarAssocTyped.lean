-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFourierScalarAssocTyped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:57:45.473126+00:00
-- url     : https://prove2.me/submissions/4770b05e-bf78-48e6-a691-524800447e63

import Mathlib.Data.Complex.Basic
open Complex
open scoped Complex.SMul
set_option autoImplicit false

theorem solution
    (a d p : ℝ) (f : ℂ) :
    ((((a * d) * p) • f) : ℂ) =
      (a : ℂ) * ((f * (p : ℂ)) * (d : ℂ)) := by
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring
