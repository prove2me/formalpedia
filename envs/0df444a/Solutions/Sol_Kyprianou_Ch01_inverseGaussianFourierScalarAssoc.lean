-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFourierScalarAssoc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:57:36.569012+00:00
-- url     : https://prove2.me/submissions/1cd68d2b-e12f-44c4-a01e-d782c2c11647

import Mathlib.Data.Complex.Basic
open Complex
open scoped Complex.SMul
set_option autoImplicit false

theorem solution
    (a d p : ℝ) (f : ℂ) :
    ((a * d) * p) • f =
      (a : ℂ) * ((f * (p : ℂ)) * (d : ℂ)) := by
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring
