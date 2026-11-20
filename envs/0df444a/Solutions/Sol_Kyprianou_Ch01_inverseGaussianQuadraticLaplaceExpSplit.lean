-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianQuadraticLaplaceExpSplit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:11:48.4109+00:00
-- url     : https://prove2.me/submissions/fa55472b-e51a-41d6-be15-5777891ac01a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianQuadraticExponentSplit
open Real
set_option autoImplicit false

theorem solution
    (s b q x : ℝ) (hx : 0 < x) :
    Real.exp (-((s - b * x) ^ 2 / (2 * x))) *
      Real.exp (-q * x) =
      Real.exp (s * b) *
        Real.exp (-(s ^ 2 / (2 * x)) -
          (b ^ 2 / 2 + q) * x) := by
  rw [← Real.exp_add]
  rw [show -((s - b * x) ^ 2 / (2 * x)) + -q * x =
      -((s - b * x) ^ 2 / (2 * x)) - q * x by ring]
  rw [Kyprianou.Ch01.inverseGaussianQuadraticExponentSplit s b q x hx]
  rw [show s * b - s ^ 2 / (2 * x) -
      (b ^ 2 / 2 + q) * x =
      s * b + (-(s ^ 2 / (2 * x)) -
        (b ^ 2 / 2 + q) * x) by ring]
  rw [Real.exp_add]
