-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanPhiPositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:47:06.385146+00:00
-- url     : https://prove2.me/submissions/6e2966a4-28d9-412d-9630-bce5c2862007

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory ProbabilityTheory
set_option autoImplicit false

/-- The positive quadratic root of the Brownian discounted stopping equation. -/
theorem solution
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q) :
    0 < (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
      sigma ^ 2 := by
  have hsigma2 : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hdelta : 0 < 2 * sigma ^ 2 * q := by positivity
  have hsq : gamma ^ 2 < gamma ^ 2 + 2 * sigma ^ 2 * q := by linarith
  have hroot : Real.sqrt (gamma ^ 2) <
      Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) :=
    Real.sqrt_lt_sqrt (sq_nonneg gamma) hsq
  have hbelow : -gamma ≤ Real.sqrt (gamma ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
    exact neg_le_abs gamma
  apply div_pos _ hsigma2
  linarith
