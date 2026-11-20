-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianDensityPowerIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:47:30.072991+00:00
-- url     : https://prove2.me/submissions/2d254c98-6b5b-4064-b763-7d068bc1ddeb

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real
set_option autoImplicit false

theorem solution (r : ℝ) (hr : 0 < r) :
    (1 / Real.sqrt (2 * Real.pi * r ^ 3)) =
      (1 / Real.sqrt (2 * Real.pi)) * r ^ (-(3 / 2 : ℝ)) := by
  have hp : 0 ≤ 2 * Real.pi := by positivity
  have hs : Real.sqrt (2 * Real.pi * r ^ 3) =
      Real.sqrt (2 * Real.pi) * Real.sqrt (r ^ 3) := by
    simpa only [mul_assoc] using Real.sqrt_mul hp (r ^ 3)
  have hrpow : Real.sqrt (r ^ 3) = r ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast_mul (le_of_lt hr) (3 : ℕ) (1 / 2 : ℝ)]
    congr 1
    ring
  rw [hs, hrpow]
  rw [Real.rpow_neg (le_of_lt hr), div_eq_mul_inv,
    div_eq_mul_inv, mul_inv_rev]
  ring
