-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_dyadic_reward_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:13:00.425928+00:00
-- url     : https://prove2.me/submissions/09ffa9a0-8f81-4f4f-98bc-2b2015480605

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The infimum of exponential path evaluations on the countable dyadic grid is measurable. -/
theorem solution (β : ℝ) :
    Measurable (fun f : NNReal → ℝ =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))) := by
  apply Measurable.iInf
  intro q
  exact ENNReal.measurable_ofReal.comp
    ((measurable_const.mul (measurable_pi_apply ((q.1 : NNReal) / 2 ^ q.2))).exp)
