-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteTelescopingV7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:15:06.098481+00:00
-- url     : https://prove2.me/submissions/c553ce2e-a16e-449a-9c42-03adac4c8c8b

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    (n : ℕ) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.range n, (v (k + 1) - v k)) = v n - v 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
