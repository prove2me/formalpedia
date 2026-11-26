-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_discrete_product_summation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:26:25.640113+00:00
-- url     : https://prove2.me/submissions/eb9bab50-48d7-4c37-b2a0-64756cbb55e8

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false

/-- Discrete integration by parts for complex-valued sequences. -/
theorem solution (E H : Nat → Complex) (N : Nat) :
    (∑ i ∈ Finset.range N, H i * (E (i+1) - E i)) +
    (∑ i ∈ Finset.range N, E (i+1) * (H (i+1) - H i)) =
      E N * H N - E 0 * H 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    linear_combination ih
