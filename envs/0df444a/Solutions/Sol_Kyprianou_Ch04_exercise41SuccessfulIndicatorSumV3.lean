-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SuccessfulIndicatorSumV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:41:47.605226+00:00
-- url     : https://prove2.me/submissions/2d54f4f7-1eb8-42ec-a1a7-caa4c5c9226e

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem solution
    {Ω : Type} (I : Finset ℕ) (B : ℕ → Set Ω) (ω : Ω) :
    (∑ i ∈ I, (B i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω) =
      ((I.filter (fun i => ω ∈ B i)).card : ℝ≥0∞) := by
  classical
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter, Set.indicator_apply]
