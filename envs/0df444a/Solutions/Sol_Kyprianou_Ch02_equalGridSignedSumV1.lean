-- Prove2me | solution 1 for Kyprianou.Ch02.equalGridSignedSumV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:53:59.229144+00:00
-- url     : https://prove2.me/submissions/ee77dc0d-2c54-45c7-b557-a70fec62abf5

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Positivity
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (a b : ℝ≥0) (hab : a ≤ b) (n : ℕ) :
    let g (k : ℕ) : ℝ≥0 := a+(b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    (∑ k : Fin (n+1), (f (g (k.val+1))-f (g k.val))) = f b-f a := by
  dsimp only
  let g (k : ℕ) : ℝ≥0 := a+(b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
  change (∑ k : Fin (n+1), (f (g (k.val+1))-f (g k.val))) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => f (g (k+1))-f (g k))]
  rw [Finset.sum_range_sub (fun k => f (g k))]
  have hg : g (n+1) = b := by
    dsimp [g]
    rw [mul_div_cancel_right₀ _ (by positivity), add_tsub_cancel_of_le hab]
  rw [hg]
  simp [g]
