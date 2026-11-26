-- Prove2me | solution 1 for Kyprianou.Ch04.positiveDiscountSequenceAndClockError
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:33.884049+00:00
-- url     : https://prove2.me/submissions/ca236396-1a87-4e7a-a35d-f381b97f5bee

import Mathlib
open Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A positive discount sequence converging to zero and its early-clock error. -/
theorem solution :
    let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    (∀ n, 0 < q n) ∧ Tendsto q atTop (nhds 0) ∧
      ∀ T : NNReal, Tendsto (fun n => 1 - Real.exp (-(q n * (T : ℝ)))) atTop (nhds 0) := by
  intro q
  have hp (n : ℕ) : 0 < q n := by dsimp [q]; positivity
  have ht : Tendsto q atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨hp,ht,?_⟩
  intro T
  have h := (ht.mul (tendsto_const_nhds (x := (T : ℝ)))).neg
  have he := Real.continuous_exp.continuousAt.tendsto.comp h
  have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub he
  simpa using h'
