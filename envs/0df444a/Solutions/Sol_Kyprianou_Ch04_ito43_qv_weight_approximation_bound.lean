-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_weight_approximation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:43:22.349387+00:00
-- url     : https://prove2.me/submissions/a6618093-297a-42c6-aa10-49963f2ab3b0

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Finite weighted energy perturbation bound. -/
theorem solution {ι : Type} (S : Finset ι) (g h e : ι → ℝ) (δ : ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) (hh : ∀ i ∈ S, |g i-h i| ≤ δ) :
    |∑ i ∈ S, (g i-h i)*e i| ≤ δ * ∑ i ∈ S, e i := by
  calc
    |∑ i ∈ S, (g i-h i)*e i| ≤ ∑ i ∈ S, |(g i-h i)*e i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, δ*e i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (he i hi)]
      exact mul_le_mul_of_nonneg_right (hh i hi) (he i hi)
    _ = δ * ∑ i ∈ S, e i := by rw [Finset.mul_sum]
