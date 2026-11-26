-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49GeometricSeriesV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:39.199805+00:00
-- url     : https://prove2.me/submissions/805f3b48-2e5c-4809-8bcd-94d72fe36b3f

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false


theorem solution
    (rho : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho < 1)
    (u r : ℕ → ℝ)
    (hu : ∀ k, 0 ≤ u k)
    (hr : ∀ n, 0 ≤ r n ∧ r n ≤ rho ^ n)
    (hrec : ∀ n, r n = (1 - rho) * (rho ^ n * u n) + r (n + 1)) :
    r 0 = (1 - rho) * ∑' k, rho ^ k * u k := by
  let a : ℕ → ℝ := fun k => (1 - rho) * (rho ^ k * u k)
  have ha : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (sub_nonneg.mpr hr1.le) (mul_nonneg (pow_nonneg hr0 k) (hu k))
  have hpartial : ∀ n, ∑ k ∈ Finset.range n, a k = r 0 - r n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hh := hrec n
      change r n = a n + r (n + 1) at hh
      linarith
  have hlim : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun n => (hr n).1) (fun n => (hr n).2)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  have ht : Tendsto (fun n => r 0 - r n) atTop (𝓝 (r 0)) := by
    simpa using (tendsto_const_nhds (x := r 0)).sub hlim
  have hsum : HasSum a (r 0) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg ha (r 0)).2
    simpa only [hpartial] using ht
  calc
    r 0 = ∑' k, a k := hsum.tsum_eq.symm
    _ = (1 - rho) * ∑' k, rho ^ k * u k := by simp only [a, tsum_mul_left]
