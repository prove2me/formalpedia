-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_grid_step_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:26:41.010907+00:00
-- url     : https://prove2.me/submissions/b1057139-9d28-433c-93c9-81a956bb8892

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_weight_approximation_bound
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Exchange the two finite sums and apply the proved nonnegative-energy weighted approximation bound. -/
theorem solution
    (n m : ℕ) (u : ℕ → NNReal) (T : NNReal)
    (hu : ∀ k < n, u k ≤ T) (G : NNReal → ℝ) (e : ℕ → ℝ)
    (he : ∀ k < n, 0 ≤ e k) (δ : ℝ) (b : ℕ → NNReal) (c : ℕ → ℝ)
    (hW : ∀ s ≤ T, |G s -
      ∑ i ∈ Finset.range m, c i * (if b i ≤ s then (1:ℝ) else 0)| ≤ δ) :
    |(∑ k ∈ Finset.range n, G (u k) * e k) -
      (∑ i ∈ Finset.range m, c i *
        (∑ k ∈ Finset.range n, (if b i ≤ u k then (1:ℝ) else 0) * e k))| ≤
        δ * ∑ k ∈ Finset.range n, e k := by
  have hsum : (∑ i ∈ Finset.range m, c i *
      (∑ k ∈ Finset.range n, (if b i ≤ u k then (1:ℝ) else 0) * e k)) =
      ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range m,
        c i * (if b i ≤ u k then (1:ℝ) else 0)) * e k := by
    calc
      _ = ∑ i ∈ Finset.range m, ∑ k ∈ Finset.range n,
        c i * ((if b i ≤ u k then (1:ℝ) else 0) * e k) := by
          simp only [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range m,
        (c i * (if b i ≤ u k then (1:ℝ) else 0)) * e k := by
          rw [Finset.sum_comm]
          simp only [mul_assoc]
      _ = _ := by simp only [Finset.sum_mul]
  rw [hsum,← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  exact Kyprianou.Ch04.ito43_qv_weight_approximation_bound (Finset.range n)
    (fun k => G (u k)) (fun k => ∑ i ∈ Finset.range m,
      c i * (if b i ≤ u k then (1:ℝ) else 0)) e δ
    (fun k hk => he k (Finset.mem_range.mp hk))
    (fun k hk => hW (u k) (hu k (Finset.mem_range.mp hk)))
