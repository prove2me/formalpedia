-- Prove2me | solution 1 for MasulloRH.finite_cutoff_cross_correlation
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T01:21:42.44866+00:00
-- url     : https://prove2.me/submissions/2001f37e-53dc-4ae0-80b9-bbaa2df76a04

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

open Finset

theorem solution :
    let corr (u v : ℤ →₀ ℝ) : ℤ →₀ ℝ :=
      ∑ i ∈ u.support, ∑ k ∈ v.support, Finsupp.single (k-i) (u i * v k)
    (∀ (a b : ℤ →₀ ℝ) (f : ℤ → ℝ),
      (∑ j ∈ (corr a b).support, corr a b j * f j) =
        ∑ i ∈ a.support, ∑ k ∈ b.support, (a i * b k) * f (k-i)) ∧
    (∀ a b : ℤ →₀ ℝ, (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
      (∑ i ∈ a.support, a i) = 1 → (∑ i ∈ b.support, b i) = 1 →
      (∀ j, 0 ≤ corr a b j) ∧ (∑ j ∈ (corr a b).support, corr a b j) = 1) ∧
    (∀ (a b : ℤ →₀ ℝ) (j : ℤ), corr b a j = corr a b (-j)) ∧
    (∀ r : ℤ, corr (Finsupp.single 0 1) (Finsupp.single r 1) = Finsupp.single r 1) := by
  classical
  intro corr
  have push (a b : ℤ →₀ ℝ) (f : ℤ → ℝ) :
      (∑ j ∈ (corr a b).support, corr a b j * f j) =
        ∑ i ∈ a.support, ∑ k ∈ b.support, (a i*b k)*f (k-i) := by
    let weight : (ℤ →₀ ℝ) →+ ℝ :=
      { toFun := fun u => u.sum fun j x => x*f j
        map_zero' := by simp
        map_add' := fun u v => Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul ..) }
    have hw (i : ℤ) (w : ℝ) : weight (Finsupp.single i w) = w*f i := by
      change (Finsupp.single i w).sum (fun j x => x*f j) = w*f i
      exact Finsupp.sum_single_index (zero_mul _)
    change weight (corr a b) = _
    simp only [corr, map_sum, hw]
  have coeff (a b : ℤ →₀ ℝ) (j : ℤ) :
      corr a b j = ∑ i ∈ a.support, ∑ k ∈ b.support, if k-i=j then a i * b k else 0 := by
    simp only [corr, Finsupp.finsetSum_apply, Finsupp.single_apply]
  refine ⟨push, ?_, ?_, ?_⟩
  · intro a b ha hb hma hmb
    constructor
    · intro j
      rw [coeff]
      refine sum_nonneg fun i _ => sum_nonneg fun k _ => ?_
      split_ifs
      · exact mul_nonneg (ha i) (hb k)
      · exact le_rfl
    · simpa only [mul_one, ←mul_sum, hmb, hma] using push a b (fun _ => 1)
  · intro a b j
    rw [coeff, coeff, sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro k _
    have he : i-k=j ↔ k-i= -j := by omega
    simp only [he, mul_comm]
  · intro r
    simp [corr]
