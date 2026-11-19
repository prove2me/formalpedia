-- Prove2me | solution 2 for Kyprianou.Ch01.finiteGridOptionalStoppingEventwisePublic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:40:57.145525+00:00
-- url     : https://prove2.me/submissions/ec12c87a-e9bf-4d3c-b7b1-2b0ad1c20db6

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset
open scoped BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω)
    (M : ℕ → Ω → ℝ) (τ : Ω → ℕ) (N : ℕ)
    (hF : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (hBound : ∀ ω, τ ω ≤ N)
    (hInt : ∀ n, Integrable (M n) P)
    (hStop : ∀ n, n < N →
      @MeasurableSet Ω (F n) {ω | n < τ ω})
    (hMart : ∀ (n : ℕ) (A : Set Ω),
      @MeasurableSet Ω (F n) A →
      (∫ ω in A, M (n + 1) ω ∂P) =
        (∫ ω in A, M n ω ∂P)) :
    Integrable (fun ω => M (τ ω) ω) P ∧
      (∫ ω, M (τ ω) ω ∂P) =
        (∫ ω, M 0 ω ∂P) := by
  set D : ℕ → Ω → ℝ := fun n => {ω | n < τ ω}.indicator (fun ω => M (n + 1) ω - M n ω) with hD
  have hrep : (fun ω => M (τ ω) ω) = fun ω => M 0 ω + ∑ n ∈ range N, D n ω := by
    funext ω
    have h1 : ∑ n ∈ range N, D n ω = ∑ n ∈ range (τ ω), (M (n + 1) ω - M n ω) := by
      simp only [hD, Set.indicator_apply, Set.mem_ofPred_eq]
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨lt_of_lt_of_le h (hBound ω), h⟩
    rw [h1, Finset.sum_range_sub (fun n => M n ω)]
    ring
  have hS : ∀ n, n < N → MeasurableSet {ω | n < τ ω} := fun n hn => hF n _ (hStop n hn)
  have hDint : ∀ n ∈ range N, Integrable (D n) P := by
    intro n hn
    exact ((hInt (n + 1)).sub (hInt n)).indicator (hS n (Finset.mem_range.mp hn))
  have hDzero : ∀ n ∈ range N, ∫ ω, D n ω ∂P = 0 := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    simp only [hD]
    rw [integral_indicator (hS n hn'),
      integral_sub (hInt (n + 1)).integrableOn (hInt n).integrableOn,
      hMart n _ (hStop n hn'), sub_self]
  have hsumint : Integrable (fun ω => ∑ n ∈ range N, D n ω) P := integrable_finsetSum _ hDint
  refine ⟨?_, ?_⟩
  · rw [hrep]; exact (hInt 0).add hsumint
  · rw [hrep, integral_add (hInt 0) hsumint, integral_finsetSum _ hDint,
      Finset.sum_eq_zero hDzero, add_zero]
