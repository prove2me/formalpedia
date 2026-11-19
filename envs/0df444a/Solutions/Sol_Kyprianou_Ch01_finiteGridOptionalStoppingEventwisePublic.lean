-- Prove2me | solution 1 for Kyprianou.Ch01.finiteGridOptionalStoppingEventwisePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:38:20.10588+00:00
-- url     : https://prove2.me/submissions/566e25f5-7f81-4e95-880b-09b21f07a419

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

private theorem finiteGridPointwiseTelescoping
    {Ω : Type*} (M : ℕ → Ω → ℝ) (τ : Ω → ℕ) (N : ℕ)
    (hBound : ∀ ω, τ ω ≤ N) (ω : Ω) :
    M (τ ω) ω = M 0 ω +
      ∑ n ∈ Finset.range N,
        if n < τ ω then M (n + 1) ω - M n ω else 0 := by
  let f : ℕ → ℝ := fun n => if n < τ ω then M (n + 1) ω - M n ω else 0
  have hs (n : ℕ) : (∑ k ∈ Finset.range n, f k) = M (min n (τ ω)) ω - M 0 ω := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]; by_cases hh : n < τ ω
      · have hn : min n (τ ω) = n := min_eq_left hh.le
        have hsn : min (n + 1) (τ ω) = n + 1 := min_eq_left (Nat.succ_le_of_lt hh)
        simp only [f, if_pos hh, hn, hsn]; ring
      · have hn : min n (τ ω) = τ ω := min_eq_right (Nat.le_of_not_gt hh)
        have hsn : min (n + 1) (τ ω) = τ ω :=
          min_eq_right (Nat.le_trans (Nat.le_of_not_gt hh) (Nat.le_succ n))
        simp only [f, if_neg hh, hn, hsn, add_zero]
  have ht := hs N; rw [min_eq_right (hBound ω)] at ht
  change (∑ k ∈ Finset.range N, if k < τ ω then
    M (k+1) ω - M k ω else 0) = M (τ ω) ω - M 0 ω at ht
  linarith

private theorem finiteGridTermIntegrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : ℕ → Ω → ℝ) (τ : Ω → ℕ) (n : ℕ)
    (h0 : Integrable (M n) P) (h1 : Integrable (M (n+1)) P)
    (hm : MeasurableSet {ω : Ω | n < τ ω}) :
    Integrable (fun ω => if n < τ ω then
      M (n+1) ω - M n ω else 0) P := by
  have h : Integrable (Set.indicator {ω : Ω | n < τ ω}
      (fun ω => M (n+1) ω - M n ω)) P := (h1.sub h0).indicator hm
  have heq : (fun ω => if n < τ ω then M (n+1) ω - M n ω else 0) =
      Set.indicator {ω : Ω | n < τ ω} (fun ω => M (n+1) ω - M n ω) := by
    funext ω; by_cases hw : n < τ ω <;> simp [Set.indicator, hw]
  rw [heq]; exact h

private theorem finiteGridStepIntegralZero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : ℕ → Ω → ℝ) (τ : Ω → ℕ) (n : ℕ)
    (h0 : Integrable (M n) P) (h1 : Integrable (M (n+1)) P)
    (hm : MeasurableSet {ω : Ω | n < τ ω})
    (heq : (∫ ω in {ω : Ω | n < τ ω}, M (n+1) ω ∂P) =
      (∫ ω in {ω : Ω | n < τ ω}, M n ω ∂P)) :
    (∫ ω, if n < τ ω then M (n+1) ω - M n ω else 0 ∂P) = 0 := by
  let A : Set Ω := {ω | n < τ ω}
  have h0A := h0.mono_measure (Measure.restrict_le_self (μ := P) (s := A))
  have h1A := h1.mono_measure (Measure.restrict_le_self (μ := P) (s := A))
  have h : (∫ ω, A.indicator (fun ω => M (n+1) ω - M n ω) ω ∂P) = 0 := by
    rw [integral_indicator hm, integral_sub h1A h0A, heq]; ring
  convert h using 1
  congr 1; funext ω
  by_cases hw : n < τ ω <;> simp [A, Set.indicator, hw]

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
  let f : ℕ → Ω → ℝ := fun n ω => if n < τ ω then M (n + 1) ω - M n ω else 0
  have hmeas (n : ℕ) (hn : n < N) : MeasurableSet {ω : Ω | n < τ ω} :=
    (hF n) _ (hStop n hn)
  have hfint (n : ℕ) (hn : n < N) : Integrable (f n) P :=
    finiteGridTermIntegrable P M τ n (hInt n) (hInt (n+1)) (hmeas n hn)
  have hpoint (ω : Ω) : M (τ ω) ω = M 0 ω + ∑ k ∈ Finset.range N, f k ω :=
    finiteGridPointwiseTelescoping M τ N hBound ω
  have hstep (n : ℕ) (hn : n < N) : (∫ ω, f n ω ∂P) = 0 :=
    finiteGridStepIntegralZero P M τ n (hInt n) (hInt (n+1))
      (hmeas n hn) (hMart n _ (hStop n hn))
  have hsumInt : Integrable (fun ω => ∑ k ∈ Finset.range N, f k ω) P :=
    integrable_finset_sum _ (fun n hn => hfint n (Finset.mem_range.mp hn))
  have hτInt : Integrable (fun ω => M (τ ω) ω) P := by
    have heq : (fun ω => M (τ ω) ω) =
        (fun ω => M 0 ω + ∑ k ∈ Finset.range N, f k ω) := by
      funext ω; exact hpoint ω
    rw [heq]; exact (hInt 0).add hsumInt
  refine ⟨hτInt, ?_⟩
  calc
      (∫ ω, M (τ ω) ω ∂P) =
          ∫ ω, (M 0 ω + ∑ k ∈ Finset.range N, f k ω) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω; exact hpoint ω
      _ = (∫ ω, M 0 ω ∂P) +
          (∫ ω, ∑ k ∈ Finset.range N, f k ω ∂P) := by
            rw [integral_add (hInt 0) hsumInt]
      _ = (∫ ω, M 0 ω ∂P) := by
            rw [integral_finset_sum _ (fun n hn =>
              hfint n (Finset.mem_range.mp hn))]
            simp only [Finset.sum_eq_zero (fun n hn =>
              hstep n (Finset.mem_range.mp hn)), add_zero]
