-- Prove2me | solution 1 for NisanRonen.Rounding.rounding_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:16:15.336932+00:00
-- url     : https://prove2.me/submissions/3bcb67c2-b90b-4a93-99f3-a8fbe27796f0

import Mathlib
import Definitions.Def_NisanRonen_Rounding_roundedMakespan

open NisanRonen.Rounding in
theorem solution {n k : ℕ} [NeZero n] {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (x : Fin k → Fin n) (τ : Fin k → ℝ) (hτ : ∀ j, a ≤ τ j) :
    makespan x τ ≤ roundedMakespan δ x τ ∧
      roundedMakespan δ x τ ≤ (1 + δ / a) * makespan x τ := by
  have hru : ∀ v, v ≤ roundUp δ v ∧ roundUp δ v ≤ v + δ := by
    intro v
    unfold roundUp
    have h1 := Int.le_ceil (v / δ)
    have h2 := Int.ceil_lt_add_one (v / δ)
    have e : δ * (v / δ) = v := mul_div_cancel₀ v hδ.ne'
    constructor
    · calc v = δ * (v / δ) := e.symm
        _ ≤ δ * (⌈v / δ⌉ : ℝ) := mul_le_mul_of_nonneg_left h1 hδ.le
    · calc δ * (⌈v / δ⌉ : ℝ) ≤ δ * (v / δ + 1) := mul_le_mul_of_nonneg_left h2.le hδ.le
        _ = v + δ := by rw [mul_add, e, mul_one]
  have hτ' : ∀ j, roundUp δ (τ j) ≤ (1 + δ / a) * τ j := by
    intro j
    have h1 := (hru (τ j)).2
    have h3 : δ ≤ δ / a * τ j := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      exact mul_le_mul_of_nonneg_left (hτ j) hδ.le
    nlinarith
  have hload1 : ∀ i, load x τ i ≤ load x (fun j => roundUp δ (τ j)) i := by
    intro i
    unfold load
    exact Finset.sum_le_sum (fun j _ => (hru (τ j)).1)
  have hload2 : ∀ i, load x (fun j => roundUp δ (τ j)) i ≤ (1 + δ / a) * load x τ i := by
    intro i
    unfold load
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hτ' j)
  have hc : 0 ≤ 1 + δ / a := by positivity
  constructor
  · unfold roundedMakespan makespan
    exact Finset.sup'_le _ _ (fun i _ => Finset.le_sup'_of_le _ (Finset.mem_univ i) (hload1 i))
  · unfold roundedMakespan makespan
    apply Finset.sup'_le
    intro i _
    exact (hload2 i).trans (mul_le_mul_of_nonneg_left (Finset.le_sup' _ (Finset.mem_univ i)) hc)
