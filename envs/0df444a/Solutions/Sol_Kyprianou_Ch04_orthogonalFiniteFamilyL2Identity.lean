-- Prove2me | solution 1 for Kyprianou.Ch04.orthogonalFiniteFamilyL2Identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:54:24.832485+00:00
-- url     : https://prove2.me/submissions/169f5fd7-262f-43c5-84b7-b1ca24570d65

import Mathlib
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
universe u v

/-- Orthogonal square-integrable finite families satisfy a second-moment sum identity. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (Z : ι → Ω → ℝ)
    (hprod : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => Z i ω * Z j ω) P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∫ ω, Z i ω * Z j ω ∂P = 0) :
    ∫ ω, (∑ i ∈ s, Z i ω) ^ 2 ∂P =
      ∑ i ∈ s, ∫ ω, (Z i ω) ^ 2 ∂P := by
  have hexpand (ω : Ω) :
      (∑ i ∈ s, Z i ω) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, Z i ω * Z j ω := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  calc
    ∫ ω, (∑ i ∈ s, Z i ω) ^ 2 ∂P =
        ∫ ω, ∑ i ∈ s, ∑ j ∈ s, Z i ω * Z j ω ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact hexpand ω
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω, Z i ω * Z j ω ∂P := by
      rw [integral_finsetSum s (by
        intro i hi
        exact integrable_finsetSum s (fun j hj => hprod i hi j hj))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum s (fun j hj => hprod i hi j hj)
    _ = ∑ i ∈ s, ∫ ω, (Z i ω) ^ 2 ∂P := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp only [pow_two]
      · intro j hj hji
        exact horth i hi j hj (Ne.symm hji)
      · intro hni
        exact (hni hi).elim
