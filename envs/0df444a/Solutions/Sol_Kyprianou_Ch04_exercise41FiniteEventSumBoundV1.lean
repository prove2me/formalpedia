-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteEventSumBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:55.589856+00:00
-- url     : https://prove2.me/submissions/3a37894f-ec07-4cea-9382-0e6ecc52a5a3

import Mathlib

open MeasureTheory Set
open scoped ENNReal BigOperators
set_option autoImplicit false

/-- Sum the lower bounds for success probabilities over cells and integrate the pointwise bound of two on the finite sum of successful-cell indicators. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (I : Finset ℕ) (A B : ℕ → Set Ω) (p : ℝ≥0∞)
    (hB : ∀ i ∈ I, MeasurableSet (B i))
    (hfactor : ∀ i ∈ I, p * P (A i) ≤ P (B i))
    (hbound : ∀ ω, ∑ i ∈ I,
      (B i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω ≤ 2) :
    p * ∑ i ∈ I, P (A i) ≤ 2 := by
  classical
  calc
    _ = ∑ i ∈ I, p * P (A i) := Finset.mul_sum ..
    _ ≤ ∑ i ∈ I, P (B i) := Finset.sum_le_sum hfactor
    _ = ∫⁻ ω, ∑ i ∈ I, (B i).indicator
          (fun _ : Ω => (1 : ℝ≥0∞)) ω ∂P := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [lintegral_indicator (hB i hi)]
        simp
      · intro i hi
        have hm : Measurable (fun _ : Ω => (1 : ℝ≥0∞)) := measurable_const
        exact hm.indicator (hB i hi)
    _ ≤ ∫⁻ _ : Ω, (2 : ℝ≥0∞) ∂P := lintegral_mono hbound
    _ = 2 := by simp
