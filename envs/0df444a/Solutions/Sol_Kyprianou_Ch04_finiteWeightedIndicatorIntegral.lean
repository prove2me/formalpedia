-- Prove2me | solution 1 for Kyprianou.Ch04.finiteWeightedIndicatorIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:05:46.966947+00:00
-- url     : https://prove2.me/submissions/5b5d311f-7b71-4ed4-8c3c-e52ae21d3056

import Mathlib
open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false
universe u v

/-- Integrate a finite sum of weighted indicators of finite-measure sets. -/
theorem solution
    {A : Type u} [MeasurableSpace A] {ι : Type v} [DecidableEq ι]
    (μ : Measure A) (s : Finset ι) (B : ι → Set A) (c : ι → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, μ (B i) ≠ ⊤) :
    Integrable (fun x => ∑ i ∈ s, (B i).indicator (fun _ => c i) x) μ ∧
      (∫ x, ∑ i ∈ s, (B i).indicator (fun _ => c i) x ∂μ) =
      ∑ i ∈ s, c i * (μ (B i)).toReal := by
  have hi (i : ι) (hi : i ∈ s) :
      Integrable ((B i).indicator (fun _ : A => c i)) μ := by
    apply IntegrableOn.integrable_indicator _ (hB i hi)
    exact integrableOn_const (hFin i hi)
  refine ⟨integrable_finsetSum s hi, ?_⟩
  rw [integral_finsetSum s hi]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_indicator (hB i hi'), setIntegral_const]
  simp [smul_eq_mul, Measure.real, mul_comm]
