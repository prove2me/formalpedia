-- Prove2me | solution 1 for Kyprianou.Ch04.finiteWeightedIndicatorSquareIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:38:35.455085+00:00
-- url     : https://prove2.me/submissions/56ce56de-4955-4ae7-9b80-6a80babf6639

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteFamilyCovarianceExpansion
open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false
universe u v

/-- The energy of an arbitrary finite weighted indicator sum is the overlap sum. -/
theorem solution
    {A : Type u} [MeasurableSpace A] {ι : Type v} [DecidableEq ι]
    (μ : Measure A) (s : Finset ι) (B : ι → Set A) (c : ι → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, μ (B i) ≠ ⊤) :
    (∫ x, (∑ i ∈ s, (B i).indicator (fun _ => c i) x)^2 ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * c j) * (μ (B i ∩ B j)).toReal := by
  classical
  let Z := fun i => (B i).indicator (fun _ : A => c i)
  have he (i j : ι) : (fun x => Z i x * Z j x) =
      (B i ∩ B j).indicator (fun _ => c i * c j) := by
    funext x
    by_cases hi : x ∈ B i <;> by_cases hj : x ∈ B j <;>
      simp [Z, hi, hj]
  have hp (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Integrable (fun x => Z i x * Z j x) μ := by
    rw [he]
    exact IntegrableOn.integrable_indicator
      (integrableOn_const (ne_top_of_le_ne_top (hFin i hi)
        (measure_mono Set.inter_subset_left))) ((hB i hi).inter (hB j hj))
  change (∫ x, (∑ i ∈ s, Z i x)^2 ∂μ) = _
  rw [Kyprianou.Ch04.finiteFamilyCovarianceExpansion μ s Z hp]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [he, integral_indicator ((hB i hi).inter (hB j hj)), setIntegral_const]
  simp [smul_eq_mul, Measure.real, mul_comm]
