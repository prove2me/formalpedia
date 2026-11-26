-- Prove2me | solution 1 for Kyprianou.Ch04.finiteWeightedIndicatorExpectedSquareIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:46:28.198089+00:00
-- url     : https://prove2.me/submissions/7d8424dd-c7fa-47f1-bb8e-4d54eed4c8be

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorSquareIntegral
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false
universe u v w

/-- Expected energy of a finite random-weighted indicator sum, allowing overlaps. -/
theorem solution
    {Ω : Type u} {A : Type v} {ι : Type w}
    [MeasurableSpace Ω] [MeasurableSpace A] [DecidableEq ι]
    (P : Measure Ω) (μ : Measure A) (s : Finset ι)
    (B : ι → Set A) (H : ι → Ω → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, μ (B i) ≠ ⊤)
    (hHm : ∀ i ∈ s, AEStronglyMeasurable (H i) P)
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    (∫ ω, ∫ x, (∑ i ∈ s, (B i).indicator (fun _ => H i ω) x)^2 ∂μ ∂P) =
      ∑ i ∈ s, ∑ j ∈ s, (∫ ω, H i ω * H j ω ∂P) *
        (μ (B i ∩ B j)).toReal := by
  have hp (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Integrable (fun ω => (H i ω * H j ω) * (μ (B i ∩ B j)).toReal) P :=
    (Kyprianou.Ch04.integrableProductOfSquareIntegrable P (H i) (H j)
      (hHm i hi) (hHm j hj) (hH2 i hi) (hH2 j hj)).mul_const _
  calc
    _ = ∫ ω, ∑ i ∈ s, ∑ j ∈ s, (H i ω * H j ω) *
        (μ (B i ∩ B j)).toReal ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact Kyprianou.Ch04.finiteWeightedIndicatorSquareIntegral
        μ s B (fun i => H i ω) hB hFin
    _ = ∑ i ∈ s, ∫ ω, ∑ j ∈ s, (H i ω * H j ω) *
        (μ (B i ∩ B j)).toReal ∂P :=
      integral_finsetSum s (fun i hi => integrable_finsetSum s (fun j hj => hp i hi j hj))
    _ = _ := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [integral_finsetSum s (fun j hj => hp i hi j hj)]
      exact Finset.sum_congr rfl (fun j hj => integral_mul_const _ _)
