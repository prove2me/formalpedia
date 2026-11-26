-- Prove2me | solution 1 for Kyprianou.Ch04.finiteCoefficientCrossMomentIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:40:48.895664+00:00
-- url     : https://prove2.me/submissions/329eeca9-5163-45d9-ba9a-488ec462037e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false
universe u v w

/-- Integrate a finite sum of coefficient cross moments against fixed real weights. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} [DecidableEq ι]
    (P : Measure Ω) (s : Finset ι)
    (H : ι → Ω → ℝ) (c : ι → ι → ℝ)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (H i) P)
    (h2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    (∫ ω, ∑ i ∈ s, ∑ j ∈ s, (H i ω * H j ω) * c i j ∂P) =
      ∑ i ∈ s, ∑ j ∈ s, (∫ ω, H i ω * H j ω ∂P) * c i j := by
  have hp (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Integrable (fun ω => (H i ω * H j ω) * c i j) P :=
    (Kyprianou.Ch04.integrableProductOfSquareIntegrable P (H i) (H j)
      (hm i hi) (hm j hj) (h2 i hi) (h2 j hj)).mul_const _
  rw [integral_finsetSum s (fun i hi => integrable_finsetSum s (hp i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (hp i hi)]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_mul_const _ _
