-- Prove2me | solution 1 for Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:29:31.461728+00:00
-- url     : https://prove2.me/submissions/c48aebbc-cda6-4173-9e73-9548e17b4324

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Every subwindow integral is the exact finite sum over the original marked atoms. -/
theorem solution (R : Measure (ℝ × ℝ)) (D : Set (ℝ × ℝ))
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hR : R.restrict D = ∑ t ∈ S, Measure.dirac ((t : ℝ),j t))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (g : ℝ × ℝ → ℝ) :
    (∫ z in A, g z ∂ R) =
      ∑ t ∈ S, if ((t : ℝ),j t) ∈ A then g ((t : ℝ),j t) else 0 := by
  classical
  have he : (R.restrict D).restrict A = R.restrict A := by
    rw [Measure.restrict_restrict hA,inter_eq_left.mpr hAD]
  rw [← he,hR,← integral_indicator hA]
  rw [integral_finsetSum_measure (fun t _ => integrable_dirac (by simp))]
  apply Finset.sum_congr rfl
  intro t ht
  rw [integral_dirac,Set.indicator_apply]
