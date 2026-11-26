-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41LeftZeroCountableV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:22:55.230291+00:00
-- url     : https://prove2.me/submissions/f8bbda64-5efd-4b8a-993f-cac2b23a5a5e

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_cadlagNNRealDiscontinuitiesCountableV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (T : NNReal)
    (hR : ∀ t : NNReal, ContinuousWithinAt x (Ici t) t)
    (hL : ∀ t : NNReal, 0 < t → ∃ l : ℝ,
      Tendsto x (nhdsWithin t (Iio t)) (nhds l))
    (hZ : Set.Finite {s : NNReal | 0 < s ∧ s ≤ T ∧ x s = 0}) :
    Set.Countable {s : NNReal | 0 < s ∧ s ≤ T ∧ Function.leftLim x s = 0} := by
  have hD := Kyprianou.Ch02.cadlagNNRealDiscontinuitiesCountableV1 x hR hL
  apply (hZ.countable.union hD).mono
  intro s hs
  by_cases hcont : ContinuousAt x s
  · left
    refine ⟨hs.1, hs.2.1, ?_⟩
    have he := hcont.continuousWithinAt (s := Iic s)
    rw [← he.leftLim_eq]
    exact hs.2.2
  · exact Or.inr hcont
