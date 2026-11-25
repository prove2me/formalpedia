-- Prove2me | solution 1 for Kyprianou.Ch04.pathJumpMeasureZeroTimeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:17:40.19068+00:00
-- url     : https://prove2.me/submissions/b97b2eca-541d-41b7-b323-39c3255aded5

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The intrinsic path jump measure has no mark at time zero. -/
theorem solution {Ω : Type} (X Xleft : NNReal → Ω → ℝ) (ω : Ω) :
    Kyprianou.Ch04.pathJumpMeasure X Xleft ω
      (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
  let S : Set NNReal := {t | 0 < t ∧ X t ω ≠ Xleft t ω}
  let m := (Measure.count : Measure NNReal).restrict S
  let g : NNReal → ℝ × ℝ := fun t => (↑t, X t ω - Xleft t ω)
  change Measure.map g m (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0
  by_cases hg : AEMeasurable g m
  · rw [Measure.map_apply_of_aemeasurable hg
      ((measurableSet_singleton _).prod MeasurableSet.univ)]
    have heq : g ⁻¹' (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = {0} := by
      ext t
      simp [g, NNReal.coe_eq_zero]
    change m (g ⁻¹' (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))) = 0
    rw [heq]
    change ((Measure.count : Measure NNReal).restrict S) {0} = 0
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    have hS : ({0} : Set NNReal) ∩ S = ∅ := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, S,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, h, _⟩
      exact (lt_irrefl _ h)
    rw [hS, measure_empty]
  · rw [Measure.map_of_not_aemeasurable hg]
    simp
