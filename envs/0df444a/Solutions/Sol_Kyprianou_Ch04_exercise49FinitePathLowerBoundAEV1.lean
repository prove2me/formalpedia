-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49FinitePathLowerBoundAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:05:25.761154+00:00
-- url     : https://prove2.me/submissions/05dfe391-c07f-4956-99b1-a1f32709226a

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Almost surely a cadlag process tending to infinity has a bounded all-time depth. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ w, IsCadlag (fun t => X t w))
    (hInf : ∀ᵐ w ∂P, Tendsto (fun t => X t w) atTop atTop) :
    ∀ᵐ w ∂P, BddAbove (Set.range (fun t => -X t w)) := by
  filter_upwards [hInf] with w hi
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hi.eventually (eventually_ge_atTop (0 : ℝ)))
  obtain ⟨b, hb⟩ := Kyprianou.Ch03.reflectionSignedCompactBoundV1
    (fun t => X t w) (hc w) (-1) T
  refine ⟨max b 0, ?_⟩
  rintro x ⟨t, rfl⟩
  by_cases ht : t ≤ T
  · have hbt : (-1 : ℝ) * X t w ≤ b := hb ⟨t, ⟨bot_le, ht⟩, rfl⟩
    exact (by simpa using hbt : -X t w ≤ b).trans (le_max_left _ _)
  · have hpos := hT t (le_of_not_ge ht)
    exact (neg_nonpos.mpr hpos).trans (le_max_right _ _)
