-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42AvramIsLevyProcessV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:46:26.012963+00:00
-- url     : https://prove2.me/submissions/87442cf9-1160-444f-9b9f-3eda2676b2a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_exercise42AvramIndependentIncrementsV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The original Avram source is a LeanLevy process on the same space. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    IsLevyProcess L.X P := by
  refine ⟨funext L.X_zero, Kyprianou.Ch04.exercise42AvramIndependentIncrementsV1 P F L, ?_, ?_⟩
  · intro s h
    change IdentDistrib (fun ω => L.X (s+h) ω - L.X s ω) (fun ω => L.X h ω - L.X 0 ω) P P
    simpa only [increment, zero_add, L.X_zero, sub_zero, add_tsub_cancel_left] using
      L.stationaryIncrements s (s + h) (le_add_of_nonneg_right (zero_le : 0 ≤ h))
  · filter_upwards with ω t
    refine ⟨L.rightCont ω t, ?_⟩
    by_cases ht : 0 < t
    · exact L.leftLim ω t ht
    · have h0 : t = 0 := le_antisymm (le_of_not_gt ht) (zero_le : 0 ≤ t)
      subst t
      refine ⟨0, ?_⟩
      simp
