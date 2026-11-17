-- Prove2me | solution 1 for Kyprianou.Ch01.isLevyProcess_of_isPreBrownianReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:17:17.812204+00:00
-- url     : https://prove2.me/submissions/59c6714d-1394-4ba4-b83e-7b0d6e49cab2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_mathlibIndepIncrements_toLeanLevy
import Theorems.Thm_Kyprianou_Ch01_mathlibBrownianStationarity_toLeanLevy
import Theorems.Thm_Continuous_isCadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal X P)
    (hzero : X 0 = fun _ => 0)
    (hcontinuous : ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ≥0 => X t ω)) :
    IsLevyProcess X P := by
  refine ⟨hzero, ?_, ?_, ?_⟩
  · exact Kyprianou.Ch01.mathlibIndepIncrements_toLeanLevy
      P X hB.hasIndepIncrements
  · exact Kyprianou.Ch01.mathlibBrownianStationarity_toLeanLevy
      P X hB
  · filter_upwards [hcontinuous] with omega hcont
    exact hcont.isCadlag
