-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PrefixSafeFinishV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:03:04.459039+00:00
-- url     : https://prove2.me/submissions/064feb4a-b8d7-40ba-b005-f34428795a80

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49PrefixSafeMassV1
import Theorems.Thm_Kyprianou_Ch04_exercise49PositiveSurvivalRuinBoundV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A positive survival event gives a strictly subunit ruin probability. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (s : NNReal) (b : ℝ)
    (hA : 0 < P {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω})
    (hB : 0 < P {ω | ∀ u : NNReal, -b ≤ X u ω}) :
    (P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤}).toReal < 1 := by
  exact Kyprianou.Ch04.exercise49PositiveSurvivalRuinBoundV1 P X hX hm hc
    (Kyprianou.Ch04.exercise49PrefixSafeMassV1 P X hX hm hc s b hA hB)
