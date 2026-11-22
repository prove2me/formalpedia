-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFirstPassageZeroBoundaryIsLevyProcessPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:07:47.192957+00:00
-- url     : https://prove2.me/submissions/b1368a73-d21c-4293-a973-90174ed1b484

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryIndependentIncrementsV1
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryStationaryIncrementsV1
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryCadlagV1
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open scoped Classical
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    ProbabilityTheory.IsLevyProcess T P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext ω
    simp
  · exact Kyprianou.Ch01.inverseGaussianZeroBoundaryIndependentIncrementsV1
      P X b hb hB hMeas hContinuous
  · exact Kyprianou.Ch01.inverseGaussianZeroBoundaryStationaryIncrementsV1
      P X b hb hB hMeas hContinuous
  · exact Kyprianou.Ch01.inverseGaussianZeroBoundaryCadlagV1
      P X b hb hB hMeas hContinuous
