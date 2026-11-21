-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianZeroLevelPassageRightContinuousAeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:38:44.322867+00:00
-- url     : https://prove2.me/submissions/34872feb-6677-4647-a979-b770e9e42df4

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_linearBrownianInstantUpperCrossingAeV1
import Theorems.Thm_Kyprianou_Ch01_zeroBoundaryPassageRightContinuousOfInstantCrossingV1
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    ∀ᵐ ω ∂P, ContinuousWithinAt
      (      fun u : ℝ≥0 =>
        if u = 0 then (0 : ℝ)
        else (match firstUpperPassage X (u : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))) (Ici (0 : ℝ≥0)) 0 := by
  have hCross :=
    linearBrownianInstantUpperCrossingAeV1
      P X b hb hB hMeas hContinuous
  filter_upwards [hCross] with ω hω
  exact zeroBoundaryPassageRightContinuousOfInstantCrossingV1 X ω hω
