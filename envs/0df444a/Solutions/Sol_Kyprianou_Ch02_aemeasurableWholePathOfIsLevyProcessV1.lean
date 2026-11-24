-- Prove2me | solution 1 for Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:21:25.979864+00:00
-- url     : https://prove2.me/submissions/10ed0eb2-769f-49d9-ad8d-738c9a7a2f89

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_cadlagWholePathAEMeasurableOfCoordinatesV1
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Recover a full path-valued almost everywhere measurable version
    from coordinate-level measurability and the common cadlag event. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    AEMeasurable (fun ω : Ω => fun t : ℝ≥0 => X t ω) P := by
  exact Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1
    P X hX.cadlag_ae
    (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX)
