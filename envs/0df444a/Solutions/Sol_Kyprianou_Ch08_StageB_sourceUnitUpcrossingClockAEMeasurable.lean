-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.sourceUnitUpcrossingClockAEMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:36:25.874522+00:00
-- url     : https://prove2.me/submissions/deb5b9b3-4d7f-47ca-968d-6206f2a602bc

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_clocks_aemeasurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    AEMeasurable (fun ω => (tauPlus D.X 1 ω : ℝ≥0∞)) P := by
  have h :=
    (Kyprianou.Ch08.StageB.source_result81_strict_exit_clocks_aemeasurable
      Ω P D 0 1).1
  have hshift : shifted D.X 0 = D.X := by
    funext t ω
    simp [shifted]
  simpa only [hshift] using h
