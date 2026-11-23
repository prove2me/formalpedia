-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.sourceReflectedRationalCoordinatesAEMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:35:39.302438+00:00
-- url     : https://prove2.me/submissions/1f21d9d2-f28e-4099-b299-b254ce702cd2

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_sourceRunningSupRationalAEMeasurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ r : ℚ, 0 ≤ r →
      AEMeasurable
        (fun ω => reflectAtSup D.X 0 (r : ℝ).toNNReal ω) P := by
  intro r hr
  let t : ℝ≥0 := (r : ℝ).toNNReal
  have hSup : AEMeasurable (fun ω => runningSup D.X t ω) P :=
    Kyprianou.Ch08.StageB.sourceRunningSupRationalAEMeasurable P D r hr
  have hInc := (D.levy.stationary_increments 0 t).aemeasurable_snd
  change AEMeasurable (fun ω => D.X t ω - D.X 0 ω) P at hInc
  have hX : AEMeasurable (D.X t) P := by
    simpa only [D.levy.start_zero, sub_zero] using hInc
  have hZero : AEMeasurable (fun _ : Ω => (0 : ℝ)) P :=
    aemeasurable_const
  have hMax : AEMeasurable
      (fun ω => max (0 : ℝ) (runningSup D.X t ω)) P :=
    hZero.max hSup
  have hReflect : AEMeasurable
      (fun ω => max (0 : ℝ) (runningSup D.X t ω) - D.X t ω) P :=
    hMax.sub hX
  simpa only [reflectAtSup] using hReflect
