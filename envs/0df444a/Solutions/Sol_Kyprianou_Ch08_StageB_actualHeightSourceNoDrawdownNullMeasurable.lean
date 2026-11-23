-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actualHeightSourceNoDrawdownNullMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:31:29.138241+00:00
-- url     : https://prove2.me/submissions/7e0bff79-c00f-47dd-a465-648cc8e48703
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_sourceUnitUpcrossingClockAEMeasurable
import Theorems.Thm_Kyprianou_Ch08_StageB_sourceReflectedRationalCoordinatesAEMeasurable
import Theorems.Thm_Kyprianou_Ch08_StageB_sourceReflectedPathRegularityAE
import Theorems.Thm_Kyprianou_Ch08_StageB_stoppedStrictPathEventNullMeasurable
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ h : ℝ, 0 < h →
      NullMeasurableSet
        {ω : Ω | NoDrawdownBeforeUpcrossing D.X 1 h ω} P := by
  intro h hh
  let f : ℝ≥0 → Ω → ℝ :=
    fun t ω => reflectAtSup D.X 0 t ω
  let T : Ω → WithTop ℝ≥0 := fun ω => tauPlus D.X 1 ω
  have hT : AEMeasurable T P := by
    exact Kyprianou.Ch08.StageB.sourceUnitUpcrossingClockAEMeasurable P D
  have hf : ∀ r : ℚ, 0 ≤ r →
      AEMeasurable (f (r : ℝ).toNNReal) P := by
    exact Kyprianou.Ch08.StageB.sourceReflectedRationalCoordinatesAEMeasurable P D
  have hp : ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        ContinuousWithinAt (fun s => f s ω) (Set.Ici t) t) ∧
      (∀ z : ℝ≥0,
        UpperSemicontinuousOn (fun s => f s ω) (Set.Icc 0 z)) := by
    exact Kyprianou.Ch08.StageB.sourceReflectedPathRegularityAE P D
  have hm :=
    Kyprianou.Ch08.StageB.stoppedStrictPathEventNullMeasurable
      P f T h hT hf hp
  simpa only [f, T, NoDrawdownBeforeUpcrossing] using hm
