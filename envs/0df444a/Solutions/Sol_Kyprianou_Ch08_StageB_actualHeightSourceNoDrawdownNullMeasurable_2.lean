-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.actualHeightSourceNoDrawdownNullMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:16:38.732211+00:00
-- url     : https://prove2.me/submissions/9d24b25c-431a-4ca9-a0a3-05c93e067daa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_stoppedStrictPathEventNullMeasurable
import Theorems.Thm_Kyprianou_Ch08_StageB_sourceUnitUpcrossingClockAEMeasurable
import Theorems.Thm_Kyprianou_Ch08_StageB_sourceReflectedRationalCoordinatesAEMeasurable
import Theorems.Thm_Kyprianou_Ch08_StageB_sourceReflectedPathRegularityAE
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ h : ℝ, 0 < h →
      NullMeasurableSet
        {ω : Ω | NoDrawdownBeforeUpcrossing D.X 1 h ω} P := by
  intro h hh
  change NullMeasurableSet
    {ω : Ω | ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) < tauPlus D.X 1 ω →
        reflectAtSup D.X 0 t ω < h} P
  exact Kyprianou.Ch08.StageB.stoppedStrictPathEventNullMeasurable
    P (fun t ω => reflectAtSup D.X 0 t ω)
      (fun ω => tauPlus D.X 1 ω) h
    (by simpa using
      Kyprianou.Ch08.StageB.sourceUnitUpcrossingClockAEMeasurable P D)
    (Kyprianou.Ch08.StageB.sourceReflectedRationalCoordinatesAEMeasurable P D)
    (Kyprianou.Ch08.StageB.sourceReflectedPathRegularityAE P D)
