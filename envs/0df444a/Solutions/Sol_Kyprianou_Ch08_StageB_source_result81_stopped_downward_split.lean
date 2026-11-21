-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_stopped_downward_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T13:17:39.838181+00:00
-- url     : https://prove2.me/submissions/f55e288a-c3e3-42a6-8a82-a6074bb2c99f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_no_positive_jumps
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_restart_payoff_split
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_restart_payoff_factor
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (q x a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hxa : x ≤ a) :
    downExpectation P D.X q x =
      downBeforeUpExpectation P D.X q x a +
        upBeforeDownExpectation P D.X q x a * downExpectation P D.X q a := by
  obtain ⟨hLower, hRestart, hFactor⟩ := source_result81_restart_payoff_factor Ω P D q x a hq ha hxa
  have hSplit := source_result81_restart_payoff_split Ω P D
    (source_result81_no_positive_jumps Ω P D) q x a hq ha hxa
  have hsum := integral_congr_ae hSplit
  rw [integral_add hLower hRestart, hFactor] at hsum
  exact hsum
