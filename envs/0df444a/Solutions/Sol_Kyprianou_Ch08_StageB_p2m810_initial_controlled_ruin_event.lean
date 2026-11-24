-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_initial_controlled_ruin_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:16:24.07566+00:00
-- url     : https://prove2.me/submissions/9c4a6069-c292-4152-8346-a1eef4b87c51

import Theorems.Thm_stageB_reflect_eq
import Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_piecewise
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact first-record clock reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (x a : ℝ) (ω : Ω) (t : ℝ≥0),
      0 ≤ x → x ≤ a → 0 < t →
      (a < reflectAtSup X.X x t ω ↔
        riskProcess X (a-x) (barrierStrategy X (a-x) a) t ω < 0) := by
  intro Ω mΩ P F X x a ω t hx hxa ht
  have hs := stageB_reflect_eq X t ω
  unfold reflectAtSup reflectedSup at hs
  have he : max 0 (Kyprianou.Ch08.runningSup X.X t ω) =
      AvramDividend.Classical.runningSup X t ω := by linarith
  have hm : max x (Kyprianou.Ch08.runningSup X.X t ω) =
      max x (AvramDividend.Classical.runningSup X t ω) := by
    rw [← he,← max_assoc,max_eq_left hx]
  unfold reflectAtSup
  rw [hm,riskProcess_barrier_piecewise X (a-x) a (by linarith) t ht ω,
      sub_sub_cancel]
  by_cases h : AvramDividend.Classical.runningSup X t ω < x
  · rw [if_pos h,max_eq_left h.le]
    constructor <;> intro hh <;> linarith
  · rw [if_neg h,max_eq_right (le_of_not_gt h)]
    constructor <;> intro hh <;> linarith
