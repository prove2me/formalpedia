-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_avram_upper_shifted_clock_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:46:27.288041+00:00
-- url     : https://prove2.me/submissions/44097bf7-c305-4275-a0bf-bdaf9ef821e0

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
/-- Upper passage clock of the shifted Avram path. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 mΩ)
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
    ∀ ω : Ω,
      (tauPlus (shifted X.X x) a ω : ℝ≥0∞) =
        AvramDividend.Classical.twoSidedExitUpTime X (a - x) ω := by
  intro Ω mΩ P hP F X a x ha hx hxa ω
  have hr : ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => x + X.X s ω) (Ici t) t := by
    intro t
    exact continuous_const.continuousWithinAt.add (X.rightCont ω t)
  have h := source_result81_positive_open_clock_eq_all_times
    (fun s : ℝ≥0 => x + X.X s ω) (Ioi (a : ℝ)) isOpen_Ioi hr
  have he (u : ℝ≥0) : a < x + X.X u ω ↔ a - x < X.X u ω := by
    constructor <;> intro hh <;> linarith
  change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0,
      0 < u ∧ (u : ℝ≥0∞) = t ∧ a < x + X.X u ω} =
    ⨅ (u : ℝ≥0) (_ : a - x < X.X u ω), (u : ℝ≥0∞)
  simpa only [mem_Ioi, he, AvramDividend.Classical.twoSidedExitUpTime] using h
