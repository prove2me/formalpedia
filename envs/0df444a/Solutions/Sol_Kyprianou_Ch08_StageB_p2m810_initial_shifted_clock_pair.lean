-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_initial_shifted_clock_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:13:29.705395+00:00
-- url     : https://prove2.me/submissions/76dfd007-c11e-4820-b8c5-d9d8b1e88269

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Initial source clock pair. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (x a : ℝ) (ω : Ω),
      (tauPlus (shifted X.X (a-x)) a ω : ℝ≥0∞) = twoSidedExitUpTime X x ω ∧
      (tauMinus (shifted X.X (a-x)) 0 ω : ℝ≥0∞) = twoSidedExitDownTime X (x-a) ω := by
  intro Ω mΩ P F X x a ω
  have hr : ∀ t : ℝ≥0, ContinuousWithinAt (fun s => (a-x)+X.X s ω) (Ici t) t :=
    fun t => continuous_const.continuousWithinAt.add (X.rightCont ω t)
  have hu := source_result81_positive_open_clock_eq_all_times
    (fun s => (a-x)+X.X s ω) (Ioi a) isOpen_Ioi hr
  have hd := source_result81_positive_open_clock_eq_all_times
    (fun s => (a-x)+X.X s ω) (Iio (0:ℝ)) isOpen_Iio hr
  have hu' (s : ℝ≥0) : a < a-x+X.X s ω ↔ x < X.X s ω := by
    constructor <;> intro h <;> linarith
  have hd' (s : ℝ≥0) : a-x+X.X s ω < 0 ↔ X.X s ω < x-a := by
    constructor <;> intro h <;> linarith
  have hU : (tauPlus (shifted X.X (a-x)) a ω : ℝ≥0∞) =
      twoSidedExitUpTime X x ω := by
    change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧
      (u : ℝ≥0∞) = t ∧ a < a-x+X.X u ω} =
      ⨅ (u : ℝ≥0) (_ : x < X.X u ω), (u : ℝ≥0∞)
    simpa only [mem_Ioi,hu'] using hu
  have hL : (tauMinus (shifted X.X (a-x)) 0 ω : ℝ≥0∞) =
      twoSidedExitDownTime X (x-a) ω := by
    change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧
      (u : ℝ≥0∞) = t ∧ a-x+X.X u ω < 0} =
      ⨅ (u : ℝ≥0) (_ : X.X u ω < x-a), (u : ℝ≥0∞)
    simpa only [mem_Iio,hd'] using hd
  exact ⟨hU,hL⟩
