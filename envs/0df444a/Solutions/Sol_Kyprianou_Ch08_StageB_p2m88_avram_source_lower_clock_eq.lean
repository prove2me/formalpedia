-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_avram_source_lower_clock_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:08:13.168598+00:00
-- url     : https://prove2.me/submissions/8b0aa651-bc6e-4a4c-acb2-85f877772ecc

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact source clock reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F)
      (x : ℝ) (ω : Ω),
      (tauMinus (shifted X.X x) 0 ω : ℝ≥0∞) =
        AvramDividend.Classical.twoSidedExitDownTime X (-x) ω := by
  intro Ω mΩ P F X x ω
  have hr : ∀ t : ℝ≥0, ContinuousWithinAt (fun s => x + X.X s ω) (Ici t) t :=
    fun t => continuous_const.continuousWithinAt.add (X.rightCont ω t)
  have h := source_result81_positive_open_clock_eq_all_times
    (fun s : ℝ≥0 => x + X.X s ω) (Iio (0 : ℝ)) isOpen_Iio hr
  have he (u : ℝ≥0) : x + X.X u ω < 0 ↔ X.X u ω < -x := by
    constructor <;> intro hh <;> linarith
  change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = t ∧
      x + X.X u ω < 0} =
    ⨅ (u : ℝ≥0) (_ : X.X u ω < -x), (u : ℝ≥0∞)
  simpa only [mem_Iio, he] using h
