-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_factor_source_exit_clocks_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:52:36.891854+00:00
-- url     : https://prove2.me/submissions/10a77ceb-1a77-4aab-8e46-8bc2f46e8d24

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω) (x a : ℝ) :
    ∀ᵐ ω ∂P,
      tauPlus (shifted D.X x) a ω = twoSidedExitUpTime X (a - x) ω ∧
      tauMinus (shifted D.X x) 0 ω = twoSidedExitDownTime X (-x) ω ∧
      tauMinus (shifted D.X a) 0 ω = tauMinus (shifted X.X a) 0 ω
:= by
  filter_upwards [hpath] with ω hω
  have hr : ∀ t : ℝ≥0, ContinuousWithinAt (fun s => x + X.X s ω) (Ici t) t :=
    fun t => continuous_const.continuousWithinAt.add (X.rightCont ω t)
  refine ⟨?_, ?_, ?_⟩
  · have h := source_result81_positive_open_clock_eq_all_times
      (fun s : ℝ≥0 => x + X.X s ω) (Ioi a) isOpen_Ioi hr
    have he (u : ℝ≥0) : a < x + X.X u ω ↔ a - x < X.X u ω := by
      constructor <;> intro hh <;> linarith
    change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = t ∧
      a < x + D.X u ω} = ⨅ (u : ℝ≥0) (_ : a - x < X.X u ω), (u : ℝ≥0∞)
    simpa only [mem_Ioi, he, ← hω] using h
  · have h := source_result81_positive_open_clock_eq_all_times
      (fun s : ℝ≥0 => x + X.X s ω) (Iio 0) isOpen_Iio hr
    have he (u : ℝ≥0) : x + X.X u ω < 0 ↔ X.X u ω < -x := by
      constructor <;> intro hh <;> linarith
    change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = t ∧
      x + D.X u ω < 0} = ⨅ (u : ℝ≥0) (_ : X.X u ω < -x), (u : ℝ≥0∞)
    simpa only [mem_Iio, he, ← hω] using h
  · simp only [tauMinus, shifted, hω]
