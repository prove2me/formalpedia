-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_filtered_record_weight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:18:43.025909+00:00
-- url     : https://prove2.me/submissions/c5b72bc7-25b2-4232-8981-34661e288f0c

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_initial_shifted_clock_pair
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Identify the initial stopped weight with the exact source payoff. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
      (X : SpectrallyNegativeLevy P F) (q x a : ℝ),
      0 ≤ q → 0 < x → x ≤ a →
      (∫ ω, if twoSidedExitUpTime X x ω < twoSidedExitDownTime X (x-a) ω
        then Real.exp (-q*((twoSidedExitUpTime X x ω).toNNReal:ℝ)) else 0 ∂P) =
      upBeforeDownExpectation P X.X q (a-x) a := by
  intro Ω mΩ P hP F X q x a hq hx hxa
  unfold upBeforeDownExpectation
  apply integral_congr_ae
  filter_upwards with ω
  obtain ⟨hU,hL⟩ := p2m810_initial_shifted_clock_pair Ω P F X x a ω
  rw [← hU,← hL]
  let U : ℝ≥0∞ := tauPlus (shifted X.X (a-x)) a ω
  let L : ℝ≥0∞ := tauMinus (shifted X.X (a-x)) 0 ω
  change (if U < L then Real.exp (-q*(U.toNNReal:ℝ)) else 0) =
    (if (U:WithTop ℝ≥0) < (L:WithTop ℝ≥0) then discountedAt q U else 0)
  by_cases h : U < L
  · have he : (U:WithTop ℝ≥0) < (L:WithTop ℝ≥0) := h
    simp only [if_pos h,if_pos he]
    have hf : U ≠ ⊤ := ne_of_lt (h.trans_le le_top)
    cases hcase : U with
    | top => exact (hf hcase).elim
    | coe t => rfl
  · have he : ¬ (U:WithTop ℝ≥0) < (L:WithTop ℝ≥0) := h
    simp only [if_neg h,if_neg he]
