-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_upper_payoff_continuous_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T14:08:51.484883+00:00
-- url     : https://prove2.me/submissions/83886639-9ff8-4c71-9bcf-7dd6bccbfbfd

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_clocks_aemeasurable
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem discountedAt_norm_le_one (q : ℝ) (hq : 0 ≤ q) (t : WithTop ℝ≥0) :
    ‖discountedAt q t‖ ≤ 1 := by
  induction t using WithTop.recTopCoe with
  | top => simp [discountedAt]
  | coe s =>
    change ‖Real.exp (-q * (s : ℝ))‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) s.coe_nonneg

private theorem discountedAt_continuous_in_discount (t : WithTop ℝ≥0) :
    Continuous (fun q : ℝ => discountedAt q t) := by
  induction t using WithTop.recTopCoe with
  | top => simpa only [discountedAt] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  | coe s =>
    change Continuous (fun q : ℝ => Real.exp (-q * (s : ℝ)))
    exact Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)

private theorem discountedAt_measurable (q : ℝ) :
    Measurable (fun t : ℝ≥0∞ => discountedAt q t) := by
  have heq : (fun t : ℝ≥0∞ => discountedAt q t) =
      fun t => if t = ⊤ then 0 else Real.exp (-q * t.toReal) := by
    funext t
    induction t using WithTop.recTopCoe with
    | top => exact (if_pos rfl).symm
    | coe s => simp [discountedAt]
  rw [heq]
  exact Measurable.ite (measurableSet_singleton (⊤ : ℝ≥0∞)) measurable_const
    (Real.continuous_exp.measurable.comp (measurable_const.mul ENNReal.measurable_toReal))

private theorem ordered_clock_discount_limit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U L : Ω → ℝ≥0∞) (hU : AEMeasurable U P) (hL : AEMeasurable L P) :
    Tendsto (fun q : ℝ => ∫ ω, (if U ω < L ω then discountedAt q (U ω) else 0) ∂P)
      (nhdsWithin 0 (Ioi 0))
      (nhds (∫ ω, (if U ω < L ω then discountedAt 0 (U ω) else 0) ∂P)) := by
  have hm (q : ℝ) : AEStronglyMeasurable
      (fun ω => if U ω < L ω then discountedAt q (U ω) else 0) P := by
    have hg : Measurable (fun p : ℝ≥0∞ × ℝ≥0∞ =>
        if p.1 < p.2 then discountedAt q p.1 else 0) :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
        ((discountedAt_measurable q).comp measurable_fst) measurable_const
    exact (hg.comp_aemeasurable (hU.prodMk hL)).aestronglyMeasurable
  refine tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (Eventually.of_forall hm) ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact Eventually.of_forall fun ω => by
      change ‖(if U ω < L ω then discountedAt q (U ω) else 0)‖ ≤ 1
      by_cases h : U ω < L ω
      · simpa only [if_pos h] using discountedAt_norm_le_one q (le_of_lt hq) (U ω)
      · simp only [if_neg h, norm_zero, zero_le_one]
  · exact Eventually.of_forall fun ω => by
      change Tendsto (fun q : ℝ => if U ω < L ω then discountedAt q (U ω) else 0)
        (nhdsWithin 0 (Ioi 0)) (nhds (if U ω < L ω then discountedAt 0 (U ω) else 0))
      by_cases h : U ω < L ω
      · simpa only [if_pos h] using
          ((discountedAt_continuous_in_discount (U ω)).continuousWithinAt
            (s := Ioi (0 : ℝ)) (x := (0 : ℝ))).tendsto
      · simpa only [if_neg h] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (nhdsWithin 0 (Ioi 0)) (nhds 0))

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (x a : ℝ) :
    Tendsto (fun q : ℝ => upBeforeDownExpectation P D.X q x a)
      (nhdsWithin 0 (Ioi 0)) (nhds (upBeforeDownExpectation P D.X 0 x a)) := by
  obtain ⟨hU, hL⟩ := source_result81_strict_exit_clocks_aemeasurable Ω P D x a
  exact ordered_clock_discount_limit P _ _ hU hL
