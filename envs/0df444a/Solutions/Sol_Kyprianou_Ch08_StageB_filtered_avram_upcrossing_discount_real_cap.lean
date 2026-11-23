-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.filtered_avram_upcrossing_discount_real_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:07:09.820529+00:00
-- url     : https://prove2.me/submissions/d86db755-c3cf-4f4e-9e4e-db7528f4f289

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_stageB_tauPlus_coe_eq
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Theorems.Thm_AvramDividend_Classical_levy_nonnegative_root_unrestricted_upcrossing_discount_bound
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

private theorem excursionDiscountMeasurable (q : ℝ) :
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

private theorem excursionDiscountENNEq (q : ℝ) (t : WithTop ℝ≥0) :
    ENNReal.ofReal (discountedAt q t) =
      if (t : ℝ≥0∞) < ⊤ then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal t))) else 0 := by
  cases t using WithTop.recTopCoe with
  | top => simp [discountedAt]
  | coe s =>
      split_ifs with hfin
      · simp [discountedAt]
      · exact False.elim (hfin ENNReal.coe_lt_top)

private theorem excursionDiscountUnit (q : ℝ) (hq : 0 ≤ q) (t : WithTop ℝ≥0) :
    0 ≤ discountedAt q t ∧ discountedAt q t ≤ 1 := by
  induction t using WithTop.recTopCoe with
  | top => simp [discountedAt]
  | coe s =>
      simp only [discountedAt]
      constructor
      · exact (Real.exp_pos _).le
      · rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) s.coe_nonneg

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 ≤ q) (φ : ℝ) (hφ : 0 ≤ φ)
    (hroot : A.ψ φ = q) :
    Integrable (fun ω => discountedAt q (tauPlus A.X 1 ω)) P ∧
      (∫ ω, discountedAt q (tauPlus A.X 1 ω) ∂P) ≤
        Real.exp (-(φ * 1)) := by
  have hpass := levy_nonnegative_root_unrestricted_upcrossing_discount_bound
    A q hq φ hφ hroot 1 (by norm_num)
  let clock : Ω → ℝ≥0∞ := fun ω => (tauPlus A.X 1 ω : ℝ≥0∞)
  let f : Ω → ℝ := fun ω => discountedAt q (tauPlus A.X 1 ω)
  have hclock (ω : Ω) : clock ω = twoSidedExitUpTime A 1 ω :=
    stageB_tauPlus_coe_eq A 1 ω
  have hclockCorrected (ω : Ω) :
      clock ω = twoSidedExitUpTimeCorrected A 1 ω := by
    change clock ω = twoSidedExitUpTime A 1 ω
    exact hclock ω
  have hclockmeas : Measurable clock := by
    have heq : clock = fun ω => twoSidedExitUpTime A 1 ω := funext hclock
    rw [heq]
    exact upperPassage_measurable_from_stopping A 1
  have hfmeas : Measurable f := (excursionDiscountMeasurable q).comp hclockmeas
  have hfnon (ω : Ω) : 0 ≤ f ω := (excursionDiscountUnit q hq _).1
  have hfnorm (ω : Ω) : ‖f ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnon ω)]
    exact (excursionDiscountUnit q hq _).2
  have hfint : Integrable f P :=
    Integrable.of_bound hfmeas.aestronglyMeasurable 1
      (Eventually.of_forall hfnorm)
  have hpoint (ω : Ω) :
      ENNReal.ofReal (f ω) =
        if twoSidedExitUpTimeCorrected A 1 ω < ⊤
        then ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTimeCorrected A 1 ω).toReal)))
        else 0 := by
    rw [← hclockCorrected ω]
    change ENNReal.ofReal (discountedAt q (tauPlus A.X 1 ω)) =
      if clock ω < ⊤ then
        ENNReal.ofReal (Real.exp (-(q * (clock ω).toReal))) else 0
    exact excursionDiscountENNEq q (tauPlus A.X 1 ω)
  have hlintegral := (lintegral_congr hpoint).le.trans hpass
  refine ⟨hfint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall hfnon) hfmeas.aestronglyMeasurable]
  have hmono := ENNReal.toReal_mono
    (ENNReal.ofReal_lt_top.ne) hlintegral
  simpa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hmono
