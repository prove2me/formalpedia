-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_avram_clock_strict_event_to_infimum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:03:29.452156+00:00
-- url     : https://prove2.me/submissions/a369115d-326f-43e8-adfb-60ff4957e09d

import Theorems.Thm_AvramDividend_Classical_chat04_true_strict_closed_exponential_product_integral_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact clock calculation. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ q x : ℝ, 0 < q → 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
      (P.prod (expMeasure q)) {z : Ω × ℝ | 0 ≤ z.2 ∧
          ENNReal.ofReal z.2 < AvramDividend.Classical.twoSidedExitDownTime X (-x) z.1 ∧
          x + X.X z.2.toNNReal z.1 ∈ A} =
      (P.prod (expMeasure q)) {z : Ω × ℝ | (-sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1}) ≤ x ∧
          x + X.X z.2.toNNReal z.1 ∈ A} := by
  intro Ω mΩ P hP F X q x hq hx A hA
  classical
  let μ := P.prod (expMeasure q)
  let S : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
    ENNReal.ofReal z.2 < AvramDividend.Classical.twoSidedExitDownTime X (-x) z.1}
  let C : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
    ∀ s : ℝ≥0, s ≤ z.2.toNNReal → -x ≤ X.X s z.1}
  let T : Set (Ω × ℝ) := {z | x + X.X z.2.toNNReal z.1 ∈ A}
  let I : Ω × ℝ → ℝ := fun z => -sInf {y : ℝ | ∃ s : ℝ≥0,
    s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  have hS : MeasurableSet S :=
    AvramDividend.Classical.chat04_exponential_clock_strict_lower_killing_joint_measurable X (-x)
  have hC : MeasurableSet C :=
    AvramDividend.Classical.chat04_closed_history_lower_survival_joint_measurable_ws01a X x
  have hT : MeasurableSet T :=
    (measurable_const.add
      ((AvramDividend.Classical.chat04_levy_joint_time_state_measurable X).comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))) hA
  have hR : Measurable (T.indicator (1 : Ω × ℝ → ℝ≥0∞)) :=
    measurable_const.indicator hT
  have h := AvramDividend.Classical.chat04_true_strict_closed_exponential_product_integral_ws01a
    P X q hq x (T.indicator 1) hR
  change (∫⁻ z, S.indicator (T.indicator 1) z ∂μ) =
    (∫⁻ z, C.indicator (T.indicator 1) z ∂μ) at h
  rw [Set.indicator_indicator, Set.indicator_indicator,
    lintegral_indicator_one (hS.inter hT), lintegral_indicator_one (hC.inter hT)] at h
  have heq (z : Ω × ℝ) :
      (∀ s : ℝ≥0, s ≤ z.2.toNNReal → -x ≤ X.X s z.1) ↔ I z ≤ x := by
    let U : Set ℝ := {y | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧ y = X.X s z.1}
    have hne : U.Nonempty := ⟨X.X 0 z.1, 0, by positivity, rfl⟩
    have hb : BddBelow U :=
      AvramDividend.Classical.levy_path_bddBelow_finite_horizon X z.2.toNNReal z.1
    change _ ↔ -sInf U ≤ x
    constructor
    · intro hs
      apply neg_le.mpr
      exact le_csInf hne (by rintro y ⟨s, hs', rfl⟩; exact hs s hs')
    · intro hs s hs'
      have hh := csInf_le hb (show X.X s z.1 ∈ U from ⟨s, hs', rfl⟩)
      linarith
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  have he : (expMeasure q) (Iio (0 : ℝ)) = 0 := by
    change (volume.withDensity (exponentialPDF q)) (Iio (0 : ℝ)) = 0
    rw [withDensity_apply _ measurableSet_Iio]
    exact lintegral_exponentialPDF_of_nonpos le_rfl
  have hae : ∀ᵐ r ∂expMeasure q, 0 ≤ r := by
    rw [ae_iff]
    simp only [not_le]
    change (expMeasure q) (Iio (0 : ℝ)) = 0
    exact he
  have hprod : ∀ᵐ z ∂μ, 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const measurable_snd)).mpr
    exact Filter.Eventually.of_forall fun _ => hae
  have hleft : {z : Ω × ℝ | 0 ≤ z.2 ∧
      ENNReal.ofReal z.2 < AvramDividend.Classical.twoSidedExitDownTime X (-x) z.1 ∧
      x + X.X z.2.toNNReal z.1 ∈ A} = S ∩ T := by
    ext z
    simp only [S, T, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [hleft]
  change μ (S ∩ T) = μ {z | I z ≤ x ∧ x + X.X z.2.toNNReal z.1 ∈ A}
  rw [h]
  apply measure_congr
  filter_upwards [hprod] with z hz
  change ((0 ≤ z.2 ∧ ∀ s : ℝ≥0, s ≤ z.2.toNNReal → -x ≤ X.X s z.1) ∧
      x + X.X z.2.toNNReal z.1 ∈ A) =
    (I z ≤ x ∧ x + X.X z.2.toNNReal z.1 ∈ A)
  simp only [hz, true_and, heq]
