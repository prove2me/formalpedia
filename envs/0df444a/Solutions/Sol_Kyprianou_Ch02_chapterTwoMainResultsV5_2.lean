-- Prove2me | solution 2 for Kyprianou.Ch02.chapterTwoMainResultsV5
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T17:40:36.315806+00:00
-- url     : https://prove2.me/submissions/2ef5cda2-14e6-4a6f-91ef-3e82be2b4f3e

import Mathlib
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV2
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV5
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists
import Theorems.Thm_Kyprianou_poissonRandomMeasureSupportCountable
import Theorems.Thm_Kyprianou_poissonRandomMeasureIntegralLaws
import Theorems.Thm_Kyprianou_sumOfIndependentLevyProcesses
import Theorems.Thm_Kyprianou_smallJumpLimitCadlagCorrected
import Theorems.Thm_Kyprianou_levyItoDecompositionCorrected
import Theorems.Thm_Kyprianou_boundedVariationCriterionCh02
import Theorems.Thm_Kyprianou_compoundPoissonDriftPathCriterionCh02V3
import Theorems.Thm_Kyprianou_independentSubordinationCh02V3
import Theorems.Thm_Kyprianou_subordinatorCriterionCh02V3
import Theorems.Thm_Kyprianou_markedCompoundPoissonRandomMeasureCh02V5
import Theorems.Thm_Kyprianou_poissonRandomMeasureExistsGenericCh02V3
import Theorems.Thm_Kyprianou_poissonRestrictionAndIndependenceCh02V3
import Theorems.Thm_Kyprianou_finiteRegionPoissonIntegralCh02V3
import Theorems.Thm_Kyprianou_compensatedGeneralRegionMartingaleCh02V3
import Theorems.Thm_Kyprianou_exercise2_1_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_3_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_4_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_6_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_8_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_11_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_2_AllPartsCh02V4
import Theorems.Thm_Kyprianou_exercise2_7_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_10_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_5_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_9_AllPartsCh02V4
import Theorems.Thm_Kyprianou_exercise2_12_AllPartsCh02V4
import Theorems.Thm_Kyprianou_poissonRandomMeasureSupportGenericMeasurableSingletons

open MeasureTheory ProbabilityTheory Kyprianou
open scoped NNReal ENNReal
set_option autoImplicit false

private lemma levyMeasure_finite_of_abs_ge
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {B : Set ℝ} {δ : ℝ} (hδ : 0 < δ) (hsubB : ∀ x ∈ B, δ ≤ |x|) :
    levyMeasure B < ⊤ := by
  let c : ENNReal := ENNReal.ofReal (min 1 (δ ^ 2))
  let f : ℝ → ENNReal := fun x => ENNReal.ofReal (min 1 (x ^ 2))
  have hc_pos : 0 < c := ENNReal.ofReal_pos.mpr (lt_min one_pos (sq_pos_of_pos hδ))
  have hf_meas : Measurable f :=
    ENNReal.measurable_ofReal.comp (measurable_const.min (measurable_id'.pow_const 2))
  have hsub : B ⊆ {x : ℝ | c ≤ f x} := fun x hx =>
    ENNReal.ofReal_le_ofReal (min_le_min le_rfl
      ((sq_abs x).symm ▸ pow_le_pow_left₀ hδ.le (hsubB x hx) 2))
  have hle : c * levyMeasure B ≤ ∫⁻ x, f x ∂levyMeasure :=
    le_trans (mul_le_mul_right (measure_mono hsub) c)
      (mul_meas_ge_le_lintegral hf_meas c (μ := levyMeasure))
  exact ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top hlevyMeasure.2.ne hle) hc_pos.ne'

private lemma largeJumpProcessLevy_of_finiteRegion :
    Kyprianou.Ch02.certificateV2_largeJumpProcessLevy := by
  intro Ω _ P _ levyMeasure _ hlevyMeasure N
  let B : Set ℝ := {x : ℝ | 1 ≤ |x|}
  have hB : MeasurableSet B := measurableSet_le measurable_const continuous_abs.measurable
  have hfinite : levyMeasure B < ⊤ :=
    levyMeasure_finite_of_abs_ge levyMeasure hlevyMeasure one_pos (fun _ hx => hx)
  exact Kyprianou.finiteRegionPoissonIntegralCh02V3 P levyMeasure N B hB hfinite

private lemma compensatedBandIsL2Martingale_of_generalRegion :
    Kyprianou.Ch02.certificateV2_compensatedBandIsL2Martingale := by
  intro Ω _ P _ levyMeasure _ hlevyMeasure N ε hε _
  let B : Set ℝ := {x : ℝ | ε ≤ |x| ∧ |x| < 1}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfinite : levyMeasure B < ⊤ :=
    levyMeasure_finite_of_abs_ge levyMeasure hlevyMeasure hε (fun _ hx => hx.1)
  have : IsFiniteMeasure (levyMeasure.restrict B) := isFiniteMeasure_restrict.mpr hfinite.ne
  have hbound : ∀ᵐ x ∂(levyMeasure.restrict B), ‖x‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem hB] with x hx
    simpa only [Real.norm_eq_abs] using hx.2.le
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x) (levyMeasure.restrict B) :=
    measurable_id.aestronglyMeasurable
  have hfirst : Integrable (fun x : ℝ => x) (levyMeasure.restrict B) :=
    MeasureTheory.Integrable.of_bound hmeas 1 hbound
  have hsecond : MemLp (fun x : ℝ => x) 2 (levyMeasure.restrict B) :=
    MeasureTheory.MemLp.of_bound hmeas 1 hbound
  obtain ⟨ℱ, hfil, hmart, hmem⟩ :=
    Kyprianou.compensatedGeneralRegionMartingaleCh02V3 P levyMeasure N B hB hfinite hfirst
  exact ⟨ℱ, hfil, hmart, hmem hsecond⟩

theorem solution :
    Kyprianou.Ch02.certificateV2_poissonRandomMeasureExists ∧
    Kyprianou.Ch02.certificateV2_poissonRandomMeasureSupportCountable ∧
    Kyprianou.Ch02.certificateV2_poissonRandomMeasureIntegralLaws ∧
    Kyprianou.Ch02.certificateV2_largeJumpProcessLevy ∧
    Kyprianou.Ch02.certificateV2_sumOfIndependentLevyProcesses ∧
    Kyprianou.Ch02.certificateV2_compensatedBandIsL2Martingale ∧
    Kyprianou.Ch02.certificateV2_smallJumpLimitCadlag ∧
    Kyprianou.Ch02.certificateV2_levyItoDecomposition ∧
    Kyprianou.Ch02.certificateV2_boundedVariationCriterionCh02 ∧
    Kyprianou.Ch02.certificateV3_compoundPoissonDriftPathCriterionCh02V3 ∧
    Kyprianou.Ch02.certificateV3_independentSubordinationCh02V3 ∧
    Kyprianou.Ch02.certificateV3_subordinatorCriterionCh02V3 ∧
    Kyprianou.Ch02.certificateV4_markedCompoundPoissonRandomMeasureCh02V5 ∧
    Kyprianou.Ch02.certificateV3_poissonRandomMeasureExistsGenericCh02V3 ∧
    Kyprianou.Ch02.certificateV3_poissonRestrictionAndIndependenceCh02V3 ∧
    Kyprianou.Ch02.certificateV3_finiteRegionPoissonIntegralCh02V3 ∧
    Kyprianou.Ch02.certificateV3_compensatedGeneralRegionMartingaleCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_1_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_3_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_4_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_6_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_8_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_11_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV4_exercise2_2_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV3_exercise2_7_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_10_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_5_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV4_exercise2_9_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV4_exercise2_12_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV5_poissonRandomMeasureSupportGenericMeasurableSingletons :=
  ⟨Kyprianou.poissonRandomMeasureExists,
   Kyprianou.poissonRandomMeasureSupportCountable,
   Kyprianou.poissonRandomMeasureIntegralLaws,
   largeJumpProcessLevy_of_finiteRegion,
   Kyprianou.sumOfIndependentLevyProcesses,
   compensatedBandIsL2Martingale_of_generalRegion,
   Kyprianou.smallJumpLimitCadlagCorrected,
   Kyprianou.levyItoDecompositionCorrected,
   Kyprianou.boundedVariationCriterionCh02,
   Kyprianou.compoundPoissonDriftPathCriterionCh02V3,
   Kyprianou.independentSubordinationCh02V3,
   Kyprianou.subordinatorCriterionCh02V3,
   Kyprianou.markedCompoundPoissonRandomMeasureCh02V5,
   Kyprianou.poissonRandomMeasureExistsGenericCh02V3,
   Kyprianou.poissonRestrictionAndIndependenceCh02V3,
   Kyprianou.finiteRegionPoissonIntegralCh02V3,
   Kyprianou.compensatedGeneralRegionMartingaleCh02V3,
   Kyprianou.exercise2_1_AllPartsCh02V3,
   Kyprianou.exercise2_3_AllPartsCh02V3,
   Kyprianou.exercise2_4_AllPartsCh02V3,
   Kyprianou.exercise2_6_AllPartsCh02V3,
   Kyprianou.exercise2_8_AllPartsCh02V3,
   Kyprianou.exercise2_11_AllPartsCh02V3,
   Kyprianou.exercise2_2_AllPartsCh02V4,
   Kyprianou.exercise2_7_AllPartsCh02V3,
   Kyprianou.exercise2_10_AllPartsCh02V3,
   Kyprianou.exercise2_5_AllPartsCh02V3,
   Kyprianou.exercise2_9_AllPartsCh02V4,
   Kyprianou.exercise2_12_AllPartsCh02V4,
   Kyprianou.poissonRandomMeasureSupportGenericMeasurableSingletons⟩
