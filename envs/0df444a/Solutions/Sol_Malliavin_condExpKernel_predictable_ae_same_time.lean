-- Prove2me | solution 1 for Malliavin.condExpKernel_predictable_ae_same_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:17:28.328894+00:00
-- url     : https://prove2.me/submissions/7b85f6b1-321c-48a5-bf07-fb97e1363e70

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
namespace Malliavin
theorem _root_.solution
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    ∀ᵐ p ∂μ, ∀ᵐ q ∂condExpKernel μ 𝓕.predictable p, q.1 = p.1 := by
  let mΩ : MeasurableSpace (ℝ≥0 × S) := inferInstance
  have hm : 𝓕.predictable ≤ mΩ := predictable_le_prod 𝓕
  have hdiag_meas : @Measurable (ℝ≥0 × S) ((ℝ≥0 × S) × (ℝ≥0 × S))
      mΩ (𝓕.predictable.prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have hsame_time_meas : @MeasurableSet ((ℝ≥0 × S) × (ℝ≥0 × S))
      (𝓕.predictable.prod mΩ) {z | z.2.1 = z.1.1} := by
    apply measurableSet_eq_fun
    · exact measurable_fst.comp measurable_snd
    · exact (measurable_fst_predictable 𝓕).comp measurable_fst
  have hdiag_ae : @AEMeasurable (ℝ≥0 × S) ((ℝ≥0 × S) × (ℝ≥0 × S))
      (𝓕.predictable.prod mΩ) mΩ Function.diag μ :=
    @Measurable.aemeasurable (ℝ≥0 × S) ((ℝ≥0 × S) × (ℝ≥0 × S))
      mΩ (𝓕.predictable.prod mΩ) Function.diag μ hdiag_meas
  have hbad_time_meas : @MeasurableSet ((ℝ≥0 × S) × (ℝ≥0 × S))
      (𝓕.predictable.prod mΩ) {z | ¬z.2.1 = z.1.1} := hsame_time_meas.compl
  have hdiag : ∀ᵐ z ∂(@Measure.map (ℝ≥0 × S) ((ℝ≥0 × S) × (ℝ≥0 × S))
      mΩ (𝓕.predictable.prod mΩ) Function.diag μ), z.2.1 = z.1.1 := by
    rw [ae_iff]
    rw [@Measure.map_apply_of_aemeasurable (ℝ≥0 × S)
      ((ℝ≥0 × S) × (ℝ≥0 × S)) mΩ (𝓕.predictable.prod mΩ)
      μ Function.diag hdiag_ae _ hbad_time_meas]
    simp only [Set.preimage_ofPred_eq, Function.diag, not_true_eq_false, Set.ofPred_false, measure_empty]
  rw [← compProd_trim_condExpKernel hm] at hdiag
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_compProd hdiag)
end Malliavin
