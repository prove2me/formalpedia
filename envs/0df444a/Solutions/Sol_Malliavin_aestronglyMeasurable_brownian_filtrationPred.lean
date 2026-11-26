-- Prove2me | solution 1 for Malliavin.aestronglyMeasurable_brownian_filtrationPred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:44.816384+00:00
-- url     : https://prove2.me/submissions/a1429131-f0f9-4d83-8db7-bf08d5ba4a21

import Definitions.Def_Malliavin_PointwiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_le_filtrationPred
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_tendsto_brownianLp_exhaustion
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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) (ht : 0 < t) :
    AEStronglyMeasurable[filtrationPred (Filtration.natural B hm) t] (B t) P := by
  let u : ℕ → ℝ≥0 := fun n ↦ t - t / (n + 2)
  have hu_lt : ∀ n, u n < t := fun n ↦ tsub_lt_self ht (by positivity)
  have hconv : TendstoInMeasure P
      (fun n : ℕ ↦ (brownianLp hB (u n) : W → ℝ)) atTop
      (brownianLp hB t : W → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp (tendsto_brownianLp_exhaustion hB t)
  obtain ⟨ns, -, hlim⟩ := hconv.exists_seq_tendsto_ae
  have hcoe : ∀ᵐ w ∂P, ∀ n,
      (brownianLp hB (u (ns n)) : W → ℝ) w = B (u (ns n)) w :=
    ae_all_iff.2 fun n ↦ coeFn_brownianLp hB _
  have hlimB : ∀ᵐ w ∂P,
      Tendsto (fun n ↦ B (u (ns n)) w) atTop (nhds (B t w)) := by
    filter_upwards [hlim, hcoe, coeFn_brownianLp hB t] with w hw hcw htw
    simpa only [hcw, htw] using hw
  let G : W → ℝ := fun w ↦ limsup (fun n ↦ B (u (ns n)) w) atTop
  have hG : StronglyMeasurable[filtrationPred (Filtration.natural B hm) t] G :=
    Measurable.stronglyMeasurable (Measurable.limsup fun n ↦
      ((Filtration.stronglyAdapted_natural hm (u (ns n))).mono
        (le_filtrationPred (Filtration.natural B hm) (hu_lt (ns n)))).measurable)
  exact hG.aestronglyMeasurable.congr (hlimB.mono fun w hw ↦ hw.limsup_eq)
end Malliavin
