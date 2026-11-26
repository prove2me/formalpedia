-- Prove2me | solution 1 for Malliavin.dense_brownianPolynomialSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:06.977128+00:00
-- url     : https://prove2.me/submissions/d1575e7c-8e3d-4ca8-b453-cf36be3a8d1e

import Definitions.Def_Malliavin_PastCylinderDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Theorems.Thm_Malliavin_measureDense_brownianCylinderEvents
import Theorems.Thm_Malliavin_indicator_brownianCylinder_mem_closure
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    Dense (brownianPolynomialSpan hB : Set (RandomL2 P)) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let _ : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let K := brownianPolynomialSpan hB
  have hMD := measureDense_brownianCylinderEvents hB hgen
  have hone {s : Set W} (hs : MeasurableSet s) (hPs : P s ≠ ∞) :
      indicatorConstLp 2 hs hPs (1 : ℝ) ∈ K.topologicalClosure := by
    have happ := Measure.MeasureDense.indicatorConstLp_subset_closure
      (X := W) (E := ℝ) (μ := P) (𝒜 := brownianCylinderEvents B)
      2 hMD (1 : ℝ) ⟨s, hs, hPs, rfl⟩
    apply (closure_minimal _ K.isClosed_topologicalClosure) happ
    rintro y ⟨t, ht, hPt, rfl⟩
    exact indicator_brownianCylinder_mem_closure hB hgen ht
  have hall : ∀ f : RandomL2 P, f ∈ K.topologicalClosure := by
    refine @Lp.induction W ℝ _ _ 2 P _ (by norm_num)
      (fun f ↦ f ∈ K.topologicalClosure) ?_ ?_ K.isClosed_topologicalClosure
    · intro c s hs hPs
      change indicatorConstLp 2 hs hPs.ne c ∈ K.topologicalClosure
      have heq : indicatorConstLp 2 hs hPs.ne c =
          c • indicatorConstLp 2 hs hPs.ne (1 : ℝ) := by
        ext1
        grw [Lp.coeFn_smul, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
        filter_upwards [] with x
        by_cases hx : x ∈ s <;> simp [hx]
      rw [heq]
      exact K.topologicalClosure.smul_mem c (hone hs hPs.ne)
    · intro f g _hf _hg _hdisjoint hfm hgm
      exact K.topologicalClosure.add_mem hfm hgm
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro f _hf
  exact hall f
end Malliavin
