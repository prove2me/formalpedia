-- Prove2me | solution 1 for Malliavin.pastCylinderDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:52:50.307025+00:00
-- url     : https://prove2.me/submissions/8db89619-e82f-4976-b447-9f26c3dc172b

import Definitions.Def_Malliavin_NaturalClarkOcone
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_PastCylinderDensity
import Theorems.Thm_Malliavin_measureDense_pastCylinderEvents
import Theorems.Thm_Malliavin_adaptedIndicator_pastCylinder_mem_closure
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
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
set_option maxHeartbeats 250000
omit [CompleteSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    PastCylinderDense hB coordinate coordinate_apply hsm hnat := by
  intro a
  let _ : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let K : Submodule ℝ (lpMeas ℝ ℝ (𝓕 a) 2 P) :=
    pastCylinderSpan hB coordinate coordinate_apply hsm hnat a
  let e : lpMeas ℝ ℝ (𝓕 a) 2 P ≃ₗᵢ[ℝ]
      @Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)) :=
    lpMeasToLpTrimLie ℝ ℝ 2 P (𝓕.le a)
  let R : Submodule ℝ (@Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a))) :=
    K.map (e : lpMeas ℝ ℝ (𝓕 a) 2 P →ₗ[ℝ]
      @Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)))
  have hMD := measureDense_pastCylinderEvents hB hsm hnat a
  have hone {s : Set W} (hs : MeasurableSet[𝓕 a] s)
      (hPs : P.trim (𝓕.le a) s ≠ ∞) :
      indicatorConstLp 2 hs hPs (1 : ℝ) ∈ R.topologicalClosure := by
    have happ := Measure.MeasureDense.indicatorConstLp_subset_closure
      (X := W) (E := ℝ) (m := 𝓕 a) (μ := P.trim (𝓕.le a))
      (𝒜 := pastCylinderEvents B a) 2 hMD (1 : ℝ) ⟨s, hs, hPs, rfl⟩
    apply (closure_minimal _ R.isClosed_topologicalClosure) happ
    rintro y ⟨t, ht, hPt, rfl⟩
    let Z := adaptedIndicator (P := P) 𝓕 a
      (measurableSet_pastCylinderEvents hsm hnat a ht)
    have hZ : Z ∈ K.topologicalClosure := by
      exact adaptedIndicator_pastCylinder_mem_closure
        hB coordinate coordinate_apply hsm hnat a ht
    have heq : e Z = indicatorConstLp 2
        (measurableSet_pastCylinderEvents hsm hnat a ht) hPt (1 : ℝ) := by
      apply e.symm.injective
      rw [e.symm_apply_apply]
      apply Subtype.ext
      simpa only [Z, adaptedIndicator] using
        (lpMeasToLpTrimLie_symm_indicator (F := ℝ) (p := 2)
          (μ := P) (hm := 𝓕.le a)
          (measurableSet_pastCylinderEvents hsm hnat a ht) hPt (1 : ℝ)).symm
    rw [← heq]
    apply K.topologicalClosure_map
      (e : lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ]
        @Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)))
    exact ⟨Z, hZ, rfl⟩
  have hall : ∀ f : @Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)),
      f ∈ R.topologicalClosure := by
    refine @Lp.induction W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)) _
      (by norm_num) (fun f ↦ f ∈ R.topologicalClosure) ?_ ?_
        R.isClosed_topologicalClosure
    · intro c s hs hPs
      change indicatorConstLp 2 hs hPs.ne c ∈ R.topologicalClosure
      have heq : indicatorConstLp 2 hs hPs.ne c =
          c • indicatorConstLp 2 hs hPs.ne (1 : ℝ) := by
        ext1
        grw [Lp.coeFn_smul, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
        filter_upwards [] with x
        by_cases hx : x ∈ s <;> simp [hx]
      rw [heq]
      exact R.topologicalClosure.smul_mem c (hone hs hPs.ne)
    · intro f g _hf _hg _hdisjoint hfm hgm
      exact R.topologicalClosure.add_mem hfm hgm
  have hRtop : R.topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    intro f _hf
    exact hall f
  have hback :
      (R.map (e.symm : @Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)) →ₗ[ℝ]
        lpMeas ℝ ℝ (𝓕 a) 2 P)).topologicalClosure = ⊤ :=
    (e.symm.surjective.denseRange).topologicalClosure_map_submodule hRtop
  have hmap :
      R.map (e.symm : @Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)) →ₗ[ℝ]
        lpMeas ℝ ℝ (𝓕 a) 2 P) = K := by
    apply le_antisymm
    · rintro z ⟨y, ⟨x, hx, rfl⟩, hy⟩
      have hxz : x = z := (e.symm_apply_apply x).symm.trans hy
      rwa [← hxz]
    · intro x hx
      refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
      exact e.symm_apply_apply x
  rw [hmap] at hback
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hback
end Malliavin
