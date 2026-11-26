-- Prove2me | solution 1 for Malliavin.adaptedIndicator_pastCylinder_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:50:39.167693+00:00
-- url     : https://prove2.me/submissions/15264c2e-bd5f-4096-bc65-059bdad95e89

import Definitions.Def_Malliavin_NaturalClarkOcone
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_PastCylinderDensity
import Theorems.Thm_Malliavin_IsSmoothBounded_comp_continuousLinearMap
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
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
omit [CompleteSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0)
    {s : Set W} (hs : s ∈ pastCylinderEvents B a) :
    adaptedIndicator (P := P) 𝓕 a
        (measurableSet_pastCylinderEvents hsm hnat a hs) ∈
      (pastCylinderSpan hB coordinate coordinate_apply hsm hnat a).topologicalClosure := by
  rcases hs with ⟨C, hC, rfl⟩
  rcases (mem_measurableCylinders C).mp hC with ⟨I, A, hA, rfl⟩
  let L : W →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun i ↦ coordinate i.1
  let ν : Measure (I → ℝ) := P.map L
  let _ : IsGaussian ν := by
    dsimp only [ν]
    infer_instance
  let hmp : MeasurePreserving L P ν := L.measurable.measurePreserving P
  let Y : Lp ℝ 2 ν :=
    indicatorConstLp 2 hA (measure_ne_top ν A) (1 : ℝ)
  have hset :
      pastProcess B a ⁻¹' cylinder I A = L ⁻¹' A := by
    ext w
    simp only [Set.mem_preimage, mem_cylinder, Finset.restrict_def, pastProcess, L,
      ContinuousLinearMap.coe_pi', coordinate_apply]
  change adaptedIndicator (P := P) 𝓕 a
      (measurableSet_pastCylinderEvents hsm hnat a
        ⟨cylinder I A, hC, rfl⟩) ∈
    closure (pastCylinderSpan hB coordinate coordinate_apply hsm hnat a :
      Set (lpMeas ℝ ℝ (𝓕 a) 2 P))
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  have hY : Y ∈ closure
      (Set.range fun G : {G : (I → ℝ) → ℝ // IsSmoothBounded G} ↦ G.2.toLp ν) :=
    (denseRange_toLp ν) Y
  rcases Metric.mem_closure_iff.mp hY ε hε with ⟨g, ⟨G, rfl⟩, hdist⟩
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let Q : (Fin (Fintype.card I) → ℝ) ≃L[ℝ] (I → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : I ↦ ℝ) e
  let f : (Fin (Fintype.card I) → ℝ) → ℝ := G.1 ∘ Q
  have hf : IsSmoothBounded f :=
    G.2.comp_continuousLinearMap Q.toContinuousLinearMap
  let t : Fin (Fintype.card I) → ℝ≥0 := fun j ↦ (e j).1
  have ht : ∀ j, t j ≤ a := fun j ↦ (e j).1.2
  let Z := pastCylinderLpMeas hB coordinate coordinate_apply hsm hnat
    f hf.contDiff hf.bounded hf.bounded_fderiv t a ht
  refine ⟨Z, ?_, ?_⟩
  · change Z ∈ pastCylinderSpan hB coordinate coordinate_apply hsm hnat a
    apply Submodule.subset_span
    exact ⟨Fintype.card I, f, hf.contDiff, hf.bounded, hf.bounded_fderiv,
      t, ht, rfl⟩
  · have hfun : (fun w ↦ f (fun j ↦ B (t j) w)) = G.1 ∘ L := by
      funext w
      simp only [f, Function.comp_apply, t, L, ContinuousLinearMap.coe_pi',
        coordinate_apply]
      apply congrArg G.1
      have hy : (fun j ↦ coordinate (e j).1 w) =
          Q.symm (fun i ↦ coordinate i.1 w) := by
        rfl
      rw [hy, Q.apply_symm_apply]
    have hZ : (Z : Lp ℝ 2 P) =
        Lp.compMeasurePreserving L hmp (G.2.toLp ν) := by
      let hG := isSmoothBounded_cylinder coordinate coordinate_apply
        f hf.contDiff hf.bounded hf.bounded_fderiv t
      change hG.toLp P = Lp.compMeasurePreserving L hmp (G.2.toLp ν)
      unfold IsSmoothBounded.toLp
      rw [Lp.toLp_compMeasurePreserving]
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (hG.memLp P 2),
        MemLp.coeFn_toLp ((G.2.memLp ν 2).comp_measurePreserving hmp)] with w hw₁ hw₂
      rw [hw₁, hw₂]
      exact congrFun hfun w
    have hI :
        ((adaptedIndicator (P := P) 𝓕 a
          (measurableSet_pastCylinderEvents hsm hnat a
            ⟨cylinder I A, hC, rfl⟩) :
            lpMeas ℝ ℝ (𝓕 a) 2 P) : Lp ℝ 2 P) =
          Lp.compMeasurePreserving L hmp Y := by
      change indicatorConstLp 2
          (𝓕.le a (pastProcess B a ⁻¹' cylinder I A)
            (measurableSet_pastCylinderEvents hsm hnat a
              ⟨cylinder I A, hC, rfl⟩))
          (measure_ne_top P (pastProcess B a ⁻¹' cylinder I A)) (1 : ℝ) =
        Lp.compMeasurePreserving L hmp Y
      rw [Lp.indicatorConstLp_compMeasurePreserving]
      congr 1
    change dist
      ((adaptedIndicator (P := P) 𝓕 a
        (measurableSet_pastCylinderEvents hsm hnat a
          ⟨cylinder I A, hC, rfl⟩) :
          lpMeas ℝ ℝ (𝓕 a) 2 P) : Lp ℝ 2 P) (Z : Lp ℝ 2 P) < ε
    rw [hI, hZ, (Lp.isometry_compMeasurePreserving hmp).dist_eq]
    exact hdist
end Malliavin
