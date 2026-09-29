-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.exists_isCuspLift3_translateRight_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1b94efab-5a19-5d41-bf20-2ada1bd1ebea

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuousLinearMap_eq_of_forall_toL2_eq
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_isCuspLift3_translateRight_norm_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix IsDedekindDomain NumberField MeasureTheory Filter Topology AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal NNReal Uniformity

namespace LTCubicCuspLift

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

abbrev 𝔸ℚ : Type := AdeleRing (𝓞 ℚ) ℚ

abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ

abbrev pins₀ : CarrierPins ℚ :=
  productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

def ν₀ : Measure 𝔸ℚ :=
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

theorem pins₀_ν : pins₀.ν = ν₀ := rfl

scoped instance : IsProbabilityMeasure ν₀ :=
  AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

theorem ae_mem_box : ∀ᵐ y ∂ν₀, y ∈ AdelicBox.adelicBox ℚ := by
  unfold ν₀ ProbabilityTheory.cond
  exact Measure.ae_smul_measure (ae_restrict_mem (AdelicBox.measurableSet_adelicBox ℚ)) _

def boxHull : Set 𝔸ℚ := (AdelicBox.exists_isCompact_adelicBox_subset ℚ).choose

theorem isCompact_boxHull : IsCompact boxHull :=
  (AdelicBox.exists_isCompact_adelicBox_subset ℚ).choose_spec.1

theorem box_subset_boxHull : AdelicBox.adelicBox ℚ ⊆ boxHull :=
  (AdelicBox.exists_isCompact_adelicBox_subset ℚ).choose_spec.2

theorem ae_mem_boxHull : ∀ᵐ y ∂ν₀, y ∈ boxHull :=
  ae_mem_box.mono fun _ hy => box_subset_boxHull hy

def boxIter (Ψ : 𝔸ℚ → 𝔸ℚ → ℂ) : ℂ := ∫ x, ∫ y, Ψ x y ∂ν₀ ∂ν₀

section Iter

variable {Ψ Ψ' : 𝔸ℚ → 𝔸ℚ → ℂ}

theorem integrable_of_continuous {h : 𝔸ℚ → ℂ} (hh : Continuous h) : Integrable h ν₀ := by
  obtain ⟨B, hB⟩ := isCompact_boxHull.exists_bound_of_continuousOn hh.continuousOn
  exact Integrable.mono' (integrable_const B) hh.aestronglyMeasurable (ae_mem_boxHull.mono fun y hy => hB y hy)

theorem integrable_section (hΨ : Continuous (Function.uncurry Ψ)) (x : 𝔸ℚ) : Integrable (Ψ x) ν₀ :=
  integrable_of_continuous (hΨ.comp (Continuous.prodMk_right x))

theorem continuous_inner (hΨ : Continuous (Function.uncurry Ψ)) :
    Continuous fun x => ∫ y, Ψ x y ∂ν₀ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  show Tendsto (fun x => ∫ y, Ψ x y ∂ν₀) (𝓝 x₀) (𝓝 (∫ y, Ψ x₀ y ∂ν₀))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨v, hv, hvu⟩ := isCompact_boxHull.mem_uniformity_of_prod (f := Ψ) (s := Set.univ)
    hΨ.continuousOn (Set.mem_univ x₀) (Metric.dist_mem_uniformity hε2)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with x hx
  have hpt : ∀ y ∈ boxHull, ‖Ψ x y - Ψ x₀ y‖ ≤ ε / 2 := fun y hy => by
    have := hvu x hx y hy
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  rw [dist_eq_norm, ← integral_sub (integrable_section hΨ x) (integrable_section hΨ x₀)]
  have h := norm_integral_le_of_norm_le_const (μ := ν₀) (f := fun y => Ψ x y - Ψ x₀ y) (C := ε / 2)
    (ae_mem_boxHull.mono fun y hy => hpt y hy)
  simp only [probReal_univ, mul_one] at h
  linarith

theorem integrable_innerIntegral (hΨ : Continuous (Function.uncurry Ψ)) :
    Integrable (fun x => ∫ y, Ψ x y ∂ν₀) ν₀ :=
  integrable_of_continuous (continuous_inner hΨ)

theorem boxIter_add (hΨ : Continuous (Function.uncurry Ψ)) (hΨ' : Continuous (Function.uncurry Ψ')) :
    boxIter (fun x y => Ψ x y + Ψ' x y) = boxIter Ψ + boxIter Ψ' := by
  unfold boxIter
  have h1 : (fun x => ∫ y, Ψ x y + Ψ' x y ∂ν₀) = fun x => (∫ y, Ψ x y ∂ν₀) + ∫ y, Ψ' x y ∂ν₀ := by
    funext x
    exact integral_add (integrable_section hΨ x) (integrable_section hΨ' x)
  rw [h1]
  exact integral_add (integrable_innerIntegral hΨ) (integrable_innerIntegral hΨ')

theorem boxIter_const_mul (Ψ : 𝔸ℚ → 𝔸ℚ → ℂ) (c : ℂ) :
    boxIter (fun x y => c * Ψ x y) = c * boxIter Ψ := by
  unfold boxIter
  have h1 : (fun x => ∫ y, c * Ψ x y ∂ν₀) = fun x => c * ∫ y, Ψ x y ∂ν₀ := by
    funext x
    exact integral_const_mul c _
  rw [h1]
  exact integral_const_mul c _

theorem boxIter_zero : boxIter (fun _ _ => (0 : ℂ)) = 0 := by
  simp [boxIter]

end Iter

def theta21 (g : G3) (p : 𝔸ℚ × 𝔸ℚ) : G3 := radicalP21 ![p.1, p.2] * g

def theta12 (g : G3) (p : 𝔸ℚ × 𝔸ℚ) : G3 := radicalP12 ![p.1, p.2] * g

theorem continuous_upperUnipotent3 :
    Continuous fun q : 𝔸ℚ × 𝔸ℚ × 𝔸ℚ => (upperUnipotent3 q.1 q.2.1 q.2.2 : G3) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi_iff.2 fun i => continuous_pi_iff.2 fun j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent3, Matrix.of_apply] <;> fun_prop
  · refine continuous_pi_iff.2 fun i => continuous_pi_iff.2 fun j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent3, Matrix.of_apply] <;> fun_prop

theorem continuous_theta21 (g : G3) : Continuous (theta21 g) := by
  have h : Continuous fun p : 𝔸ℚ × 𝔸ℚ => (radicalP21 ![p.1, p.2] : G3) := by
    have := continuous_upperUnipotent3.comp
      (show Continuous fun p : 𝔸ℚ × 𝔸ℚ => ((0 : 𝔸ℚ), p.2, p.1) by fun_prop)
    simpa [radicalP21, Function.comp_def] using this
  exact h.mul continuous_const

theorem continuous_theta12 (g : G3) : Continuous (theta12 g) := by
  have h : Continuous fun p : 𝔸ℚ × 𝔸ℚ => (radicalP12 ![p.1, p.2] : G3) := by
    have := continuous_upperUnipotent3.comp
      (show Continuous fun p : 𝔸ℚ × 𝔸ℚ => (p.1, (0 : 𝔸ℚ), p.2) by fun_prop)
    simpa [radicalP12, Function.comp_def] using this
  exact h.mul continuous_const

theorem isCuspidalAlongP21_iff (F : G3 → ℂ) :
    IsCuspidalAlongP21 pins₀ F ↔ ∀ g : G3, boxIter (fun x y => F (theta21 g (x, y))) = 0 :=
  Iff.rfl

theorem isCuspidalAlongP12_iff (F : G3 → ℂ) :
    IsCuspidalAlongP12 pins₀ F ↔ ∀ g : G3, boxIter (fun x y => F (theta12 g (x, y))) = 0 :=
  Iff.rfl

theorem continuous_uncurry_comp_theta21 {F : G3 → ℂ} (hF : Continuous F) (g : G3) :
    Continuous (Function.uncurry fun x y => F (theta21 g (x, y))) :=
  hF.comp (continuous_theta21 g)

theorem continuous_uncurry_comp_theta12 {F : G3 → ℂ} (hF : Continuous F) (g : G3) :
    Continuous (Function.uncurry fun x y => F (theta12 g (x, y))) :=
  hF.comp (continuous_theta12 g)

section CuspSpace

variable {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {a b : ℝ} {Φ₀ : Set G3}

theorem zero_mem_cuspFunctions : (0 : G3 → ℂ) ∈ cuspFunctions ω a b Φ₀ := by
  refine ⟨Submodule.zero_mem _, continuous_const, ?_, ?_⟩
  · rw [isCuspidalAlongP21_iff]
    intro g
    exact boxIter_zero
  · rw [isCuspidalAlongP12_iff]
    intro g
    exact boxIter_zero

theorem add_mem_cuspFunctions {F F' : G3 → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀)
    (hF' : F' ∈ cuspFunctions ω a b Φ₀) : F + F' ∈ cuspFunctions ω a b Φ₀ := by
  refine ⟨Submodule.add_mem _ hF.1 hF'.1, hF.2.1.add hF'.2.1, ?_, ?_⟩
  · rw [isCuspidalAlongP21_iff]
    intro g
    have h := boxIter_add (continuous_uncurry_comp_theta21 hF.2.1 g) (continuous_uncurry_comp_theta21 hF'.2.1 g)
    have h1 := (isCuspidalAlongP21_iff F).1 hF.2.2.1 g
    have h2 := (isCuspidalAlongP21_iff F').1 hF'.2.2.1 g
    simp only [Pi.add_apply]
    rw [h, h1, h2, add_zero]
  · rw [isCuspidalAlongP12_iff]
    intro g
    have h := boxIter_add (continuous_uncurry_comp_theta12 hF.2.1 g) (continuous_uncurry_comp_theta12 hF'.2.1 g)
    have h1 := (isCuspidalAlongP12_iff F).1 hF.2.2.2 g
    have h2 := (isCuspidalAlongP12_iff F').1 hF'.2.2.2 g
    simp only [Pi.add_apply]
    rw [h, h1, h2, add_zero]

theorem smul_mem_cuspFunctions (c : ℂ) {F : G3 → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    c • F ∈ cuspFunctions ω a b Φ₀ := by
  refine ⟨Submodule.smul_mem _ c hF.1, hF.2.1.const_smul c, ?_, ?_⟩
  · rw [isCuspidalAlongP21_iff]
    intro g
    have h1 := (isCuspidalAlongP21_iff F).1 hF.2.2.1 g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [boxIter_const_mul, h1, mul_zero]
  · rw [isCuspidalAlongP12_iff]
    intro g
    have h1 := (isCuspidalAlongP12_iff F).1 hF.2.2.2 g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [boxIter_const_mul, h1, mul_zero]

end CuspSpace

section Lift

variable (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
  (a b : ℝ) (Φ₀ : Set G3) (hΦ₀ : IsSlabDomain a b Φ₀)

def cuspSub : Submodule ℂ ↥(automorphicSubmodule ω a b Φ₀) where
  carrier := cuspMembers ω a b Φ₀
  zero_mem' := (mem_cuspMembers_iff ω a b Φ₀ _).2 zero_mem_cuspFunctions
  add_mem' := fun {f f'} hf hf' =>
    (mem_cuspMembers_iff ω a b Φ₀ _).2
      (add_mem_cuspFunctions ((mem_cuspMembers_iff ω a b Φ₀ _).1 hf) ((mem_cuspMembers_iff ω a b Φ₀ _).1 hf'))
  smul_mem' := fun c {f} hf =>
    (mem_cuspMembers_iff ω a b Φ₀ _).2 (smul_mem_cuspFunctions c ((mem_cuspMembers_iff ω a b Φ₀ _).1 hf))

theorem mem_cuspSub_iff (f : ↥(automorphicSubmodule ω a b Φ₀)) :
    f ∈ cuspSub ω a b Φ₀ ↔ (f : G3 → ℂ) ∈ cuspFunctions ω a b Φ₀ :=
  Iff.rfl

theorem coe_cuspSub : (cuspSub ω a b Φ₀ : Set ↥(automorphicSubmodule ω a b Φ₀)) = cuspMembers ω a b Φ₀ := rfl

abbrev V : Type := ↥(cuspidalSubspace ω a b Φ₀)

scoped instance completeSpace_V : CompleteSpace (V ω a b Φ₀) := by
  unfold V cuspidalSubspace
  infer_instance

def e : ↥(cuspSub ω a b Φ₀) →ₗ[ℂ] V ω a b Φ₀ where
  toFun f := ⟨toL2 ω a b Φ₀ (f : ↥(automorphicSubmodule ω a b Φ₀)), toL2_mem_cuspidalSubspace ω a b Φ₀ f.2⟩
  map_add' f f' := by
    apply Subtype.ext
    simp
  map_smul' c f := by
    apply Subtype.ext
    simp

theorem e_apply_coe (f : ↥(cuspSub ω a b Φ₀)) :
    ((e ω a b Φ₀ f : V ω a b Φ₀) : Carrier a b Φ₀) = toL2 ω a b Φ₀ (f : ↥(automorphicSubmodule ω a b Φ₀)) := rfl

theorem denseRange_e : DenseRange (e ω a b Φ₀) := by
  rw [DenseRange, Subtype.dense_iff]
  intro v hv
  have hV : ((cuspidalSubspace ω a b Φ₀ : Submodule ℂ (Carrier a b Φ₀)) : Set (Carrier a b Φ₀)) =
      closure ((Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀) : Submodule ℂ (Carrier a b Φ₀)) :
        Set (Carrier a b Φ₀)) := by
    rw [cuspidalSubspace_def, Submodule.topologicalClosure_coe]
  rw [hV] at hv
  refine closure_mono ?_ hv
  intro w hw
  have hspan : Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀) =
      (cuspSub ω a b Φ₀).map (toL2 ω a b Φ₀) := by
    rw [← coe_cuspSub, Submodule.span_image, Submodule.span_eq]
  have hw' : w ∈ (cuspSub ω a b Φ₀).map (toL2 ω a b Φ₀) := by
    rw [← hspan]; exact hw
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hw'
  exact ⟨⟨toL2 ω a b Φ₀ f, toL2_mem_cuspidalSubspace ω a b Φ₀ hf⟩, ⟨⟨f, hf⟩, rfl⟩, rfl⟩

include hω hΦ₀

theorem translate_facts (F : G3 → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) :
    ∃ hmem : ∀ g : G3, translateRight g F ∈ cuspFunctions ω a b Φ₀,
      (∀ g : G3, ‖toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩‖ = ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖) ∧
      Continuous fun g : G3 => toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩ :=
  exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F hF

theorem translateRight_mem (g : G3) {F : G3 → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    translateRight g F ∈ cuspFunctions ω a b Φ₀ :=
  (translate_facts ω hω a b Φ₀ hΦ₀ F hF).fst g

theorem norm_toL2_translateRight (g : G3) {F : G3 → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀)
    (h : translateRight g F ∈ automorphicSubmodule ω a b Φ₀) :
    ‖toL2 ω a b Φ₀ ⟨translateRight g F, h⟩‖ = ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖ :=
  (translate_facts ω hω a b Φ₀ hΦ₀ F hF).snd.1 g

theorem continuous_toL2_translateRight {F : G3 → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀)
    (h : ∀ g : G3, translateRight g F ∈ automorphicSubmodule ω a b Φ₀) :
    Continuous fun g : G3 => toL2 ω a b Φ₀ ⟨translateRight g F, h g⟩ :=
  (translate_facts ω hω a b Φ₀ hΦ₀ F hF).snd.2

def Rsub (g : G3) : ↥(cuspSub ω a b Φ₀) →ₗ[ℂ] ↥(cuspSub ω a b Φ₀) where
  toFun f := ⟨⟨translateRight g (f : ↥(automorphicSubmodule ω a b Φ₀)),
      (translateRight_mem ω hω a b Φ₀ hΦ₀ g f.2).1⟩, translateRight_mem ω hω a b Φ₀ hΦ₀ g f.2⟩
  map_add' f f' := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem coe_coe_Rsub (g : G3) (f : ↥(cuspSub ω a b Φ₀)) :
    (((Rsub ω hω a b Φ₀ hΦ₀ g f : ↥(cuspSub ω a b Φ₀)) : ↥(automorphicSubmodule ω a b Φ₀)) : G3 → ℂ) =
      translateRight g ((f : ↥(automorphicSubmodule ω a b Φ₀)) : G3 → ℂ) := rfl

def fg (g : G3) : ↥(cuspSub ω a b Φ₀) →ₗ[ℂ] V ω a b Φ₀ :=
  (e ω a b Φ₀).comp (Rsub ω hω a b Φ₀ hΦ₀ g)

theorem fg_apply (g : G3) (f : ↥(cuspSub ω a b Φ₀)) :
    fg ω hω a b Φ₀ hΦ₀ g f = e ω a b Φ₀ (Rsub ω hω a b Φ₀ hΦ₀ g f) := rfl

theorem fg_apply_coe (g : G3) (f : ↥(cuspSub ω a b Φ₀)) :
    ((fg ω hω a b Φ₀ hΦ₀ g f : V ω a b Φ₀) : Carrier a b Φ₀) =
      toL2 ω a b Φ₀ ⟨translateRight g ((f : ↥(automorphicSubmodule ω a b Φ₀)) : G3 → ℂ),
        (translateRight_mem ω hω a b Φ₀ hΦ₀ g f.2).1⟩ := rfl

theorem norm_fg (g : G3) (f : ↥(cuspSub ω a b Φ₀)) :
    ‖fg ω hω a b Φ₀ hΦ₀ g f‖ = ‖e ω a b Φ₀ f‖ := by
  rw [Submodule.coe_norm, Submodule.coe_norm, fg_apply_coe, e_apply_coe]
  have hf : ((f : ↥(automorphicSubmodule ω a b Φ₀)) : G3 → ℂ) ∈ cuspFunctions ω a b Φ₀ := f.2
  have h := norm_toL2_translateRight ω hω a b Φ₀ hΦ₀ g hf (translateRight_mem ω hω a b Φ₀ hΦ₀ g f.2).1
  exact h

def U (g : G3) : V ω a b Φ₀ →L[ℂ] V ω a b Φ₀ :=
  LinearMap.extendOfNorm (𝕜 := ℂ) (𝕜₂ := ℂ) (σ₁₂ := RingHom.id ℂ) (E := ↥(cuspSub ω a b Φ₀))
    (Eₗ := V ω a b Φ₀) (F := V ω a b Φ₀) (fg ω hω a b Φ₀ hΦ₀ g) (e ω a b Φ₀)

theorem U_apply_e (g : G3) (f : ↥(cuspSub ω a b Φ₀)) :
    U ω hω a b Φ₀ hΦ₀ g (e ω a b Φ₀ f) = fg ω hω a b Φ₀ hΦ₀ g f := by
  have key := @LinearMap.extendOfNorm_eq ℂ ℂ (↥(cuspSub ω a b Φ₀)) (V ω a b Φ₀) (V ω a b Φ₀) _ _ (RingHom.id ℂ)
    _ _ _ _ _ _ _ _ _ (fg ω hω a b Φ₀ hΦ₀ g) (e ω a b Φ₀)
  have hd : DenseRange (e ω a b Φ₀) := denseRange_e ω a b Φ₀
  have hb : ∃ C : ℝ, ∀ f : ↥(cuspSub ω a b Φ₀), ‖fg ω hω a b Φ₀ hΦ₀ g f‖ ≤ C * ‖e ω a b Φ₀ f‖ :=
    ⟨1, fun f => by rw [one_mul, norm_fg]⟩
  exact key hd hb f

theorem U_apply_mk (g : G3) (F : G3 → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀)
    (h1 : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ cuspidalSubspace ω a b Φ₀)
    (h2 : translateRight g F ∈ automorphicSubmodule ω a b Φ₀)
    (h3 : toL2 ω a b Φ₀ ⟨translateRight g F, h2⟩ ∈ cuspidalSubspace ω a b Φ₀) :
    U ω hω a b Φ₀ hΦ₀ g ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, h1⟩ = ⟨toL2 ω a b Φ₀ ⟨translateRight g F, h2⟩, h3⟩ := by
  have hf : (⟨F, hF.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ cuspSub ω a b Φ₀ := hF
  exact U_apply_e ω hω a b Φ₀ hΦ₀ g ⟨⟨F, hF.1⟩, hf⟩

theorem coe_U_apply_mk (g : G3) (F : G3 → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀)
    (h1 : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ cuspidalSubspace ω a b Φ₀)
    (h2 : translateRight g F ∈ automorphicSubmodule ω a b Φ₀) :
    ((U ω hω a b Φ₀ hΦ₀ g ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, h1⟩ : V ω a b Φ₀) : Carrier a b Φ₀) =
      toL2 ω a b Φ₀ ⟨translateRight g F, h2⟩ := by
  rw [U_apply_mk ω hω a b Φ₀ hΦ₀ g F hF h1 h2
    (toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ (translateRight_mem ω hω a b Φ₀ hΦ₀ g hF))]

theorem isCuspLift3_U (g : G3) : IsCuspLift3 ω a b Φ₀ (translateRight g) (U ω hω a b Φ₀ hΦ₀ g) := by
  intro F hF
  exact ⟨translateRight_mem ω hω a b Φ₀ hΦ₀ g hF, coe_U_apply_mk ω hω a b Φ₀ hΦ₀ g F hF _ _⟩

theorem norm_U (g : G3) (x : V ω a b Φ₀) : ‖U ω hω a b Φ₀ hΦ₀ g x‖ = ‖x‖ := by
  refine (denseRange_e ω a b Φ₀).induction_on x
    (isClosed_eq ((U ω hω a b Φ₀ hΦ₀ g).continuous.norm) continuous_norm) ?_
  intro f
  rw [U_apply_e, norm_fg]

theorem U_mul (g h : G3) : U ω hω a b Φ₀ hΦ₀ (g * h) = (U ω hω a b Φ₀ hΦ₀ g).comp (U ω hω a b Φ₀ hΦ₀ h) := by
  refine continuousLinearMap_eq_of_forall_toL2_eq ω a b Φ₀ _ _ fun F hF => ?_
  have hhF : translateRight h F ∈ cuspFunctions ω a b Φ₀ := translateRight_mem ω hω a b Φ₀ hΦ₀ h hF
  have hghF : translateRight g (translateRight h F) ∈ cuspFunctions ω a b Φ₀ :=
    translateRight_mem ω hω a b Φ₀ hΦ₀ g hhF
  have hghF' : translateRight (g * h) F ∈ cuspFunctions ω a b Φ₀ := by
    rw [translateRight_mul]; exact hghF
  rw [ContinuousLinearMap.comp_apply,
    U_apply_mk ω hω a b Φ₀ hΦ₀ (g * h) F hF _ hghF'.1 (toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hghF'),
    U_apply_mk ω hω a b Φ₀ hΦ₀ h F hF _ hhF.1 (toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hhF),
    U_apply_mk ω hω a b Φ₀ hΦ₀ g (translateRight h F) hhF _ hghF.1
      (toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hghF)]
  apply Subtype.ext
  show toL2 ω a b Φ₀ ⟨translateRight (g * h) F, hghF'.1⟩ = toL2 ω a b Φ₀ ⟨translateRight g (translateRight h F), hghF.1⟩
  congr 1
  exact Subtype.ext (translateRight_mul g h F)

theorem U_one : U ω hω a b Φ₀ hΦ₀ 1 = ContinuousLinearMap.id ℂ (V ω a b Φ₀) := by
  refine continuousLinearMap_eq_of_forall_toL2_eq ω a b Φ₀ _ _ fun F hF => ?_
  have h1 : translateRight 1 F ∈ cuspFunctions ω a b Φ₀ := by rw [translateRight_one]; exact hF
  rw [ContinuousLinearMap.id_apply,
    U_apply_mk ω hω a b Φ₀ hΦ₀ 1 F hF _ h1.1 (toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ h1)]
  apply Subtype.ext
  show toL2 ω a b Φ₀ ⟨translateRight 1 F, h1.1⟩ = toL2 ω a b Φ₀ ⟨F, hF.1⟩
  congr 1
  exact Subtype.ext (translateRight_one F)

theorem continuous_U_apply_e (f : ↥(cuspSub ω a b Φ₀)) :
    Continuous fun g : G3 => U ω hω a b Φ₀ hΦ₀ g (e ω a b Φ₀ f) := by
  have hf : ((f : ↥(automorphicSubmodule ω a b Φ₀)) : G3 → ℂ) ∈ cuspFunctions ω a b Φ₀ := f.2
  have hc := continuous_toL2_translateRight ω hω a b Φ₀ hΦ₀ hf
    (fun g => (translateRight_mem ω hω a b Φ₀ hΦ₀ g f.2).1)
  simp_rw [U_apply_e]
  refine Continuous.subtype_mk ?_ _
  exact hc

theorem continuous_U_apply (x : V ω a b Φ₀) : Continuous fun g : G3 => U ω hω a b Φ₀ hΦ₀ g x := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu

  have hx : x ∈ closure (Set.range (e ω a b Φ₀)) := (denseRange_e ω a b Φ₀).closure_range ▸ Set.mem_univ x
  obtain ⟨y, ⟨f, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (half_pos hε)
  refine ⟨fun g => U ω hω a b Φ₀ hΦ₀ g (e ω a b Φ₀ f), continuous_U_apply_e ω hω a b Φ₀ hΦ₀ f, fun g => hεu ?_⟩
  rw [dist_eq_norm, ← map_sub, norm_U, ← dist_eq_norm]
  linarith

theorem main :
    ∃ U : G3 → (V ω a b Φ₀ →L[ℂ] V ω a b Φ₀),
      (∀ g : G3, IsCuspLift3 ω a b Φ₀ (translateRight g) (U g)) ∧
      (∀ (g : G3) (x : V ω a b Φ₀), ‖U g x‖ = ‖x‖) ∧
      (∀ g h : G3, U (g * h) = (U g).comp (U h)) ∧
      U 1 = ContinuousLinearMap.id ℂ (V ω a b Φ₀) ∧
      ∀ x : V ω a b Φ₀, Continuous fun g : G3 => U g x :=
  ⟨U ω hω a b Φ₀ hΦ₀, isCuspLift3_U ω hω a b Φ₀ hΦ₀, norm_U ω hω a b Φ₀ hΦ₀, U_mul ω hω a b Φ₀ hΦ₀,
    U_one ω hω a b Φ₀ hΦ₀, continuous_U_apply ω hω a b Φ₀ hΦ₀⟩

end Lift

end LTCubicCuspLift
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_isCuspLift3_translateRight_norm_eq.LTCubicCuspLift"

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀) :
    ∃ U : AdelicGL 3 (𝓞 ℚ) ℚ → (↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)),
      (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, IsCuspLift3 ω a b Φ₀ (translateRight g) (U g)) ∧
      (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : ↥(cuspidalSubspace ω a b Φ₀)), ‖U g x‖ = ‖x‖) ∧
      (∀ g h : AdelicGL 3 (𝓞 ℚ) ℚ, U (g * h) = (U g).comp (U h)) ∧
      U 1 = ContinuousLinearMap.id ℂ ↥(cuspidalSubspace ω a b Φ₀) ∧
      ∀ x : ↥(cuspidalSubspace ω a b Φ₀), Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => U g x :=
  LTCubicCuspLift.main ω _hω a b Φ₀ _hΦ₀

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_isCuspLift3_translateRight_norm_eq.LTCubicCuspLift"

end S_LanglandsTunnell_CubicInduction_SlabL2_exists_isCuspLift3_translateRight_norm_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_isCuspLift3_translateRight_norm_eq (solution)
