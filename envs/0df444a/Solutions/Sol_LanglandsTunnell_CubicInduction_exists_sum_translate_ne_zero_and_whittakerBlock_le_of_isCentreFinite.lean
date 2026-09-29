-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5c960ebe-c304-5acf-829c-ce17bef86d0e

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicFourier
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_sum_translate_whittaker_ne_zero_and_whittakerBlock_empty_le_of_isCentreFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

noncomputable section

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped ENNReal

namespace WhittakerBlockTransfer

open LanglandsTunnell.CubicInduction NumberField.StandardAddChar NumberField.AdelicHaar

section Iterated

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

omit [SecondCountableTopology X] in

private theorem integrable_of_continuous_of_ae_mem {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] (ν : Measure X)
    [IsFiniteMeasure ν] {C : Set X} (hC : IsCompact C) (hν : ∀ᵐ x ∂ν, x ∈ C) {f : X → E}
    (hf : Continuous f) : Integrable f ν := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable M (hν.mono fun x hx => hM x hx)

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] in

private theorem integrable_integral_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure X) [IsFiniteMeasure ν] {C : Set X} (hν : ∀ᵐ x ∂ν, x ∈ C) {F : X → X → E}
    (hF : StronglyMeasurable (Function.uncurry F)) {M : ℝ} (hM : ∀ x ∈ C, ∀ y ∈ C, ‖F x y‖ ≤ M) :
    Integrable (fun x => ∫ y, F x y ∂ν) ν :=
  Integrable.of_bound (hF.integral_prod_right (ν := ν)).aestronglyMeasurable (M * ν.real Set.univ)
    (hν.mono fun x hx => norm_integral_le_of_norm_le_const (hν.mono fun y hy => hM x hx y hy))

private theorem integral3_finsetSum (ν : Measure X) [IsFiniteMeasure ν] {C : Set X} (hC : IsCompact C)
    (hν : ∀ᵐ x ∂ν, x ∈ C) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → X → X → X → ℂ)
    (hF : ∀ i, Continuous fun p : X × X × X => F i p.1 p.2.1 p.2.2) :
    ∫ x, ∫ y, ∫ z, (∑ i ∈ s, c i * F i x y z) ∂ν ∂ν ∂ν =
      ∑ i ∈ s, c i * ∫ x, ∫ y, ∫ z, F i x y z ∂ν ∂ν ∂ν := by
  have h3 : ∀ i x y, Continuous fun z => F i x y z := fun i x y =>
    (hF i).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have h23 : ∀ i x, Continuous (Function.uncurry fun y z => F i x y z) := fun i x =>
    (hF i).comp (continuous_const.prodMk continuous_id)
  have h123 : ∀ i, Continuous (Function.uncurry fun (q : X × X) z => F i q.1 q.2 z) := fun i =>
    (hF i).comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))

  have hin : ∀ x y, ∫ z, (∑ i ∈ s, c i * F i x y z) ∂ν = ∑ i ∈ s, c i * ∫ z, F i x y z ∂ν := by
    intro x y
    rw [integral_finsetSum s fun i _ =>
      (integrable_of_continuous_of_ae_mem ν hC hν (h3 i x y)).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

  have hG : ∀ i x, Integrable (fun y => ∫ z, F i x y z ∂ν) ν := by
    intro i x
    obtain ⟨M, hM⟩ := ((isCompact_singleton (x := x)).prod (hC.prod hC)).exists_bound_of_continuousOn
      (hF i).continuousOn
    refine integrable_integral_of_bound ν hν (h23 i x).stronglyMeasurable (M := M) fun y hy z hz => ?_
    exact hM (x, y, z) (Set.mk_mem_prod rfl (Set.mk_mem_prod hy hz))
  have hmid : ∀ x, ∫ y, ∫ z, (∑ i ∈ s, c i * F i x y z) ∂ν ∂ν = ∑ i ∈ s, c i * ∫ y, ∫ z, F i x y z ∂ν ∂ν := by
    intro x
    rw [show (fun y => ∫ z, (∑ i ∈ s, c i * F i x y z) ∂ν) = fun y => ∑ i ∈ s, c i * ∫ z, F i x y z ∂ν from
      funext (hin x), integral_finsetSum s fun i _ => (hG i x).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

  have hH : ∀ i, Integrable (fun x => ∫ y, ∫ z, F i x y z ∂ν ∂ν) ν := by
    intro i
    obtain ⟨M, hM⟩ := (hC.prod (hC.prod hC)).exists_bound_of_continuousOn (hF i).continuousOn
    have hGb : ∀ x ∈ C, ∀ y ∈ C, ‖∫ z, F i x y z ∂ν‖ ≤ M * ν.real Set.univ := fun x hx y hy =>
      norm_integral_le_of_norm_le_const (hν.mono fun z hz => hM (x, y, z) (Set.mk_mem_prod hx (Set.mk_mem_prod hy hz)))
    exact integrable_integral_of_bound ν hν ((h123 i).stronglyMeasurable.integral_prod_right (ν := ν)) hGb
  rw [show (fun x => ∫ y, ∫ z, (∑ i ∈ s, c i * F i x y z) ∂ν ∂ν) = fun x => ∑ i ∈ s, c i * ∫ y, ∫ z, F i x y z ∂ν ∂ν
    from funext hmid, integral_finsetSum s fun i _ => (hH i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end Iterated

section Combinations

private theorem continuous_upperUnipotent3 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun t : A × A × A => upperUnipotent3 t.1 t.2.1 t.2.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : A × A × A => ((upperUnipotent3 t.1 t.2.1 t.2.2 : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
    simp only [upperUnipotent3_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun t : A × A × A =>
      (!![1, -t.1, t.1 * t.2.1 - t.2.2; 0, 1, -t.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (Ug : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
  (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)

private theorem whittaker3_finsetSum (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (φ : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : ∀ i, Continuous (φ i)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D Ug gen (AdelicBox.adelicBox ℚ)) ψ (fun x => ∑ i ∈ s, c i * φ i x) g =
      ∑ i ∈ s, c i * whittaker3 (productionPinsOf ℚ D Ug gen (AdelicBox.adelicBox ℚ)) ψ (φ i) g := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := (productionPinsOf ℚ D Ug gen (AdelicBox.adelicBox ℚ)).nS
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ
  haveI : IsProbabilityMeasure (productionPinsOf ℚ D Ug gen (AdelicBox.adelicBox ℚ)).ν :=
    AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hν : ∀ᵐ x ∂(productionPinsOf ℚ D Ug gen (AdelicBox.adelicBox ℚ)).ν, x ∈ C :=
    (ProbabilityTheory.ae_cond_mem (μ := adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.measurableSet_adelicBox ℚ)).mono
      fun x hx => hsub hx
  have hF : ∀ i, Continuous fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      φ i (upperUnipotent3 t.1 t.2.1 t.2.2 * g) * ψ (-(t.1 + t.2.1)) := fun i =>
    ((hφ i).comp (continuous_upperUnipotent3.mul continuous_const)).mul (hψ.comp (by fun_prop))
  have := integral3_finsetSum (productionPinsOf ℚ D Ug gen (AdelicBox.adelicBox ℚ)).ν hC hν s c
    (fun i x y z => φ i (upperUnipotent3 x y z * g) * ψ (-(x + y))) hF
  simpa only [whittaker3, Finset.sum_mul, mul_assoc] using this

private theorem whittaker3_translate (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (a g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ (fun x => φ (x * a)) g = whittaker3 pins ψ φ (g * a) := by
  simp only [whittaker3, mul_assoc]

private theorem whittaker3_const_mul (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (c : ℂ)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ (fun x => c * φ x) g = c * whittaker3 pins ψ φ g := by
  simp only [whittaker3, mul_assoc, integral_const_mul]

private def comb {J : Type*} [Fintype J] (c : J → ℂ) (τ : J → AdelicGL 3 (𝓞 ℚ) ℚ)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun x => ∑ j, c j * φ (x * τ j)

private theorem continuous_comb {J : Type*} [Fintype J] (c : J → ℂ) (τ : J → AdelicGL 3 (𝓞 ℚ) ℚ)
    {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : Continuous φ) : Continuous (comb c τ φ) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (hφ.comp (continuous_id.mul continuous_const))

private theorem comb_comb {J J' : Type*} [Fintype J] [Fintype J'] (c : J → ℂ) (τ : J → AdelicGL 3 (𝓞 ℚ) ℚ)
    (c' : J' → ℂ) (τ' : J' → AdelicGL 3 (𝓞 ℚ) ℚ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    comb c τ (comb c' τ' φ) = comb (fun jj : J × J' => c jj.1 * c' jj.2) (fun jj => τ jj.1 * τ' jj.2) φ := by
  funext x
  simp only [comb, Finset.mul_sum, Fintype.sum_prod_type, mul_assoc]

private theorem comb_globalPointsGL_mul {J : Type*} [Fintype J] (c : J → ℂ) (τ : J → AdelicGL 3 (𝓞 ℚ) ℚ)
    {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    comb c τ φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = comb c τ φ g := by
  simp only [comb, mul_assoc, haut]

private theorem whittaker3_comb {J : Type*} [Fintype J] (c : J → ℂ) (τ : J → AdelicGL 3 (𝓞 ℚ) ℚ)
    {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : Continuous φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D Ug gen (AdelicBox.adelicBox ℚ)) psiQ (comb c τ φ) g =
      ∑ j, c j * whittaker3 (productionPinsOf ℚ D Ug gen (AdelicBox.adelicBox ℚ)) psiQ φ (g * τ j) := by
  unfold comb
  rw [whittaker3_finsetSum D Ug gen psiQ continuous_psiQ Finset.univ c (fun j x => φ (x * τ j))
    (fun j => hφ.comp (continuous_id.mul continuous_const)) g]
  exact Finset.sum_congr rfl fun j _ => by rw [whittaker3_translate]

end Combinations

section Components

variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_localToAdelic3 (k : GL (Fin 3) (p.adicCompletion ℚ)) :
    ((localToAdelic3 p k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ p (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) :=
  rfl

private theorem coe_componentAt3 (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ q g : GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) =
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem componentAt3_localToAdelic3_self (k : GL (Fin 3) (p.adicCompletion ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 p k) = k := by
  refine Units.ext ?_
  rw [coe_componentAt3, coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply, mapMatrix_fin_finMatN,
    mapMatrix_localMatN_self]

private theorem componentAt3_localToAdelic3_of_ne {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p)
    (k : GL (Fin 3) (p.adicCompletion ℚ)) : componentAt3 (𝓞 ℚ) ℚ q (localToAdelic3 p k) = 1 := by
  refine Units.ext ?_
  rw [coe_componentAt3, coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply, mapMatrix_fin_finMatN,
    mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hq, Units.val_one]

private theorem archComponent3_localToAdelic3 (k : GL (Fin 3) (p.adicCompletion ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 p k) = 1 := by
  refine Units.ext ?_
  rw [coe_archComponent3, coe_localToAdelic3, mapMatrix_arch_finMatN, Units.val_one]

private theorem mul_localToAdelic3_eq_localToAdelic3_mul (Y : AdelicGL 3 (𝓞 ℚ) ℚ)
    (a b : GL (Fin 3) (p.adicCompletion ℚ)) (h : componentAt3 (𝓞 ℚ) ℚ p Y * a = b * componentAt3 (𝓞 ℚ) ℚ p Y) :
    Y * localToAdelic3 p a = localToAdelic3 p b * Y := by
  refine Units.ext (matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_)
  · rw [Units.val_mul, Units.val_mul, map_mul, map_mul, coe_localToAdelic3, coe_localToAdelic3,
      mapMatrix_arch_finMatN, mapMatrix_arch_finMatN, mul_one, one_mul]
  · rw [Units.val_mul, Units.val_mul, map_mul, map_mul, coe_localToAdelic3, coe_localToAdelic3,
      mapMatrix_fin_finMatN, mapMatrix_fin_finMatN]
    refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = p
    · subst hw
      rw [mapMatrix_localMatN_self, mapMatrix_localMatN_self]
      have hval := congrArg Units.val h
      simpa only [Units.val_mul, coe_componentAt3, ← RingHom.mapMatrix_comp, RingHom.comp_apply] using hval
    · rw [mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hw, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hw,
        mul_one, one_mul]

private theorem mapMatrix_upperUnipotent3_val {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x y z : A) :
    f.mapMatrix ((upperUnipotent3 x y z : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      ((upperUnipotent3 (f x) (f y) (f z) : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, RingHom.mapMatrix_apply, Matrix.map_apply]

private theorem finAdeleEval_mapMatrix_upperUnipotent3 (w : HeightOneSpectrum (𝓞 ℚ)) (X Y Z : AdeleRing (𝓞 ℚ) ℚ) :
    (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
      ((upperUnipotent3 X Y Z : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
      ((upperUnipotent3 (X.2 w) (Y.2 w) (Z.2 w) : GL (Fin 3) (w.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) := by
  rw [mapMatrix_upperUnipotent3_val, mapMatrix_upperUnipotent3_val]
  rfl

private theorem localToAdelic3_upperUnipotent3 (x y z : p.adicCompletion ℚ) :
    localToAdelic3 p (upperUnipotent3 x y z) =
      upperUnipotent3 (adeleSingleAt ℚ p x) (adeleSingleAt ℚ p y) (adeleSingleAt ℚ p z) := by
  refine Units.ext (matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_)
  · rw [coe_localToAdelic3, mapMatrix_arch_finMatN, mapMatrix_upperUnipotent3_val]
    show (1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      ((upperUnipotent3 (0 : InfiniteAdeleRing ℚ) 0 0 : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
    rw [upperUnipotent3_zero, Units.val_one]
  · refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    rw [coe_localToAdelic3, mapMatrix_fin_finMatN, finAdeleEval_mapMatrix_upperUnipotent3]
    show _ = ((upperUnipotent3 (finAdeleSingleAt ℚ p x w) (finAdeleSingleAt ℚ p y w) (finAdeleSingleAt ℚ p z w) :
      GL (Fin 3) (w.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ))
    by_cases hw : w = p
    · subst hw
      rw [mapMatrix_localMatN_self, finAdeleSingleAt_apply_self, finAdeleSingleAt_apply_self,
        finAdeleSingleAt_apply_self]
    · rw [mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hw, finAdeleSingleAt_apply_of_ne ℚ p x hw,
        finAdeleSingleAt_apply_of_ne ℚ p y hw, finAdeleSingleAt_apply_of_ne ℚ p z hw, upperUnipotent3_zero,
        Units.val_one]

private theorem psiQ_adeleSingleAt (x : p.adicCompletion ℚ) : psiQ (adeleSingleAt ℚ p x) = psiV p x := by
  rw [psiQ_apply, adeleSingleAt_apply, AddChar.map_zero_eq_one, one_mul, psiFin_apply,
    finprod_eq_single _ p fun w hw => by rw [finAdeleSingleAt_apply_of_ne ℚ p x hw, AddChar.map_zero_eq_one],
    finAdeleSingleAt_apply_self]

private theorem componentAt3_upperUnipotent3 (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ p (upperUnipotent3 x y z) = upperUnipotent3 (x.2 p) (y.2 p) (z.2 p) := by
  refine Units.ext ?_
  rw [coe_componentAt3, ← RingHom.mapMatrix_comp, RingHom.comp_apply, finAdeleEval_mapMatrix_upperUnipotent3]

end Components

section MatrixKit

variable {A : Type*} [CommRing A]

private theorem upperUnipotent3_mul_upperUnipotent3 (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem upperUnipotent3_eq_radicalP21_mul_iotaGL (x y z : A) :
    upperUnipotent3 x y z = radicalP21 ![z, y] * iotaGL (unipotentGL2 x) := by
  rw [radicalP21, iotaGL_unipotentGL2, upperUnipotent3_mul_upperUnipotent3]
  simp

private theorem radicalP21_mul_iotaGL_mul_radicalP21 (w : Fin 2 → A) (h : GL (Fin 2) A) (y : Fin 2 → A) :
    radicalP21 w * iotaGL h * radicalP21 y =
      upperUnipotent3 0 (((h : Matrix (Fin 2) (Fin 2) A) *ᵥ y) 1) (((h : Matrix (Fin 2) (Fin 2) A) *ᵥ y) 0) *
        (radicalP21 w * iotaGL h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP21, upperUnipotent3, embedMat2, Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Fin.sum_univ_three]
  all_goals ring

private theorem radicalP21_mul_iotaGL_mul_upperUnipotent3 (w : Fin 2 → A) (h : GL (Fin 2) A)
    (h10 : (h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (h11 : (h : Matrix (Fin 2) (Fin 2) A) 1 1 = 1) (x : A) :
    radicalP21 w * iotaGL h * upperUnipotent3 x 0 0 =
      upperUnipotent3 ((h : Matrix (Fin 2) (Fin 2) A) 0 0 * x) 0 (-((h : Matrix (Fin 2) (Fin 2) A) 0 0 * x * w 1)) *
        (radicalP21 w * iotaGL h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP21, upperUnipotent3, embedMat2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h10,
      h11]
  all_goals ring

variable {F : Type*} [Field F]

private theorem exists_eq_upper_mul_lower (h : GL (Fin 2) F) (h11 : (h : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    ∃ b c : GL (Fin 2) F, h = b * c ∧
      (b : Matrix (Fin 2) (Fin 2) F) =
        !![(h : Matrix (Fin 2) (Fin 2) F).det / (h : Matrix (Fin 2) (Fin 2) F) 1 1,
            (h : Matrix (Fin 2) (Fin 2) F) 0 1 / (h : Matrix (Fin 2) (Fin 2) F) 1 1; 0, 1] ∧
      (c : Matrix (Fin 2) (Fin 2) F) =
        !![1, 0; (h : Matrix (Fin 2) (Fin 2) F) 1 0, (h : Matrix (Fin 2) (Fin 2) F) 1 1] := by
  have hdet : (h : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
  refine ⟨⟨!![(h : Matrix (Fin 2) (Fin 2) F).det / (h : Matrix (Fin 2) (Fin 2) F) 1 1,
        (h : Matrix (Fin 2) (Fin 2) F) 0 1 / (h : Matrix (Fin 2) (Fin 2) F) 1 1; 0, 1],
      !![(h : Matrix (Fin 2) (Fin 2) F) 1 1 / (h : Matrix (Fin 2) (Fin 2) F).det,
        -((h : Matrix (Fin 2) (Fin 2) F) 0 1 / (h : Matrix (Fin 2) (Fin 2) F).det); 0, 1], ?_, ?_⟩,
    ⟨!![1, 0; (h : Matrix (Fin 2) (Fin 2) F) 1 0, (h : Matrix (Fin 2) (Fin 2) F) 1 1],
      !![1, 0; -((h : Matrix (Fin 2) (Fin 2) F) 1 0 / (h : Matrix (Fin 2) (Fin 2) F) 1 1),
        ((h : Matrix (Fin 2) (Fin 2) F) 1 1)⁻¹], ?_, ?_⟩, ?_, rfl, rfl⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | (field_simp <;> ring1)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | (field_simp <;> ring1)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | (field_simp <;> ring1)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | field_simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    all_goals (field_simp <;> ring1)

end MatrixKit

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem iotaGL_mem_localMaximalCompact3_of_lower (c : GL (Fin 2) (p.adicCompletion ℚ))
    (hc : (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1, 0; (c : Matrix (Fin 2) (Fin 2) _) 1 0, (c : Matrix (Fin 2) (Fin 2) _) 1 1])
    (h10 : (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ∈ p.adicCompletionIntegers ℚ)
    (h11 : Valued.v ((c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) = 1) :
    iotaGL c ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  obtain ⟨M, hM⟩ : ∃ M, (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = M := ⟨_, rfl⟩
  rw [hM] at hc h10 h11
  have h11' : M 1 1 ≠ 0 := (Valuation.ne_zero_iff Valued.v).1 (by rw [h11]; exact one_ne_zero)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h10
  let c' : GL (Fin 2) (p.adicCompletion ℚ) :=
    ⟨!![1, 0; M 1 0, M 1 1], !![1, 0; -(M 1 0 / M 1 1), (M 1 1)⁻¹],
      by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        all_goals first | ring1 | (field_simp <;> ring1),
      by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        all_goals first | ring1 | field_simp⟩
  have hcc : c = c' := Units.ext (hM.trans hc)
  have hc'val : ((c' : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1, 0; M 1 0, M 1 1] := rfl
  have hc'inv : ((c'⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1, 0; -(M 1 0 / M 1 1), (M 1 1)⁻¹] := rfl
  rw [hcc, mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_iotaGL, hc'val]
    fin_cases i <;> fin_cases j <;> simp [embedMat2, h10, h11]
  · rw [← map_inv, coe_iotaGL, hc'inv]
    fin_cases i <;> fin_cases j <;> simp [embedMat2, map_div₀, map_inv₀, h10, h11]

private theorem exists_upperUnipotent3_mul_of_unit (w : Fin 2 → p.adicCompletion ℚ)
    (b : GL (Fin 2) (p.adicCompletion ℚ))
    (h10 : (b : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0)
    (h11 : (b : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1)
    (h00 : Valued.v ((b : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0) = 1)
    (k : GL (Fin 3) (p.adicCompletion ℚ)) (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ∃ (x y z : p.adicCompletion ℚ) (k' : GL (Fin 3) (p.adicCompletion ℚ)),
      k' ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ radicalP21 w * iotaGL b * k = upperUnipotent3 x y z * k' := by
  obtain ⟨M, hM⟩ : ∃ M, (b : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = M := ⟨_, rfl⟩
  rw [hM] at h10 h11 h00
  have ha : M 0 0 ≠ 0 := (Valuation.ne_zero_iff Valued.v).1 (by rw [h00]; exact one_ne_zero)
  let d : GL (Fin 2) (p.adicCompletion ℚ) :=
    ⟨!![M 0 0, 0; 0, 1], !![(M 0 0)⁻¹, 0; 0, 1],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ ha],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ ha]⟩
  have hdval : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![M 0 0, 0; 0, 1] := rfl
  have hdinv : ((d⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![(M 0 0)⁻¹, 0; 0, 1] := rfl
  have hd : iotaGL d ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
    rw [mem_localMaximalCompact3_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [coe_iotaGL, hdval]
      fin_cases i <;> fin_cases j <;> simp [embedMat2, h00]
    · rw [← map_inv, coe_iotaGL, hdinv]
      fin_cases i <;> fin_cases j <;> simp [embedMat2, map_inv₀, h00]
  have hb : iotaGL b = upperUnipotent3 (M 0 1) 0 0 * iotaGL d := by
    ext i j
    rw [Units.val_mul, coe_iotaGL, coe_iotaGL, hM, hdval]
    fin_cases i <;> fin_cases j <;>
      simp [embedMat2, upperUnipotent3, Matrix.mul_apply, Fin.sum_univ_three, h10, h11]
  refine ⟨0 + M 0 1, w 1 + 0, w 0 + 0 + 0 * 0, iotaGL d * k, mul_mem hd hk, ?_⟩
  rw [hb, radicalP21, ← upperUnipotent3_mul_upperUnipotent3]
  simp only [mul_assoc]

private theorem exists_level_subset_of_mem_nhds {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    {c : p.adicCompletion ℚ} {t : Set (p.adicCompletion ℚ)} (ht : t ∈ nhds c) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → ∀ x : p.adicCompletion ℚ,
      (ϖ ^ m)⁻¹ * (x - c) ∈ p.adicCompletionIntegers ℚ → x ∈ t := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
  have hϖ : ‖ϖ‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 hϖ1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖ
  refine ⟨n, fun m hm x hx => hball ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx
  have hx' : ‖(ϖ ^ m)⁻¹ * (x - c)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 hx
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖x - c‖ = ‖ϖ ^ m‖ * ‖(ϖ ^ m)⁻¹ * (x - c)‖ := by
        rw [← norm_mul, mul_inv_cancel_left₀ (pow_ne_zero m hϖ0)]
    _ ≤ ‖ϖ ^ m‖ * 1 := by gcongr
    _ = ‖ϖ‖ ^ m := by rw [mul_one, norm_pow]
    _ ≤ ‖ϖ‖ ^ n := pow_le_pow_of_le_one (norm_nonneg ϖ) hϖ.le hm
    _ < ε := hn

private theorem exists_level_subset_of_mem_nhds_matrix {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0)
    (hϖ1 : Valued.v ϖ < 1) {C : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)}
    {t : Set (Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))} (ht : t ∈ nhds C) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → ∀ A : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ),
      (∀ i j, (ϖ ^ m)⁻¹ * (A i j - C i j) ∈ p.adicCompletionIntegers ℚ) → A ∈ t := by
  have ht' : t ∈ Filter.pi fun i : Fin 3 => @nhds (Fin 3 → p.adicCompletion ℚ) _ (C i) := by
    rw [← nhds_pi]
    exact ht
  obtain ⟨I, -, s, hs, hst⟩ := Filter.mem_pi.1 ht'
  simp only [nhds_pi, Filter.mem_pi] at hs
  choose I' _ s' hs' hs's using hs
  choose N hN using fun i j => exists_level_subset_of_mem_nhds p hϖ0 hϖ1 (hs' i j)
  refine ⟨Finset.univ.sup fun ij : Fin 3 × Fin 3 => N ij.1 ij.2, fun m hm A hA => hst ?_⟩
  refine Set.mem_pi.2 fun i _ => hs's i (Set.mem_pi.2 fun j _ => ?_)
  exact hN i j m ((Finset.le_sup (f := fun ij : Fin 3 × Fin 3 => N ij.1 ij.2) (Finset.mem_univ (i, j))).trans hm)
    (A i j) (hA i j)

private theorem level_of_mul_eq_one {ϖ : p.adicCompletion ℚ} (n : ℕ)
    {X Y : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)} (hXY : X * Y = 1)
    (hX : ∀ i j, X i j ∈ p.adicCompletionIntegers ℚ)
    (hY : ∀ i j, (ϖ ^ n)⁻¹ * (Y i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ∈
      p.adicCompletionIntegers ℚ) (i j : Fin 3) :
    (ϖ ^ n)⁻¹ * (X i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ∈ p.adicCompletionIntegers ℚ := by
  have hentry : X i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j = (X * (1 - Y)) i j := by
    rw [mul_sub, mul_one, hXY, Matrix.sub_apply]
  rw [hentry, Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun l _ => ?_
  have hlj : (ϖ ^ n)⁻¹ * (1 - Y) l j ∈ p.adicCompletionIntegers ℚ := by
    rw [Matrix.sub_apply, ← neg_sub, mul_neg]
    exact neg_mem (hY l j)
  rw [mul_left_comm]
  exact mul_mem (hX i l) hlj

private theorem exists_levelBall_subset {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    {U : Set (GL (Fin 3) (p.adicCompletion ℚ))} (hU : IsOpen U) (h1 : (1 : GL (Fin 3) (p.adicCompletion ℚ)) ∈ U) :
    ∃ n : ℕ, ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
      (∀ i j, (ϖ ^ n)⁻¹ * ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ∈ p.adicCompletionIntegers ℚ) → k ∈ U := by
  obtain ⟨O, hO, hOU⟩ :=
    (Units.isInducing_embedProduct (M := Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))).isOpen_iff.1 hU
  have h1' : Units.embedProduct _ (1 : GL (Fin 3) (p.adicCompletion ℚ)) ∈ O := by
    rw [← hOU] at h1
    exact h1
  rw [Units.embedProduct_apply] at h1'
  obtain ⟨O₁, O₂, hO₁, hO₂, hm₁, hm₂, hsub⟩ := isOpen_prod_iff.1 hO _ _ h1'
  rw [Units.val_one] at hm₁
  rw [inv_one, Units.val_one] at hm₂
  obtain ⟨n₁, hn₁⟩ := exists_level_subset_of_mem_nhds_matrix p hϖ0 hϖ1 (hO₁.mem_nhds hm₁)
  have hm₂' : (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) ∈ MulOpposite.op ⁻¹' O₂ := hm₂
  obtain ⟨n₂, hn₂⟩ := exists_level_subset_of_mem_nhds_matrix p hϖ0 hϖ1
    ((hO₂.preimage MulOpposite.continuous_op).mem_nhds hm₂')
  refine ⟨max n₁ n₂, fun k hk hlev => ?_⟩
  have hinv := level_of_mul_eq_one p (max n₁ n₂) (Units.inv_mul k)
    (fun i j => by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hk.2 i j) hlev
  rw [← hOU, Set.mem_preimage, Units.embedProduct_apply]
  exact hsub (Set.mk_mem_prod (hn₁ _ (le_max_left n₁ n₂) _ hlev) (hn₂ _ (le_max_right n₁ n₂) _ hinv))

end Local

section LevelKit

variable (p : HeightOneSpectrum (𝓞 ℚ))

private def IsLevel (ϖ : p.adicCompletion ℚ) (n : ℕ) (k : GL (Fin 3) (p.adicCompletion ℚ)) : Prop :=
  ∀ i j, (ϖ ^ n)⁻¹ * ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
    (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ∈ p.adicCompletionIntegers ℚ

private theorem isLevel_one (ϖ : p.adicCompletion ℚ) (n : ℕ) : IsLevel p ϖ n 1 := by
  intro i j
  rw [Units.val_one, sub_self, mul_zero]
  exact zero_mem _

private theorem level_of_eq {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (n : ℕ) {d w : p.adicCompletion ℚ}
    (hdw : d = ϖ ^ n * w) (hw : w ∈ p.adicCompletionIntegers ℚ) : (ϖ ^ n)⁻¹ * d ∈ p.adicCompletionIntegers ℚ := by
  rw [hdw, inv_mul_cancel_left₀ (pow_ne_zero n hϖ0)]
  exact hw

private theorem mem_integers_of_valued_lt_one {ϖ : p.adicCompletion ℚ} (hϖ1 : Valued.v ϖ < 1) :
    ϖ ∈ p.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact hϖ1.le

private theorem entryDiv_mul_right {ϖ : p.adicCompletion ℚ} {n : ℕ} {D Z : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)}
    (hD : ∀ i j, (ϖ ^ n)⁻¹ * D i j ∈ p.adicCompletionIntegers ℚ) (hZ : ∀ i j, Z i j ∈ p.adicCompletionIntegers ℚ)
    (i j : Fin 3) : (ϖ ^ n)⁻¹ * (D * Z) i j ∈ p.adicCompletionIntegers ℚ := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun l _ => ?_
  rw [← mul_assoc]
  exact mul_mem (hD i l) (hZ l j)

private theorem entryDiv_mul_left {ϖ : p.adicCompletion ℚ} {n : ℕ} {X D : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)}
    (hX : ∀ i j, X i j ∈ p.adicCompletionIntegers ℚ) (hD : ∀ i j, (ϖ ^ n)⁻¹ * D i j ∈ p.adicCompletionIntegers ℚ)
    (i j : Fin 3) : (ϖ ^ n)⁻¹ * (X * D) i j ∈ p.adicCompletionIntegers ℚ := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun l _ => ?_
  rw [mul_left_comm]
  exact mul_mem (hX i l) (hD l j)

private theorem IsLevel.entryDiv {ϖ : p.adicCompletion ℚ} {n : ℕ} {k : GL (Fin 3) (p.adicCompletion ℚ)}
    (hk : IsLevel p ϖ n k) (i j : Fin 3) :
    (ϖ ^ n)⁻¹ * ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) i j ∈ p.adicCompletionIntegers ℚ := by
  rw [Matrix.sub_apply]
  exact hk i j

private theorem entries_mem_of_mem_localMaximalCompact3 {k : GL (Fin 3) (p.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (i j : Fin 3) :
    (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ p).1 hk).1 i j

private theorem inv_entries_mem_of_mem_localMaximalCompact3 {k : GL (Fin 3) (p.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (i j : Fin 3) :
    ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈
      p.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ p).1 hk).2 i j

private theorem isLevel_iotaGL_of_entries {ϖ : p.adicCompletion ℚ} {n : ℕ} (u : GL (Fin 2) (p.adicCompletion ℚ))
    (hu : ∀ i j, (ϖ ^ n)⁻¹ * ((u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) ∈ p.adicCompletionIntegers ℚ) :
    IsLevel p ϖ n (iotaGL u) := by
  have h00 := hu 0 0
  have h01 := hu 0 1
  have h10 := hu 1 0
  have h11 := hu 1 1
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h00 h01 h10 h11
  intro i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, h00, h01, h10, h11]

private theorem iotaGL_mem_localMaximalCompact3_of_entries (u : GL (Fin 2) (p.adicCompletion ℚ))
    (hu : ∀ i j, (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ)
    (hdet : Valued.v (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det = 1) :
    iotaGL u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  obtain ⟨U, hU⟩ : ∃ U, (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = U := ⟨_, rfl⟩
  have hu' : ∀ i j, Valued.v (U i j) ≤ 1 := fun i j => by
    have h := hu i j
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers, hU] at h
  rw [hU] at hdet
  have hinv : (((u⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) =
      !![U.det⁻¹ * U 1 1, U.det⁻¹ * -(U 0 1); U.det⁻¹ * -(U 1 0), U.det⁻¹ * U 0 0] := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_iotaGL, hU]
    fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> exact hu' _ _
  · rw [← map_inv, coe_iotaGL, hinv]
    fin_cases i <;> fin_cases j <;> simp [embedMat2, map_mul, map_inv₀, hdet] <;> exact hu' _ _

private theorem IsLevel.mono {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {n N : ℕ} (hnN : n ≤ N)
    {k : GL (Fin 3) (p.adicCompletion ℚ)} (hk : IsLevel p ϖ N k) : IsLevel p ϖ n k := by
  intro i j
  refine level_of_eq p hϖ0 n ?_ (mul_mem (pow_mem (mem_integers_of_valued_lt_one p hϖ1) (N - n)) (hk i j))
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hnN, mul_inv_cancel_left₀ (pow_ne_zero N hϖ0)]

private theorem IsLevel.mul {ϖ : p.adicCompletion ℚ} {n : ℕ} {a b : GL (Fin 3) (p.adicCompletion ℚ)}
    (ha : IsLevel p ϖ n a) (hb : IsLevel p ϖ n b) (hbK : b ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsLevel p ϖ n (a * b) := by
  have hM : ((a * b : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1 =
      ((a : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) * (b : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) +
        ((b : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) := by
    rw [Units.val_mul, sub_mul, one_mul, sub_add_sub_cancel]
  intro i j
  rw [← Matrix.sub_apply, hM, Matrix.add_apply, mul_add]
  exact add_mem (entryDiv_mul_right p (IsLevel.entryDiv p ha) (entries_mem_of_mem_localMaximalCompact3 p hbK) i j)
    (IsLevel.entryDiv p hb i j)

private theorem IsLevel.inv {ϖ : p.adicCompletion ℚ} {n : ℕ} {a : GL (Fin 3) (p.adicCompletion ℚ)}
    (ha : IsLevel p ϖ n a) (haK : a ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) : IsLevel p ϖ n a⁻¹ := by
  intro i j
  exact level_of_mul_eq_one p n (Units.inv_mul a) (inv_entries_mem_of_mem_localMaximalCompact3 p haK) ha i j

private theorem IsLevel.conj {ϖ : p.adicCompletion ℚ} {n : ℕ} {k t : GL (Fin 3) (p.adicCompletion ℚ)}
    (hk : IsLevel p ϖ n k) (htK : t ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) : IsLevel p ϖ n (t⁻¹ * k * t) := by
  have hM : ((t⁻¹ * k * t : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1 =
      ((t⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) *
        ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) *
        (t : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, mul_one, sub_mul, Units.inv_mul]
  intro i j
  rw [← Matrix.sub_apply, hM]
  exact entryDiv_mul_right p (entryDiv_mul_left p (inv_entries_mem_of_mem_localMaximalCompact3 p htK) hk.entryDiv)
    (entries_mem_of_mem_localMaximalCompact3 p htK) i j

private theorem radicalP21_mem_localMaximalCompact3 {y : Fin 2 → p.adicCompletion ℚ}
    (hy : ∀ i, y i ∈ p.adicCompletionIntegers ℚ) : radicalP21 y ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hy' : ∀ i, Valued.v (y i) ≤ 1 :=
    fun i => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).1 (hy i)
  have hinv : (radicalP21 y)⁻¹ = upperUnipotent3 (-0) (-(y 1)) (0 * y 1 - y 0) := Units.ext rfl
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [radicalP21_coe]
    fin_cases i <;> fin_cases j <;> simp [hy']
  · rw [hinv, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hy']

private theorem isLevel_radicalP21 {ϖ : p.adicCompletion ℚ} {n : ℕ} {y : Fin 2 → p.adicCompletion ℚ}
    (hy : ∀ i, (ϖ ^ n)⁻¹ * y i ∈ p.adicCompletionIntegers ℚ) : IsLevel p ϖ n (radicalP21 y) := by
  intro i j
  rw [radicalP21_coe]
  fin_cases i <;> fin_cases j <;> simp [hy]

private theorem upperUnipotent3_mem_localMaximalCompact3 {x : p.adicCompletion ℚ}
    (hx : x ∈ p.adicCompletionIntegers ℚ) : upperUnipotent3 x 0 0 ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hx' : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).1 hx
  have hinv : (upperUnipotent3 x 0 0)⁻¹ = upperUnipotent3 (-x) (-0) (x * 0 - 0) := Units.ext rfl
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hx']
  · rw [hinv, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hx']

private theorem isLevel_upperUnipotent3 {ϖ : p.adicCompletion ℚ} {n : ℕ} {x : p.adicCompletion ℚ}
    (hx : (ϖ ^ n)⁻¹ * x ∈ p.adicCompletionIntegers ℚ) : IsLevel p ϖ n (upperUnipotent3 x 0 0) := by
  intro i j
  rw [upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [hx]

private theorem isLevel_iotaGL_lower {ϖ : p.adicCompletion ℚ} {n : ℕ} (c : GL (Fin 2) (p.adicCompletion ℚ))
    (hc : (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1, 0; (c : Matrix (Fin 2) (Fin 2) _) 1 0, (c : Matrix (Fin 2) (Fin 2) _) 1 1])
    (h10 : (ϖ ^ n)⁻¹ * (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ∈ p.adicCompletionIntegers ℚ)
    (h11 : (ϖ ^ n)⁻¹ * ((c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 - 1) ∈ p.adicCompletionIntegers ℚ) :
    IsLevel p ϖ n (iotaGL c) := by
  intro i j
  rw [coe_iotaGL, hc]
  fin_cases i <;> fin_cases j <;> simp [embedMat2, h10, h11]

private theorem isLevel_conj_iotaGL_lower {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {n : ℕ}
    (c : GL (Fin 2) (p.adicCompletion ℚ))
    (hc : (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1, 0; (c : Matrix (Fin 2) (Fin 2) _) 1 0, (c : Matrix (Fin 2) (Fin 2) _) 1 1])
    (h10 : (ϖ ^ (n + 2))⁻¹ * (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ∈ p.adicCompletionIntegers ℚ)
    (h11 : (ϖ ^ (n + 1))⁻¹ * ((c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 - 1) ∈ p.adicCompletionIntegers ℚ)
    {x : p.adicCompletion ℚ} (hx : ϖ * x ∈ p.adicCompletionIntegers ℚ) :
    upperUnipotent3 (-x) 0 0 * iotaGL c * upperUnipotent3 x 0 0 ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
      IsLevel p ϖ n (upperUnipotent3 (-x) 0 0 * iotaGL c * upperUnipotent3 x 0 0) := by
  have hϖ : ϖ ∈ p.adicCompletionIntegers ℚ := mem_integers_of_valued_lt_one p hϖ1
  rw [← iotaGL_unipotentGL2, ← iotaGL_unipotentGL2, ← map_mul, ← map_mul]
  set M : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) with hMdef
  set u : GL (Fin 2) (p.adicCompletion ℚ) := unipotentGL2 (-x) * c * unipotentGL2 x with hu
  have hval : (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1 - x * M 1 0, x - x * M 1 1 - x ^ 2 * M 1 0; M 1 0, M 1 1 + M 1 0 * x] := by
    rw [hu, Units.val_mul, Units.val_mul, ← hMdef, hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have e00 : (ϖ ^ n)⁻¹ * ((1 - x * M 1 0) - 1) ∈ p.adicCompletionIntegers ℚ :=
    level_of_eq p hϖ0 n (w := -((ϖ * x) * ((ϖ ^ (n + 2))⁻¹ * M 1 0) * ϖ)) (by field_simp; ring)
      (neg_mem (mul_mem (mul_mem hx h10) hϖ))
  have e01 : (ϖ ^ n)⁻¹ * ((x - x * M 1 1 - x ^ 2 * M 1 0) - 0) ∈ p.adicCompletionIntegers ℚ :=
    level_of_eq p hϖ0 n
      (w := -((ϖ * x) * ((ϖ ^ (n + 1))⁻¹ * (M 1 1 - 1))) - (ϖ * x) * (ϖ * x) * ((ϖ ^ (n + 2))⁻¹ * M 1 0))
      (by field_simp; ring) (sub_mem (neg_mem (mul_mem hx h11)) (mul_mem (mul_mem hx hx) h10))
  have e10 : (ϖ ^ n)⁻¹ * (M 1 0 - 0) ∈ p.adicCompletionIntegers ℚ :=
    level_of_eq p hϖ0 n (w := ϖ * ϖ * ((ϖ ^ (n + 2))⁻¹ * M 1 0)) (by field_simp; ring) (mul_mem (mul_mem hϖ hϖ) h10)
  have e11 : (ϖ ^ n)⁻¹ * ((M 1 1 + M 1 0 * x) - 1) ∈ p.adicCompletionIntegers ℚ :=
    level_of_eq p hϖ0 n (w := ϖ * ((ϖ ^ (n + 1))⁻¹ * (M 1 1 - 1)) + ϖ * ((ϖ ^ (n + 2))⁻¹ * M 1 0) * (ϖ * x))
      (by field_simp; ring) (add_mem (mul_mem hϖ h11) (mul_mem (mul_mem hϖ h10) hx))
  have hlev : ∀ i j, (ϖ ^ n)⁻¹ * ((u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) ∈ p.adicCompletionIntegers ℚ := by
    rw [hval]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using e00
    · simpa using e01
    · simpa using e10
    · simpa using e11
  refine ⟨iotaGL_mem_localMaximalCompact3_of_entries p u (fun i j => ?_) ?_, isLevel_iotaGL_of_entries p u hlev⟩
  · have h := hlev i j
    have hone : (1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have hsplit := add_mem hone (mul_mem (pow_mem hϖ n) h)
    rwa [mul_inv_cancel_left₀ (pow_ne_zero n hϖ0), add_sub_cancel] at hsplit
  · have hdet : (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det = M 1 1 := by
      rw [hval, Matrix.det_fin_two_of]
      ring
    rw [hdet]
    have hδ : M 1 1 - 1 = ϖ * (ϖ ^ n * ((ϖ ^ (n + 1))⁻¹ * (M 1 1 - 1))) := by
      rw [← mul_assoc, ← pow_succ', mul_inv_cancel_left₀ (pow_ne_zero (n + 1) hϖ0)]
    have hlt : Valued.v (M 1 1 - 1) < 1 := by
      rw [hδ, map_mul]
      calc Valued.v ϖ * Valued.v (ϖ ^ n * ((ϖ ^ (n + 1))⁻¹ * (M 1 1 - 1))) ≤ Valued.v ϖ * 1 := by
            refine mul_le_mul_right ?_ _
            have h := mul_mem (pow_mem hϖ n) h11
            rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
        _ = Valued.v ϖ := mul_one _
        _ < 1 := hϖ1
    have h1 := Valuation.map_one_add_of_lt Valued.v hlt
    rwa [add_sub_cancel] at h1

private theorem upperUnipotent3_neg_mul_radicalP21_mul_upperUnipotent3 {A : Type*} [CommRing A] (x : A)
    (y : Fin 2 → A) :
    upperUnipotent3 (-x) 0 0 * radicalP21 y * upperUnipotent3 x 0 0 = radicalP21 ![y 0 - x * y 1, y 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP21, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem isOpen_setOf_isLevel (ϖ : p.adicCompletion ℚ) (n : ℕ) :
    IsOpen {m : GL (Fin 3) (p.adicCompletion ℚ) | IsLevel p ϖ n m} := by
  have hrepr : {m : GL (Fin 3) (p.adicCompletion ℚ) | IsLevel p ϖ n m} = ⋂ i, ⋂ j,
      (fun m : GL (Fin 3) (p.adicCompletion ℚ) =>
        (ϖ ^ n)⁻¹ * ((m : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j)) ⁻¹'
        (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
    ext m
    simp [IsLevel]
  rw [hrepr]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  have hval : Continuous (Units.val : GL (Fin 3) (p.adicCompletion ℚ) → Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) :=
    Units.continuous_val
  exact (Valued.isClopen_valuationSubring (p.adicCompletion ℚ)).isOpen.preimage
    (continuous_const.mul ((hval.matrix_elem i j).sub continuous_const))

private theorem mem_integers_of_level {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {n : ℕ}
    {x : p.adicCompletion ℚ} (hx : (ϖ ^ n)⁻¹ * x ∈ p.adicCompletionIntegers ℚ) : x ∈ p.adicCompletionIntegers ℚ := by
  have hϖn : ϖ ^ n ∈ p.adicCompletionIntegers ℚ :=
    pow_mem ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).2 hϖ1.le) n
  have h := mul_mem hϖn hx
  rwa [mul_inv_cancel_left₀ (pow_ne_zero n hϖ0)] at h

private theorem level_mono {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {n N : ℕ} (hnN : n ≤ N)
    {x : p.adicCompletion ℚ} (hx : (ϖ ^ N)⁻¹ * x ∈ p.adicCompletionIntegers ℚ) :
    (ϖ ^ n)⁻¹ * x ∈ p.adicCompletionIntegers ℚ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnN
  have hϖm : ϖ ^ m ∈ p.adicCompletionIntegers ℚ :=
    pow_mem ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).2 hϖ1.le) m
  have h := mul_mem hϖm hx
  have hid : ϖ ^ m * ((ϖ ^ (n + m))⁻¹ * x) = (ϖ ^ n)⁻¹ * x := by
    rw [pow_add]
    field_simp
  rwa [hid] at h

private theorem valued_sub_one_lt_of_level {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {n : ℕ}
    {d : p.adicCompletion ℚ} (hd : (ϖ ^ (n + 1))⁻¹ * (d - 1) ∈ p.adicCompletionIntegers ℚ) : Valued.v (d - 1) < 1 := by
  have h1 : Valued.v ((ϖ ^ (n + 1))⁻¹ * (d - 1)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).1 hd
  have hpow : Valued.v (ϖ ^ (n + 1)) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' hϖ1 n.succ_ne_zero
  calc Valued.v (d - 1) = Valued.v (ϖ ^ (n + 1) * ((ϖ ^ (n + 1))⁻¹ * (d - 1))) := by
        rw [mul_inv_cancel_left₀ (pow_ne_zero _ hϖ0)]
    _ = Valued.v (ϖ ^ (n + 1)) * Valued.v ((ϖ ^ (n + 1))⁻¹ * (d - 1)) := map_mul _ _ _
    _ ≤ Valued.v (ϖ ^ (n + 1)) := mul_le_of_le_one_right' h1
    _ < 1 := hpow

private theorem mul_mem_integers_of_region_of_level {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) {c : ℕ}
    {t x : p.adicCompletion ℚ} (ht : ϖ ^ c * t ∈ p.adicCompletionIntegers ℚ)
    (hx : (ϖ ^ c)⁻¹ * x ∈ p.adicCompletionIntegers ℚ) : t * x ∈ p.adicCompletionIntegers ℚ := by
  have hid : t * x = (ϖ ^ c * t) * ((ϖ ^ c)⁻¹ * x) := by
    field_simp
  rw [hid]
  exact mul_mem ht hx

private theorem upperUnipotent3_inv {A : Type*} [CommRing A] (x y z : A) :
    (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) :=
  Units.ext rfl

private theorem level_mul_of_region {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) {n : ℕ} {t x : p.adicCompletion ℚ}
    (ht : ϖ * t ∈ p.adicCompletionIntegers ℚ) (hx : (ϖ ^ (n + 1))⁻¹ * x ∈ p.adicCompletionIntegers ℚ) :
    (ϖ ^ n)⁻¹ * (t * x) ∈ p.adicCompletionIntegers ℚ :=
  level_of_eq p hϖ0 n (w := ϖ * t * ((ϖ ^ (n + 1))⁻¹ * x)) (by field_simp; ring) (mul_mem ht hx)

end LevelKit

section Words

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

private theorem continuous_mul_mul (a b : G) : Continuous fun k : G => a * k * b :=
  (continuous_const.mul continuous_id).mul continuous_const

private theorem continuous_commWord (a b : G) : Continuous fun k : G => k⁻¹ * a * k * b :=
  ((continuous_inv.mul continuous_const).mul continuous_id).mul continuous_const

end Words

section GroupWords

variable {G : Type*} [Group G]

private theorem word_split (B c k : G) : B⁻¹ * (c * k) * B = B⁻¹ * c * B * (B⁻¹ * k * B) := by group

private theorem word_conj_triple (κ a b c : G) :
    κ⁻¹ * (a * b * c) * κ = κ⁻¹ * a * κ * (κ⁻¹ * b * κ) * (κ⁻¹ * c * κ) := by group

private theorem word_conj₀ (m κ u : G) : (m * κ)⁻¹ * u * (m * κ) = κ⁻¹ * (m⁻¹ * u * m) * κ := by group

private theorem word_conj₁ (κ B k r : G) :
    (κ⁻¹ * B * κ)⁻¹ * ((k * κ)⁻¹ * r * (k * κ)) * (κ⁻¹ * B * κ) =
      κ⁻¹ * ((B⁻¹ * k * B)⁻¹ * (B⁻¹ * r * B) * (B⁻¹ * k * B)) * κ := by
  group

private theorem word_conj₂ (κ B A k r : G) :
    (κ⁻¹ * B * κ)⁻¹ * ((κ⁻¹ * A * κ)⁻¹ * ((k * κ)⁻¹ * r * (k * κ)) * (κ⁻¹ * A * κ)) * (κ⁻¹ * B * κ) =
      κ⁻¹ * ((B⁻¹ * (A⁻¹ * k * A) * B)⁻¹ * (B⁻¹ * (A⁻¹ * r * A) * B) * (B⁻¹ * (A⁻¹ * k * A) * B)) * κ := by
  group

private theorem word_conj₃ (κ m B : G) :
    κ⁻¹ * (m⁻¹ * B⁻¹ * m * B) * κ = κ⁻¹ * m⁻¹ * κ * (κ⁻¹ * (B⁻¹ * m * B) * κ) := by
  group

private theorem word_comm₁ (κ B k A : G) :
    (κ⁻¹ * B * κ)⁻¹ * (κ⁻¹ * (k⁻¹ * A⁻¹ * k * A) * κ) * (κ⁻¹ * B * κ) = κ⁻¹ * (B⁻¹ * (k⁻¹ * A⁻¹ * k * A) * B) * κ := by
  group

private theorem word_comm₂ (κ B A k T : G) :
    (κ⁻¹ * B * κ)⁻¹ * ((κ⁻¹ * A * κ)⁻¹ * (κ⁻¹ * (k⁻¹ * T⁻¹ * k * T) * κ) * (κ⁻¹ * A * κ)) * (κ⁻¹ * B * κ) =
      κ⁻¹ * (B⁻¹ * (A⁻¹ * (k⁻¹ * T⁻¹ * k * T) * A) * B) * κ := by
  group

end GroupWords

section LocalTopology

variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem isClopen_localMaximalCompact3 :
    IsClopen (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))) := by
  have hint : IsClopen (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) :=
    Valued.isClopen_valuationSubring (p.adicCompletion ℚ)
  have hval : Continuous fun k : GL (Fin 3) (p.adicCompletion ℚ) =>
      (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) := Units.continuous_val
  have hinv : Continuous fun k : GL (Fin 3) (p.adicCompletion ℚ) =>
      ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) :=
    Units.continuous_coe_inv
  have hrepr : (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))) =
      (⋂ i : Fin 3, ⋂ j : Fin 3, (fun k : GL (Fin 3) (p.adicCompletion ℚ) =>
          (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ⁻¹'
            (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) ∩
        (⋂ i : Fin 3, ⋂ j : Fin 3, (fun k : GL (Fin 3) (p.adicCompletion ℚ) =>
          ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ⁻¹'
            (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) := by
    ext k
    simp [mem_localMaximalCompact3_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [hrepr]
  exact (isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      hint.preimage (hval.matrix_elem i j)).inter
    (isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => hint.preimage (hinv.matrix_elem i j))

private theorem isOpen_localMaximalCompact3 :
    IsOpen (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))) :=
  (isClopen_localMaximalCompact3 p).isOpen

private theorem continuous_componentAt3 : Continuous (componentAt3 (𝓞 ℚ) ℚ p) := by
  have hφ : Continuous ((AdelicLevel.finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) :=
    (AdelicLevel.continuous_finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ)
  have hmat : Continuous ⇑((RingHom.mapMatrix (m := Fin 3) ((AdelicLevel.finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp
      (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))).toMonoidHom) := by
    show Continuous fun A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) =>
      A.map ((AdelicLevel.finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
    exact continuous_id.matrix_map hφ
  exact Units.continuous_map hmat

end LocalTopology

section CharSum

variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_natGenerator :
    Valued.v ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  have hq : ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : 𝓞 ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Rat.HeightOneSpectrum.prime_natGenerator p).ne_zero
  have hspan : p.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator p : ℕ) : 𝓞 ℚ)} := by
    ext x
    rw [Ideal.mem_span_singleton, ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast,
      ← Ideal.mem_span_singleton, Rat.HeightOneSpectrum.span_natGenerator, ← Ideal.comap_symm, Ideal.mem_comap,
      RingEquiv.symm_apply_apply]
  have h1 := p.intValuation_singleton hq hspan
  have h2 := p.valuedAdicCompletion_eq_valuation (K := ℚ) ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : 𝓞 ℚ)
  rw [HeightOneSpectrum.valuation_of_algebraMap, h1] at h2
  simpa using h2

private theorem exp_one_le_of_one_lt {x : WithZero (Multiplicative ℤ)} (hx : 1 < x) : WithZero.exp (1 : ℤ) ≤ x := by
  have hx0 : x ≠ 0 := (zero_le_one.trans_lt hx).ne'
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = WithZero.exp k := ⟨WithZero.log x, (WithZero.exp_log hx0).symm⟩
  rw [WithZero.exp_eq_coe_ofAdd] at hx
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt] at hx
  exact WithZero.exp_le_exp.2 (by omega)

private theorem valued_sharp :
    Valued.v (algebraMap ℚ (p.adicCompletion ℚ) ((Rat.HeightOneSpectrum.natGenerator p : ℚ))⁻¹) =
      WithZero.exp (1 : ℤ) := by
  rw [map_inv₀, map_natCast, map_inv₀, valued_natGenerator, ← WithZero.exp_neg, neg_neg]

private theorem exists_psiV_ne_one {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) (c₀ : ℕ)
    (r : p.adicCompletion ℚ) (hr : ϖ ^ c₀ * r ∉ p.adicCompletionIntegers ℚ) :
    ∃ y : p.adicCompletion ℚ, (ϖ ^ c₀)⁻¹ * y ∈ p.adicCompletionIntegers ℚ ∧ psiV p (r * y) ≠ 1 := by
  have _ := hϖ1
  set r' : p.adicCompletion ℚ := ϖ ^ c₀ * r with hr'
  have hr'v : 1 < Valued.v r' := by
    by_contra h
    exact hr ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).2 (not_lt.1 h))
  have hr'0 : r' ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hr'v
    exact (not_lt.2 zero_le') hr'v
  have hr0 : r ≠ 0 := by
    rintro h0
    exact hr'0 (by rw [hr', h0, mul_zero])
  set e : p.adicCompletion ℚ := algebraMap ℚ (p.adicCompletion ℚ) ((Rat.HeightOneSpectrum.natGenerator p : ℚ))⁻¹
    with he
  have hz : e / r' ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, he, valued_sharp]
    exact (div_le_one₀ (zero_le_one.trans_lt hr'v)).2 (exp_one_le_of_one_lt hr'v)
  refine ⟨ϖ ^ c₀ * (e / r'), ?_, ?_⟩
  · rw [inv_mul_cancel_left₀ (pow_ne_zero _ hϖ0)]
    exact hz
  · have hre : r * (ϖ ^ c₀ * (e / r')) = e := by
      rw [hr']
      field_simp
    rw [hre, he]
    exact psiV_algebraMap_inv_ne_one p

private theorem exists_charSum_eq_indicator {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (c₀ n : ℕ) (a : p.adicCompletion ℚ) (ha : ϖ ^ c₀ * a ∈ p.adicCompletionIntegers ℚ) :
    ∃ (J : Type) (_ : Fintype J) (y : J → p.adicCompletion ℚ) (c : J → ℂ),
      (∀ j, ϖ ^ n * y j ∈ p.adicCompletionIntegers ℚ) ∧
      ∀ t : p.adicCompletion ℚ, ϖ ^ c₀ * t ∈ p.adicCompletionIntegers ℚ →
        ((ϖ ^ n)⁻¹ * (t - a) ∈ p.adicCompletionIntegers ℚ → ∑ j, c j * psiV p (t * y j) = 1) ∧
        ((ϖ ^ n)⁻¹ * (t - a) ∉ p.adicCompletionIntegers ℚ → ∑ j, c j * psiV p (t * y j) = 0) := by
  haveI : AddCommMagma (p.adicCompletionIntegers ℚ) := inferInstance
  classical
  set N : ℕ := n + c₀ with hN
  let I : AddSubgroup (p.adicCompletionIntegers ℚ) :=
    { carrier := {z | (ϖ ^ N)⁻¹ * (z : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ}
      zero_mem' := by simp
      add_mem' := fun {z w} (hz : (ϖ ^ N)⁻¹ * (z : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ)
        (hw : (ϖ ^ N)⁻¹ * (w : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ) => by
          simpa [mul_add] using add_mem hz hw
      neg_mem' := fun {z} (hz : (ϖ ^ N)⁻¹ * (z : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ) => by
          simpa [mul_neg] using neg_mem hz }
  have hIopen : IsOpen (I : Set (p.adicCompletionIntegers ℚ)) := by
    have hrepr : (I : Set (p.adicCompletionIntegers ℚ)) = Subtype.val ⁻¹'
        ((fun x : p.adicCompletion ℚ => (ϖ ^ N)⁻¹ * x) ⁻¹'
          (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) := rfl
    rw [hrepr]
    exact (((Valued.isClopen_valuationSubring (p.adicCompletion ℚ)).preimage
      (continuous_const.mul continuous_id)).preimage continuous_subtype_val).isOpen
  haveI : Finite (p.adicCompletionIntegers ℚ ⧸ I) := AddSubgroup.quotient_finite_of_isOpen I hIopen
  letI : Fintype (p.adicCompletionIntegers ℚ ⧸ I) := Fintype.ofFinite _
  have hker : ∀ (s : p.adicCompletion ℚ), ϖ ^ c₀ * s ∈ p.adicCompletionIntegers ℚ → ∀ z ∈ I,
      psiV p ((ϖ ^ n)⁻¹ * s * (z : p.adicCompletion ℚ)) = 1 := by
    intro s hs z hz
    have hz' : (ϖ ^ N)⁻¹ * (z : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := hz
    have hsplit : (ϖ ^ n)⁻¹ * s * (z : p.adicCompletion ℚ) =
        (ϖ ^ c₀ * s) * ((ϖ ^ N)⁻¹ * (z : p.adicCompletion ℚ)) := by
      rw [hN, pow_add]
      field_simp
    rw [hsplit]
    exact psiV_eq_one_of_mem_integers p (mul_mem hs hz')
  refine ⟨p.adicCompletionIntegers ℚ ⧸ I, inferInstance,
    fun j => (ϖ ^ n)⁻¹ * ((Quotient.out j : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ),
    fun j => (Fintype.card (p.adicCompletionIntegers ℚ ⧸ I) : ℂ)⁻¹ *
      psiV p (-a * ((ϖ ^ n)⁻¹ * ((Quotient.out j : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ))),
    fun j => ?_, fun t ht => ?_⟩
  · rw [mul_inv_cancel_left₀ (pow_ne_zero _ hϖ0)]
    exact (Quotient.out j).2
  · set s : p.adicCompletion ℚ := t - a with hs
    have hs_reg : ϖ ^ c₀ * s ∈ p.adicCompletionIntegers ℚ := by
      rw [hs, mul_sub]
      exact sub_mem ht ha
    have hconst : ∀ z w : p.adicCompletionIntegers ℚ, (z : p.adicCompletionIntegers ℚ ⧸ I) = w →
        psiV p ((ϖ ^ n)⁻¹ * s * (z : p.adicCompletion ℚ)) = psiV p ((ϖ ^ n)⁻¹ * s * (w : p.adicCompletion ℚ)) := by
      intro z w hzw
      have hmem : -z + w ∈ I := QuotientAddGroup.eq.1 hzw
      have hw : (ϖ ^ n)⁻¹ * s * (w : p.adicCompletion ℚ) = (ϖ ^ n)⁻¹ * s * (z : p.adicCompletion ℚ) +
          (ϖ ^ n)⁻¹ * s * ((-z + w : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ) := by
        push_cast
        ring
      rw [hw, AddChar.map_add_eq_mul, hker s hs_reg _ hmem, mul_one]
    let χ : AddChar (p.adicCompletionIntegers ℚ ⧸ I) ℂ :=
      { toFun := fun j => psiV p ((ϖ ^ n)⁻¹ * s * ((Quotient.out j : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ))
        map_zero_eq_one' := by
          have h := hconst (Quotient.out (0 : p.adicCompletionIntegers ℚ ⧸ I)) 0
            ((QuotientAddGroup.out_eq' _).trans rfl)
          rw [h]
          simp
        map_add_eq_mul' := by
          intro j j'
          have h := hconst (Quotient.out (j + j')) (Quotient.out j + Quotient.out j')
            ((QuotientAddGroup.out_eq' _).trans (by
              rw [show ((Quotient.out j + Quotient.out j' : p.adicCompletionIntegers ℚ) :
                  p.adicCompletionIntegers ℚ ⧸ I) =
                    ((Quotient.out j : p.adicCompletionIntegers ℚ) : p.adicCompletionIntegers ℚ ⧸ I) +
                    ((Quotient.out j' : p.adicCompletionIntegers ℚ) : p.adicCompletionIntegers ℚ ⧸ I) from rfl,
                QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']))
          rw [h]
          push_cast
          rw [mul_add, AddChar.map_add_eq_mul] }
    have hχ : ∀ j, χ j =
        psiV p ((ϖ ^ n)⁻¹ * s * ((Quotient.out j : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ)) :=
      fun _ => rfl
    have hsum : ∑ j : p.adicCompletionIntegers ℚ ⧸ I, (Fintype.card (p.adicCompletionIntegers ℚ ⧸ I) : ℂ)⁻¹ *
        psiV p (-a * ((ϖ ^ n)⁻¹ * ((Quotient.out j : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ))) *
        psiV p (t * ((ϖ ^ n)⁻¹ * ((Quotient.out j : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ))) =
        (Fintype.card (p.adicCompletionIntegers ℚ ⧸ I) : ℂ)⁻¹ * ∑ j, χ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc, ← AddChar.map_add_eq_mul, hχ]
      congr 2
      rw [hs]
      ring
    rw [hsum, AddChar.sum_eq_ite]
    have hcard : (Fintype.card (p.adicCompletionIntegers ℚ ⧸ I) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    refine ⟨fun hint => ?_, fun hint => ?_⟩
    · have hχ0 : χ = 0 := by
        ext j
        rw [hχ, AddChar.zero_apply]
        exact psiV_eq_one_of_mem_integers p (mul_mem hint (Quotient.out j).2)
      rw [if_pos hχ0]
      exact inv_mul_cancel₀ hcard
    · have hχne : χ ≠ 0 := by
        intro h0
        obtain ⟨z, hz, hne⟩ := exists_psiV_ne_one p hϖ0 hϖ1 0 ((ϖ ^ n)⁻¹ * s) (by simpa using hint)
        have hzmem : z ∈ p.adicCompletionIntegers ℚ := by simpa using hz
        have h1 : χ ((⟨z, hzmem⟩ : p.adicCompletionIntegers ℚ) : p.adicCompletionIntegers ℚ ⧸ I) = 1 := by
          rw [h0, AddChar.zero_apply]
        rw [hχ] at h1
        have hc := hconst (Quotient.out (((⟨z, hzmem⟩ : p.adicCompletionIntegers ℚ) :
          p.adicCompletionIntegers ℚ ⧸ I))) ⟨z, hzmem⟩ (by simp only [QuotientAddGroup.out_eq'])
        exact hne (hc.symm.trans h1)
      rw [if_neg hχne, mul_zero]

end CharSum

section TestFunction

open NumberField.TateGlobal NumberField.AdelicFourier NumberField.AdelicHaar

private def integralBox (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (A : Fin 3 → (p : HeightOneSpectrum (𝓞 ℚ)) → Set (p.adicCompletion ℚ)) :
    Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | ∀ i : Fin 3, ∀ p ∈ S, ((x i).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) p ∈ A i p}

private def localBox (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (A : Fin 3 → (p : HeightOneSpectrum (𝓞 ℚ)) → Set (p.adicCompletion ℚ)) (i : Fin 3) :
    Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  {y | ∀ p ∈ S, y p ∈ A i p}

private theorem isClopen_localBox (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (A : Fin 3 → (p : HeightOneSpectrum (𝓞 ℚ)) → Set (p.adicCompletion ℚ)) (hA : ∀ i p, IsClopen (A i p))
    (i : Fin 3) : IsClopen (localBox S A i) := by
  have : localBox S A i = ⋂ p ∈ S, (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y p) ⁻¹' A i p := by
    ext y; simp [localBox]
  rw [this]
  exact isClopen_biInter_finset fun p _ =>
    (hA i p).preimage (RestrictedProduct.continuous_eval p : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y p)

private theorem mem_integralBox_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (A : Fin 3 → (p : HeightOneSpectrum (𝓞 ℚ)) → Set (p.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    x ∈ integralBox S A ↔ ∀ i, (x i).2 ∈ localBox S A i := Iff.rfl

private theorem isLocallyConstant_indicator_one {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsClopen U) :
    IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun y => ?_
  by_cases hy : y ∈ U
  · exact ⟨U, hU.isOpen, hy, fun z hz => by simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hy]⟩
  · exact ⟨Uᶜ, hU.isClosed.isOpen_compl, hy, fun z hz =>
      by simp only [Set.indicator_of_notMem (Set.notMem_of_mem_compl hz), Set.indicator_of_notMem hy]⟩

private theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ) := by
  have hfun : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace ℚ) = fun x => InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x := rfl
  rw [hfun]
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem continuous_of_mem_pureTensorSet {φ : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ pureTensorSet ℚ) :
    Continuous φ := by
  classical
  obtain ⟨g, h, hlc, -, rfl⟩ := hφ
  exact (g.continuous.comp (continuous_ringEquiv_mixedSpace.comp continuous_fst)).mul
    (hlc.continuous.comp continuous_snd)

private theorem prod_indicator_localBox (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (A : Fin 3 → (p : HeightOneSpectrum (𝓞 ℚ)) → Set (p.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    (∏ i : Fin 3, (localBox S A i).indicator (fun _ => (1 : ℂ)) (x i).2) =
      (integralBox S A).indicator (fun _ => (1 : ℂ)) x := by
  by_cases hx : x ∈ integralBox S A
  · rw [Set.indicator_of_mem hx]
    exact Finset.prod_eq_one fun i _ => Set.indicator_of_mem ((mem_integralBox_iff S A x).1 hx i) _
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨i, hi⟩ : ∃ i, (x i).2 ∉ localBox S A i := by
      by_contra hcon
      exact hx ((mem_integralBox_iff S A x).2 fun i => not_not.1 fun hi => hcon ⟨i, hi⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

private theorem exists_testFunction_box (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (A : Fin 3 → (p : HeightOneSpectrum (𝓞 ℚ)) → Set (p.adicCompletion ℚ))
    (hclopen : ∀ i p, IsClopen (A i p)) (hint : ∀ i p, A i p ⊆ (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)))
    (hne : ∀ i p, (A i p).Nonempty)
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ))
    (hpt : ∀ i, Φc i ∈ pureTensorSet ℚ)
    (hstd : ∀ i, ∃ g h, IsFactorizableStandardOutside (Φc i) ∅ g h)
    (hΦ : Φ = fun x => ∏ i, Φc i (x i))
    (hreal : ∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0)
    (hmass : letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := adeleBorel (𝓞 ℚ) ℚ
      0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => adelicAddHaar (𝓞 ℚ) ℚ)) :
    ∃ Φ' : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
      ((∃ Φc' : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc' i ∈ pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, IsFactorizableStandardOutside (Φc' i) S g h) ∧
          Φ' = fun x => ∏ i, Φc' i (x i)) ∧
        (∀ x, 0 ≤ (Φ' x).re ∧ (Φ' x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ' x).re ∂(Measure.pi fun _ : Fin 3 => adelicAddHaar (𝓞 ℚ) ℚ))) ∧
      (∀ x, Φ' x = Φ x * (integralBox S A).indicator (fun _ => (1 : ℂ)) x) ∧
      (∀ x, 0 ≤ (Φ' x).re ∧ (Φ' x).re ≤ (Φ x).re) := by
  classical

  set Φc' : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ) :=
    fun i a => Φc i a * (localBox S A i).indicator (fun _ => (1 : ℂ)) a.2 with hΦc'
  set Φ' : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ := fun x => ∏ i, Φc' i (x i) with hΦ'def

  have hbox : ∀ x, Φ' x = Φ x * (integralBox S A).indicator (fun _ => (1 : ℂ)) x := by
    intro x
    simp only [hΦ'def, hΦc', hΦ, Finset.prod_mul_distrib]
    rw [prod_indicator_localBox]

  have hcases : ∀ x, (x ∈ integralBox S A ∧ Φ' x = Φ x) ∨ (x ∉ integralBox S A ∧ Φ' x = 0) := by
    intro x
    by_cases hx : x ∈ integralBox S A
    · exact Or.inl ⟨hx, by rw [hbox, Set.indicator_of_mem hx, mul_one]⟩
    · exact Or.inr ⟨hx, by rw [hbox, Set.indicator_of_notMem hx, mul_zero]⟩
  have hreal' : ∀ x, 0 ≤ (Φ' x).re ∧ (Φ' x).im = 0 := by
    intro x
    rcases hcases x with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h]; exact hreal x
    · rw [h]; simp
  have hdom : ∀ x, 0 ≤ (Φ' x).re ∧ (Φ' x).re ≤ (Φ x).re := by
    intro x
    refine ⟨(hreal' x).1, ?_⟩
    rcases hcases x with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h]
    · rw [h]; simpa using (hreal x).1

  have hre : (fun x => (Φ' x).re) = (integralBox S A).indicator fun x => (Φ x).re := by
    funext x
    rcases hcases x with ⟨hx, h⟩ | ⟨hx, h⟩
    · rw [h, Set.indicator_of_mem hx]
    · rw [h, Set.indicator_of_notMem hx]; simp
  refine ⟨Φ', ⟨⟨Φc', ?_, ?_, rfl⟩, hreal', ?_⟩, hbox, hdom⟩
  ·
    intro i
    obtain ⟨g, h, hlc, hcs, hfeq⟩ := hpt i
    refine ⟨g, fun y => h y * (localBox S A i).indicator (fun _ => (1 : ℂ)) y,
      hlc.mul (isLocallyConstant_indicator_one (isClopen_localBox S A hclopen i)), ?_, ?_⟩
    · exact hcs.mul_right
    · funext a
      simp only [hΦc', hfeq, mul_assoc]
  ·
    intro i
    obtain ⟨g, h, hrep⟩ := hstd i
    refine ⟨g, fun p => (A i p).indicator fun _ => (1 : ℂ), fun a => ?_⟩
    have hrep_a := hrep a
    simp only [Finset.prod_empty, mul_one] at hrep_a
    simp only [hΦc', hrep_a]
    by_cases hloc : a.2 ∈ localBox S A i
    ·
      have hprod : (∏ p ∈ S, (A i p).indicator (fun _ => (1 : ℂ)) ((a.2 : FiniteAdeleRing (𝓞 ℚ) ℚ) p)) = 1 :=
        Finset.prod_eq_one fun p hp => Set.indicator_of_mem (hloc p hp) _
      rw [Set.indicator_of_mem hloc]
      by_cases hS : a ∈ integralOutside (F := ℚ) S
      · have h0 : a ∈ integralOutside (F := ℚ) ∅ := by
          intro v _
          by_cases hv : v ∈ S
          · exact hint i v (hloc v hv)
          · exact hS v hv
        simp only [Set.indicator_of_mem h0, Set.indicator_of_mem hS, hprod, mul_one]
      · have h0 : a ∉ integralOutside (F := ℚ) ∅ := fun h0 => hS fun v _ => h0 v (Finset.notMem_empty v)
        simp only [Set.indicator_of_notMem h0, Set.indicator_of_notMem hS, zero_mul]
    ·
      obtain ⟨p, hp, hap⟩ : ∃ p ∈ S, (a.2 : FiniteAdeleRing (𝓞 ℚ) ℚ) p ∉ A i p := by
        by_contra hcon
        exact hloc fun p hp => not_not.1 fun hap => hcon ⟨p, hp, hap⟩
      have hprod : (∏ q ∈ S, (A i q).indicator (fun _ => (1 : ℂ)) ((a.2 : FiniteAdeleRing (𝓞 ℚ) ℚ) q)) = 0 :=
        Finset.prod_eq_zero hp (Set.indicator_of_notMem hap _)
      rw [Set.indicator_of_notMem hloc, mul_zero]
      by_cases hS : a ∈ integralOutside (F := ℚ) S
      · simp only [Set.indicator_of_mem hS, hprod, mul_zero]
      · simp only [Set.indicator_of_notMem hS]
  ·
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := adeleBorel (𝓞 ℚ) ℚ
    haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := borelSpace_adeleBorel (𝓞 ℚ) ℚ
    haveI : (adelicAddHaar (𝓞 ℚ) ℚ).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

    have hT : ∀ i, IsOpen {a : AdeleRing (𝓞 ℚ) ℚ | a.2 ∈ localBox S A i} :=
      fun i => (isClopen_localBox S A hclopen i).isOpen.preimage continuous_snd
    have hbox_eq : integralBox S A = Set.pi Set.univ fun i => {a : AdeleRing (𝓞 ℚ) ℚ | a.2 ∈ localBox S A i} := by
      ext x; simp [mem_integralBox_iff]
    have hbox_open : IsOpen (integralBox S A) := by
      rw [hbox_eq]; exact isOpen_set_pi Set.finite_univ fun i _ => hT i
    have hbox_meas : MeasurableSet (integralBox S A) := by
      rw [hbox_eq]; exact MeasurableSet.univ_pi fun i => (hT i).measurableSet

    have hΦint : Integrable (fun x => (Φ x).re) (Measure.pi fun _ : Fin 3 => adelicAddHaar (𝓞 ℚ) ℚ) := by
      by_contra hcon
      rw [integral_undef hcon] at hmass
      exact lt_irrefl _ hmass
    have hΦcont : Continuous fun x => (Φ x).re := by
      refine Complex.continuous_re.comp ?_
      rw [hΦ]
      exact continuous_finsetProd _ fun i _ => (continuous_of_mem_pureTensorSet (hpt i)).comp (continuous_apply i)

    obtain ⟨x₁, hx₁⟩ : ∃ x₁, (Φ x₁).re ≠ 0 := by
      by_contra hcon
      have hzero : ∀ x, (Φ x).re = 0 := fun x => not_not.1 fun h => hcon ⟨x, h⟩
      simp only [hzero, integral_zero, lt_self_iff_false] at hmass
    have hx₁' : Φ x₁ ≠ 0 := fun h => hx₁ (by rw [h, Complex.zero_re])
    have hfactors : ∀ i, Φc i (x₁ i) ≠ 0 := by
      intro i hi
      apply hx₁'
      rw [hΦ]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi

    let b : Fin 3 → (p : HeightOneSpectrum (𝓞 ℚ)) → p.adicCompletionIntegers ℚ := fun i p =>
      if hp : p ∈ S then ⟨(hne i p).some, hint i p (hne i p).some_mem⟩ else 0
    let y : Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ := fun i =>
      RestrictedProduct.structureMap (fun q : HeightOneSpectrum (𝓞 ℚ) => q.adicCompletion ℚ)
        (fun q => (q.adicCompletionIntegers ℚ : Set (q.adicCompletion ℚ))) Filter.cofinite (b i)
    have hy_apply : ∀ i p, (y i) p = ((b i p : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ) :=
      fun i p => RestrictedProduct.structureMap_apply _ _ p
    have hy_int : ∀ i p, (y i) p ∈ p.adicCompletionIntegers ℚ := fun i p => by
      rw [hy_apply]; exact (b i p).2
    have hy_box : ∀ i, y i ∈ localBox S A i := by
      intro i p hp
      rw [hy_apply]
      simp only [b, dif_pos hp]
      exact (hne i p).some_mem
    set x₀ : Fin 3 → AdeleRing (𝓞 ℚ) ℚ := fun i => ((x₁ i).1, y i) with hx₀
    have hx₀_box : x₀ ∈ integralBox S A := (mem_integralBox_iff S A x₀).2 fun i => hy_box i

    have hsame : ∀ i, Φc i (x₀ i) = Φc i (x₁ i) := by
      intro i
      obtain ⟨g, h, hrep⟩ := hstd i
      have h₀ : x₀ i ∈ integralOutside (F := ℚ) ∅ := fun v _ => hy_int i v
      have h₁ : x₁ i ∈ integralOutside (F := ℚ) ∅ := by
        by_contra hcon
        exact hfactors i (by rw [hrep, Set.indicator_of_notMem hcon])
      rw [hrep, hrep, Set.indicator_of_mem h₀, Set.indicator_of_mem h₁]
      simp only [hx₀, Finset.prod_empty]
    have hΦx₀ : (Φ x₀).re = (Φ x₁).re := by
      rw [hΦ]
      simp only [hsame]

    have hsupport_open : IsOpen (integralBox S A ∩ {x | (Φ x).re ≠ 0}) :=
      hbox_open.inter (isOpen_ne_fun hΦcont continuous_const)
    have hsub : integralBox S A ∩ {x | (Φ x).re ≠ 0} ⊆ Function.support fun x => (Φ' x).re := by
      intro x hx
      rcases hcases x with ⟨-, h⟩ | ⟨hx', -⟩
      · simpa [Function.mem_support, h] using hx.2
      · exact absurd hx.1 hx'
    have hpos : 0 < (Measure.pi fun _ : Fin 3 => adelicAddHaar (𝓞 ℚ) ℚ) (Function.support fun x => (Φ' x).re) := by
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      exact hsupport_open.measure_pos _ ⟨x₀, hx₀_box, by simpa [hΦx₀] using hx₁⟩
    have hint' : Integrable (fun x => (Φ' x).re) (Measure.pi fun _ : Fin 3 => adelicAddHaar (𝓞 ℚ) ℚ) := by
      rw [hre]; exact hΦint.indicator hbox_meas
    exact (integral_pos_iff_support_of_nonneg (fun x => (hreal' x).1) hint').2 hpos

end TestFunction

section Localisation

variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_le_of_inv_mul_mem {ϖ x : p.adicCompletion ℚ} (hϖ : ϖ ≠ 0)
    (hx : ϖ⁻¹ * x ∈ p.adicCompletionIntegers ℚ) : Valued.v x ≤ Valued.v ϖ := by
  have hx' : Valued.v (ϖ⁻¹ * x) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).1 hx
  calc Valued.v x = Valued.v (ϖ * (ϖ⁻¹ * x)) := by rw [mul_inv_cancel_left₀ hϖ]
    _ = Valued.v ϖ * Valued.v (ϖ⁻¹ * x) := map_mul _ _ _
    _ ≤ Valued.v ϖ := mul_le_of_le_one_right' hx'

private theorem valued_lt_one_of_inv_mul_mem {ϖ x : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hx : ϖ⁻¹ * x ∈ p.adicCompletionIntegers ℚ) : Valued.v x < 1 :=
  (valued_le_of_inv_mul_mem p hϖ0 hx).trans_lt hϖ1

private theorem valued_eq_one_of_sub_one_lt {d : p.adicCompletion ℚ} (hd : Valued.v (d - 1) < 1) :
    Valued.v d = 1 := by
  have h1 : Valued.v (d - 1) < Valued.v (1 : p.adicCompletion ℚ) := by rw [map_one]; exact hd
  have h : Valued.v ((d - 1) + 1) = Valued.v (1 : p.adicCompletion ℚ) := Valuation.map_add_eq_of_lt_right _ h1
  rwa [sub_add_cancel, map_one] at h

private theorem ne_zero_of_sub_one_lt {d : p.adicCompletion ℚ} (hd : Valued.v (d - 1) < 1) : d ≠ 0 := by
  intro h0
  have h1 := valued_eq_one_of_sub_one_lt p hd
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

private def bottomRowUnit (a b d : p.adicCompletion ℚ) (hd : d ≠ 0) : GL (Fin 3) (p.adicCompletion ℚ) where
  val := !![1, 0, 0; 0, 1, 0; a, b, d]
  inv := !![1, 0, 0; 0, 1, 0; -a / d, -b / d, d⁻¹]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hd] <;> field_simp <;> ring1
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hd] <;> ring

private theorem coe_bottomRowUnit (a b d : p.adicCompletion ℚ) (hd : d ≠ 0) :
    ((bottomRowUnit p a b d hd : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      !![1, 0, 0; 0, 1, 0; a, b, d] := rfl

private theorem coe_bottomRowUnit_inv (a b d : p.adicCompletion ℚ) (hd : d ≠ 0) :
    (((bottomRowUnit p a b d hd)⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      !![1, 0, 0; 0, 1, 0; -a / d, -b / d, d⁻¹] := rfl

private theorem bottomRowUnit_mem_localMaximalCompact3 {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0)
    (hϖ1 : Valued.v ϖ < 1)
    {a b d : p.adicCompletion ℚ} (ha : ϖ⁻¹ * a ∈ p.adicCompletionIntegers ℚ)
    (hb : ϖ⁻¹ * b ∈ p.adicCompletionIntegers ℚ) (hd1 : ϖ⁻¹ * (d - 1) ∈ p.adicCompletionIntegers ℚ) :
    bottomRowUnit p a b d (ne_zero_of_sub_one_lt p (valued_lt_one_of_inv_mul_mem p hϖ0 hϖ1 hd1)) ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hvd : Valued.v d = 1 := valued_eq_one_of_sub_one_lt p (valued_lt_one_of_inv_mul_mem p hϖ0 hϖ1 hd1)
  have ha' : Valued.v a ≤ 1 := (valued_lt_one_of_inv_mul_mem p hϖ0 hϖ1 ha).le
  have hb' : Valued.v b ≤ 1 := (valued_lt_one_of_inv_mul_mem p hϖ0 hϖ1 hb).le
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_bottomRowUnit]
    fin_cases i <;> fin_cases j <;> simp [ha', hb', hvd]
  · rw [coe_bottomRowUnit_inv]
    fin_cases i <;> fin_cases j <;> simp [map_div₀, map_inv₀, Valuation.map_neg, ha', hb', hvd]

private theorem inv_mul_bottomRowUnit_sub_one_mem {ϖ a b d : p.adicCompletion ℚ} (hd : d ≠ 0)
    (ha : ϖ⁻¹ * a ∈ p.adicCompletionIntegers ℚ) (hb : ϖ⁻¹ * b ∈ p.adicCompletionIntegers ℚ)
    (hd1 : ϖ⁻¹ * (d - 1) ∈ p.adicCompletionIntegers ℚ) (i j : Fin 3) :
    ϖ⁻¹ * (((bottomRowUnit p a b d hd : GL (Fin 3) (p.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ∈ p.adicCompletionIntegers ℚ := by
  rw [coe_bottomRowUnit]
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hd1]

private theorem exists_radicalP21_mul_iotaGL_mul_of_bottomRow {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0)
    (hϖ1 : Valued.v ϖ < 1) (g : GL (Fin 3) (p.adicCompletion ℚ))
    (h0 : ϖ⁻¹ * (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 0 ∈ p.adicCompletionIntegers ℚ)
    (h1 : ϖ⁻¹ * (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 1 ∈ p.adicCompletionIntegers ℚ)
    (h2 : ϖ⁻¹ * ((g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 2 - 1) ∈ p.adicCompletionIntegers ℚ) :
    ∃ (w : Fin 2 → p.adicCompletion ℚ) (h : GL (Fin 2) (p.adicCompletion ℚ)) (k : GL (Fin 3) (p.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
      (∀ i j, ϖ⁻¹ * ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ∈ p.adicCompletionIntegers ℚ) ∧
      g = radicalP21 w * iotaGL h * k := by
  set G : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ) := (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) with hG
  have hd : G 2 2 ≠ 0 := ne_zero_of_sub_one_lt p (valued_lt_one_of_inv_mul_mem p hϖ0 hϖ1 h2)
  set k : GL (Fin 3) (p.adicCompletion ℚ) := bottomRowUnit p (G 2 0) (G 2 1) (G 2 2) hd with hk

  obtain ⟨π, hπ⟩ : ∃ π : GL (Fin 3) (p.adicCompletion ℚ), π = g * k⁻¹ := ⟨_, rfl⟩
  have hπcoe : (π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      G * !![1, 0, 0; 0, 1, 0; -G 2 0 / G 2 2, -G 2 1 / G 2 2, (G 2 2)⁻¹] := by
    rw [hπ, Units.val_mul, hk, coe_bottomRowUnit_inv]
  have hbot0 : (π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 0 = 0 := by
    rw [hπcoe]; simp [Matrix.mul_apply, Fin.sum_univ_three]; field_simp; ring1
  have hbot1 : (π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 1 = 0 := by
    rw [hπcoe]; simp [Matrix.mul_apply, Fin.sum_univ_three]; field_simp; ring1
  have hbot2 : (π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 2 = 1 := by
    rw [hπcoe]; simp [Matrix.mul_apply, Fin.sum_univ_three, hd]

  set M : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) :=
    !![(π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 0 0, (π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 0 1;
       (π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 1 0, (π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 1 1]
    with hM
  have hdetπ : (π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 π.isUnit).ne_zero
  have hdetM : M.det ≠ 0 := by
    intro hzero
    apply hdetπ
    rw [Matrix.det_fin_three, hbot0, hbot1, hbot2]
    rw [Matrix.det_fin_two] at hzero
    simp only [hM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at hzero
    linear_combination hzero
  refine ⟨![(π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 0 2,
      (π : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 1 2],
    Matrix.GeneralLinearGroup.mkOfDetNeZero M hdetM, k,
    bottomRowUnit_mem_localMaximalCompact3 p hϖ0 hϖ1 h0 h1 h2,
    inv_mul_bottomRowUnit_sub_one_mem p hd h0 h1 h2, ?_⟩

  have hgπ : g = π * k := by rw [hπ, inv_mul_cancel_right]
  rw [hgπ]
  congr 1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hval : ((Matrix.GeneralLinearGroup.mkOfDetNeZero M hdetM : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = M := rfl
  rw [Units.val_mul, coe_iotaGL, hval, radicalP21_coe]
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, hM, Matrix.mul_apply, Fin.sum_univ_three, hbot0, hbot1, hbot2]

private theorem bottomRow_mul_inv_congr {ϖ : p.adicCompletion ℚ} (g κ : GL (Fin 3) (p.adicCompletion ℚ))
    (hκ : κ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (hrow : ∀ j, ϖ⁻¹ * ((g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j -
      (κ : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j) ∈ p.adicCompletionIntegers ℚ) (l : Fin 3) :
    ϖ⁻¹ * (((g * κ⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l) ∈ p.adicCompletionIntegers ℚ := by
  have hκ' := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ p).1 hκ
  have hinv : ∀ i j, ((κ⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈
      p.adicCompletionIntegers ℚ := fun i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).2 (hκ'.2 i j)

  have hunit : ∀ l, ∑ j, (κ : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j *
      ((κ⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) j l =
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l := by
    intro l
    have h := congrFun (congrFun (Units.mul_inv κ) 2) l
    simpa [Matrix.mul_apply] using h
  have hexpand :
      ϖ⁻¹ * (((g * κ⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l -
        (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l) =
      ∑ j, (ϖ⁻¹ * ((g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j -
        (κ : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j)) *
        ((κ⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) j l := by
    rw [Units.val_mul, Matrix.mul_apply, ← hunit l, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexpand]
  exact sum_mem fun j _ => mul_mem (hrow j) (hinv j l)

private def bottomRowBall (ϖ : p.adicCompletion ℚ) (c : Fin 3 → p.adicCompletion ℚ) (i : Fin 3) :
    Set (p.adicCompletion ℚ) :=
  {t | ϖ⁻¹ * (t - c i) ∈ p.adicCompletionIntegers ℚ}

private theorem mem_bottomRowBall_iff (ϖ : p.adicCompletion ℚ) (c : Fin 3 → p.adicCompletion ℚ) (i : Fin 3)
    (t : p.adicCompletion ℚ) : t ∈ bottomRowBall p ϖ c i ↔ ϖ⁻¹ * (t - c i) ∈ p.adicCompletionIntegers ℚ := Iff.rfl

private theorem centre_mem_bottomRowBall (ϖ : p.adicCompletion ℚ) (c : Fin 3 → p.adicCompletion ℚ) (i : Fin 3) :
    c i ∈ bottomRowBall p ϖ c i := by
  simp [bottomRowBall]

private theorem bottomRowBall_subset_integers {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    {c : Fin 3 → p.adicCompletion ℚ} (hc : ∀ i, c i ∈ p.adicCompletionIntegers ℚ) (i : Fin 3) :
    bottomRowBall p ϖ c i ⊆ (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
  intro t ht
  have ht' : ϖ⁻¹ * (t - c i) ∈ p.adicCompletionIntegers ℚ := ht
  have hϖmem : ϖ ∈ p.adicCompletionIntegers ℚ :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).2 hϖ1.le
  have key := add_mem (hc i) (mul_mem hϖmem ht')
  simpa [mul_inv_cancel_left₀ hϖ0] using key

private theorem isClopen_bottomRowBall (ϖ : p.adicCompletion ℚ) (c : Fin 3 → p.adicCompletion ℚ) (i : Fin 3) :
    IsClopen (bottomRowBall p ϖ c i) := by
  have hrepr : bottomRowBall p ϖ c i =
      (fun t => ϖ⁻¹ * (t - c i)) ⁻¹' (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := rfl
  rw [hrepr]
  exact (Valued.isClopen_valuationSubring (p.adicCompletion ℚ)).preimage
    (continuous_const.mul (continuous_sub_right _))

end Localisation

section Surgery

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "G₃" => GL (Fin 3) (p.adicCompletion ℚ)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)
local notation "𝒪ₚ" => p.adicCompletionIntegers ℚ
local notation "K₃" => localMaximalCompact3 (𝓞 ℚ) ℚ p
local notation "𝓟" => productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

private def FixedAt (U : Set (GL (Fin 3) (p.adicCompletion ℚ))) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ m ∈ U, ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, φ (x * localToAdelic3 p m) = φ x

variable {p} in
private theorem FixedAt.anti {U V : Set (GL (Fin 3) (p.adicCompletion ℚ))} {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (h : FixedAt p U φ) (hVU : V ⊆ U) : FixedAt p V φ :=
  fun m hm x => h m (hVU hm) x

private theorem fixedAt_translate {U : Set (GL (Fin 3) (p.adicCompletion ℚ))} {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : FixedAt p U φ) (t : AdelicGL 3 (𝓞 ℚ) ℚ) :
    FixedAt p {m | (componentAt3 (𝓞 ℚ) ℚ p t)⁻¹ * m * componentAt3 (𝓞 ℚ) ℚ p t ∈ U} fun x => φ (x * t) := by
  intro m hm x
  show φ (x * localToAdelic3 p m * t) = φ (x * t)
  have hex := mul_localToAdelic3_eq_localToAdelic3_mul p t
    ((componentAt3 (𝓞 ℚ) ℚ p t)⁻¹ * m * componentAt3 (𝓞 ℚ) ℚ p t) m (by group)
  rw [mul_assoc, ← hex, ← mul_assoc, hφ _ hm]

private theorem fixedAt_comb {J : Type*} [Fintype J] (c : J → ℂ) (τ : J → AdelicGL 3 (𝓞 ℚ) ℚ)
    {U : Set (GL (Fin 3) (p.adicCompletion ℚ))} {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (h : ∀ j, FixedAt p U fun x => φ (x * τ j)) : FixedAt p U (comb c τ φ) := by
  intro m hm x
  simp only [comb]
  exact Finset.sum_congr rfl fun j _ => by
    have h' := h j m hm x
    beta_reduce at h'
    rw [h']

private theorem whittaker3_mul_localToAdelic3 (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    {U : Set (GL (Fin 3) (p.adicCompletion ℚ))} {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : FixedAt p U φ)
    {m : GL (Fin 3) (p.adicCompletion ℚ)} (hm : m ∈ U) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ φ (g * localToAdelic3 p m) = whittaker3 pins ψ φ g := by
  rw [← whittaker3_translate]
  exact congrArg (fun φ' => whittaker3 pins ψ φ' g) (funext fun x => hφ m hm x)

private theorem whittaker3_surgery (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (U : Set (GL (Fin 3) (p.adicCompletion ℚ))) (hU : FixedAt p U φ)
    {J : Type*} [Fintype J] (coef : J → ℂ) (t : J → GL (Fin 3) (p.adicCompletion ℚ))
    (κ q k : GL (Fin 3) (p.adicCompletion ℚ)) (A B Cf : J → p.adicCompletion ℚ)
    (hconj : ∀ j, q * t j * q⁻¹ = upperUnipotent3 (A j) (B j) (Cf j))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : componentAt3 (𝓞 ℚ) ℚ p g = q * k * κ)
    (hk : ∀ j, κ⁻¹ * (k⁻¹ * (t j)⁻¹ * k * t j) * κ ∈ U) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ
        (comb coef (fun j => localToAdelic3 p (κ⁻¹ * t j * κ)) φ) g =
      (∑ j, coef j * psiV p (A j + B j)) *
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ g := by
  rw [whittaker3_comb ∅ (fun _ => ⊥) (fun _ => 1) coef _ hφc g, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc (coef j) (psiV p (A j + B j))]
  refine congrArg (fun w => coef j * w) ?_

  set m : GL (Fin 3) (p.adicCompletion ℚ) := κ⁻¹ * (k⁻¹ * (t j)⁻¹ * k * t j) * κ with hm
  have hsplit : localToAdelic3 p (κ⁻¹ * t j * κ) =
      localToAdelic3 p (κ⁻¹ * t j * κ * m⁻¹) * localToAdelic3 p m := by
    rw [← MonoidHom.map_mul, inv_mul_cancel_right]
  have hex : g * localToAdelic3 p (κ⁻¹ * t j * κ * m⁻¹) = localToAdelic3 p (q * t j * q⁻¹) * g :=
    mul_localToAdelic3_eq_localToAdelic3_mul p g _ _ (by rw [hg, hm]; group)
  rw [hsplit, ← mul_assoc, hex, whittaker3_mul_localToAdelic3 p _ psiQ hU (hk j), hconj j,
    localToAdelic3_upperUnipotent3,
    (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul φ haut).1,
    ← (adeleSingleAt ℚ p).map_add, psiQ_adeleSingleAt]

private theorem whittaker3_eq_zero_of_psiV_ne_one (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (U : Set (GL (Fin 3) (p.adicCompletion ℚ))) (hU : FixedAt p U φ)
    (κ q k u : GL (Fin 3) (p.adicCompletion ℚ)) (a b c : p.adicCompletion ℚ)
    (hconj : q * u * q⁻¹ = upperUnipotent3 a b c) (hu : κ⁻¹ * u * κ ∈ U)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : componentAt3 (𝓞 ℚ) ℚ p g = q * k * κ)
    (hk : κ⁻¹ * (k⁻¹ * u⁻¹ * k * u) * κ ∈ U) (hne : psiV p (a + b) ≠ 1) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ g = 0 := by
  have h := whittaker3_surgery p φ hφc haut U hU (fun _ : Unit => (1 : ℂ)) (fun _ => u) κ q k (fun _ => a)
    (fun _ => b) (fun _ => c) (fun _ => hconj) g hg (fun _ => hk)
  have hL : whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ
      (comb (fun _ : Unit => (1 : ℂ)) (fun _ => localToAdelic3 p (κ⁻¹ * u * κ)) φ) g =
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ g := by
    rw [whittaker3_comb ∅ (fun _ => ⊥) (fun _ => 1) _ _ hφc g, Finset.univ_unique, Finset.sum_singleton, one_mul,
      whittaker3_mul_localToAdelic3 p _ psiQ hU hu]
  have hR : ∑ _j : Unit, (1 : ℂ) * psiV p (a + b) = psiV p (a + b) := by
    rw [Finset.univ_unique, Finset.sum_singleton, one_mul]
  rw [hL, hR] at h
  have hzero : (1 - psiV p (a + b)) *
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ g = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp hzero with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hne
  · exact h0

private theorem lower_factor_facts {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) (n₀ : ℕ)
    (h b c : GL (Fin 2) (p.adicCompletion ℚ))
    (hb : (b : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![(h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det / (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1,
        (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 / (h : Matrix (Fin 2) (Fin 2) _) 1 1; 0, 1])
    (hc : (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1, 0; (h : Matrix (Fin 2) (Fin 2) _) 1 0, (h : Matrix (Fin 2) (Fin 2) _) 1 1])
    (hγ : (ϖ ^ (n₀ + 3))⁻¹ * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ∈ p.adicCompletionIntegers ℚ)
    (hδ : (ϖ ^ (n₀ + 2))⁻¹ * ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 - 1) ∈
      p.adicCompletionIntegers ℚ) :
    (b : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 ∧
      (b : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1 ∧
      (c : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
        !![1, 0; (c : Matrix (Fin 2) (Fin 2) _) 1 0, (c : Matrix (Fin 2) (Fin 2) _) 1 1] ∧
      iotaGL c ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ IsLevel p ϖ n₀ (iotaGL c) ∧
      ∀ x : p.adicCompletion ℚ, ϖ * x ∈ p.adicCompletionIntegers ℚ →
        (upperUnipotent3 x 0 0 : GL (Fin 3) (p.adicCompletion ℚ))⁻¹ * iotaGL c * upperUnipotent3 x 0 0 ∈
            localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
          IsLevel p ϖ n₀ ((upperUnipotent3 x 0 0 : GL (Fin 3) (p.adicCompletion ℚ))⁻¹ * iotaGL c *
            upperUnipotent3 x 0 0) := by
  have hc10 : (c : M₂) 1 0 = (h : M₂) 1 0 := by simp [hc]
  have hc11 : (c : M₂) 1 1 = (h : M₂) 1 1 := by simp [hc]
  have hc' : (c : M₂) = !![1, 0; (c : M₂) 1 0, (c : M₂) 1 1] := by
    rw [hc10, hc11]; exact hc
  have hδv : Valued.v ((h : M₂) 1 1) = 1 :=
    valued_eq_one_of_sub_one_lt p (valued_sub_one_lt_of_level p hϖ0 hϖ1 hδ)
  refine ⟨by simp [hb], by simp [hb], hc', ?_, ?_, fun x hx => ?_⟩
  · exact iotaGL_mem_localMaximalCompact3_of_lower p c hc' (hc10 ▸ mem_integers_of_level p hϖ0 hϖ1 hγ)
      (hc11 ▸ hδv)
  · exact isLevel_iotaGL_lower p c hc' (hc10 ▸ level_mono p hϖ0 hϖ1 (by omega) hγ)
      (hc11 ▸ level_mono p hϖ0 hϖ1 (by omega) hδ)
  · rw [upperUnipotent3_inv, neg_zero, mul_zero, sub_zero]
    exact isLevel_conj_iotaGL_lower p hϖ0 hϖ1 c hc' (hc10 ▸ level_mono p hϖ0 hϖ1 (by omega) hγ)
      (hc11 ▸ level_mono p hϖ0 hϖ1 (by omega) hδ) hx

private theorem surgery_coreA
    {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {n₀ : ℕ}
    {U : Set (G₃)} (hU1 : (1 : G₃) ∈ U)
    (κ : G₃)
    (habs : ∀ m ∈ K₃, IsLevel p ϖ n₀ m → κ⁻¹ * m * κ ∈ U)
    {J₁ J₂ J₃ : Type} [Fintype J₁] [Fintype J₂] [Fintype J₃] (y₁ : J₁ → p.adicCompletion ℚ)
    (y₂ : J₂ → p.adicCompletion ℚ) (y₃ : J₃ → p.adicCompletion ℚ) (e₁ : J₁ → ℂ) (e₂ : J₂ → ℂ) (e₃ : J₃ → ℂ)
    (hy₃' : ∀ j, ϖ * y₃ j ∈ 𝒪ₚ)
    (tA1 : J₁ → G₃) (htA1 : ∀ j, tA1 j = radicalP21 ![y₁ j, 0])
    (tA2 : J₂ → G₃) (htA2 : ∀ j, tA2 j = radicalP21 ![0, y₂ j])
    (tB : J₃ → G₃) (htB : ∀ j, tB j = upperUnipotent3 (y₃ j) 0 0)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (hUφ : FixedAt p U φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (w : Fin 2 → p.adicCompletion ℚ)
    (h : GL (Fin 2) (p.adicCompletion ℚ))
    (k : G₃) (hg : componentAt3 (𝓞 ℚ) ℚ p g = radicalP21 w * iotaGL h * k * κ)
    (hVA : ∀ jj : J₁ × J₂ × J₃, κ⁻¹ * ((tB jj.2.2)⁻¹ * ((tA2 jj.2.1)⁻¹ * (k⁻¹ * (tA1 jj.1)⁻¹ * k * tA1 jj.1) *
      tA2 jj.2.1) * tB jj.2.2) * κ ∈ U)
    (hVB : ∀ jj : J₂ × J₃, κ⁻¹ * ((tB jj.2)⁻¹ * (k⁻¹ * (tA2 jj.1)⁻¹ * k * tA2 jj.1) * tB jj.2) * κ ∈ U)
    (hVC : ∀ jj : J₂ × J₃, (tB jj.2)⁻¹ * ((tA2 jj.1)⁻¹ * k * tA2 jj.1) * tB jj.2 ∈ K₃)
    (hVD : ∀ j : J₃, (tB j)⁻¹ * k * tB j ∈ K₃ ∧ IsLevel p ϖ n₀ ((tB j)⁻¹ * k * tB j)) :
    (whittaker3 𝓟 psiQ
        (comb e₁ (fun j => localToAdelic3 p (κ⁻¹ * tA1 j * κ))
          (comb e₂ (fun j => localToAdelic3 p (κ⁻¹ * tA2 j * κ))
            (comb e₃ (fun j => localToAdelic3 p (κ⁻¹ * tB j * κ)) φ))) g =
      (∑ j, e₁ j * psiV p ((h : M₂) 1 0 * y₁ j)) *
        whittaker3 𝓟 psiQ
          (comb e₂ (fun j => localToAdelic3 p (κ⁻¹ * tA2 j * κ))
            (comb e₃ (fun j => localToAdelic3 p (κ⁻¹ * tB j * κ)) φ)) g) ∧
    (whittaker3 𝓟 psiQ
        (comb e₂ (fun j => localToAdelic3 p (κ⁻¹ * tA2 j * κ))
          (comb e₃ (fun j => localToAdelic3 p (κ⁻¹ * tB j * κ)) φ)) g =
      (∑ j, e₂ j * psiV p ((h : M₂) 1 1 * y₂ j)) *
        whittaker3 𝓟 psiQ (comb e₃ (fun j => localToAdelic3 p (κ⁻¹ * tB j * κ)) φ) g) ∧
    (ϖ ^ (n₀ + 1) * (h : M₂) 1 0 ∉ 𝒪ₚ →
      whittaker3 𝓟 psiQ
        (comb e₂ (fun j => localToAdelic3 p (κ⁻¹ * tA2 j * κ))
          (comb e₃ (fun j => localToAdelic3 p (κ⁻¹ * tB j * κ)) φ)) g = 0) ∧
    (ϖ ^ (n₀ + 1) * (h : M₂) 1 1 ∉ 𝒪ₚ →
      whittaker3 𝓟 psiQ (comb e₃ (fun j => localToAdelic3 p (κ⁻¹ * tB j * κ)) φ) g = 0) := by
  set ψ₃ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := comb e₃ (fun j => localToAdelic3 p (κ⁻¹ * tB j * κ)) φ with hψ₃
  set ψ₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := comb e₂ (fun j => localToAdelic3 p (κ⁻¹ * tA2 j * κ)) ψ₃ with hψ₂
  set ψ₁ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := comb e₁ (fun j => localToAdelic3 p (κ⁻¹ * tA1 j * κ)) ψ₂ with hψ₁

  have hψ₃c : Continuous ψ₃ := continuous_comb _ _ hφc
  have hψ₂c : Continuous ψ₂ := continuous_comb _ _ hψ₃c
  have hψ₃a : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), ψ₃ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = ψ₃ g :=
    comb_globalPointsGL_mul _ _ haut
  have hψ₂a : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), ψ₂ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = ψ₂ g :=
    comb_globalPointsGL_mul _ _ hψ₃a
  have hlev : ∀ {V' : Set (G₃)} {φ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (t' : G₃), FixedAt p V' φ' →
      FixedAt p {m | (κ⁻¹ * t' * κ)⁻¹ * m * (κ⁻¹ * t' * κ) ∈ V'}
        fun x => φ' (x * localToAdelic3 p (κ⁻¹ * t' * κ)) := by
    intro V' φ' t' h
    have := fixedAt_translate p h (localToAdelic3 p (κ⁻¹ * t' * κ))
    rwa [componentAt3_localToAdelic3_self] at this
  set U₃ : Set (G₃) := {m | ∀ j, (κ⁻¹ * tB j * κ)⁻¹ * m * (κ⁻¹ * tB j * κ) ∈ U} with hU₃
  set U₂ : Set (G₃) := {m | ∀ j, (κ⁻¹ * tA2 j * κ)⁻¹ * m * (κ⁻¹ * tA2 j * κ) ∈ U₃} with hU₂
  have hψ₃U : FixedAt p U₃ ψ₃ :=
    fixedAt_comb p _ _ fun j => (hlev (tB j) hUφ).anti fun m hm => hm j
  have hψ₂U : FixedAt p U₂ ψ₂ :=
    fixedAt_comb p _ _ fun j => (hlev (tA2 j) hψ₃U).anti fun m hm => hm j
  set q₀ : G₃ := radicalP21 w * iotaGL h with hq₀
  have hg' : componentAt3 (𝓞 ℚ) ℚ p g = q₀ * k * κ := by rw [hq₀]; exact hg

  have hconjA : ∀ yv : Fin 2 → p.adicCompletion ℚ, q₀ * radicalP21 yv * q₀⁻¹ =
      upperUnipotent3 0 (((h : M₂) *ᵥ yv) 1)
        (((h : M₂) *ᵥ yv) 0) := fun yv => by
    rw [mul_inv_eq_iff_eq_mul, hq₀, radicalP21_mul_iotaGL_mul_radicalP21]
  have hmv1 : ∀ j, (0 : p.adicCompletion ℚ) + ((h : M₂) *ᵥ ![y₁ j, 0]) 1 =
      (h : M₂) 1 0 * y₁ j := fun j => by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hmv2 : ∀ j, (0 : p.adicCompletion ℚ) + ((h : M₂) *ᵥ ![0, y₂ j]) 1 =
      (h : M₂) 1 1 * y₂ j := fun j => by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

  have hradcomm : ∀ a b : Fin 2 → p.adicCompletion ℚ, (radicalP21 a)⁻¹ * radicalP21 b * radicalP21 a =
      (radicalP21 b : G₃) := fun a b => by
    rw [mul_assoc, ← radicalP21_add, add_comm, radicalP21_add, ← mul_assoc, inv_mul_cancel, one_mul]
  have hBconjrad : ∀ (j : J₃) (b : Fin 2 → p.adicCompletion ℚ), (tB j)⁻¹ * radicalP21 b * tB j =
      (radicalP21 ![b 0 - y₃ j * b 1, b 1] : G₃) := fun j b => by
    rw [htB, upperUnipotent3_inv, neg_zero, mul_zero, sub_zero, upperUnipotent3_neg_mul_radicalP21_mul_upperUnipotent3]

  have hA1 : whittaker3 𝓟 psiQ ψ₁ g =
      (∑ j, e₁ j * psiV p ((h : M₂) 1 0 * y₁ j)) *
        whittaker3 𝓟 psiQ ψ₂ g := by
    have := whittaker3_surgery p ψ₂ hψ₂c hψ₂a U₂ hψ₂U e₁ tA1 κ q₀ k (fun _ => 0)
      (fun j => ((h : M₂) *ᵥ ![y₁ j, 0]) 1)
      (fun j => ((h : M₂) *ᵥ ![y₁ j, 0]) 0)
      (fun j => by rw [htA1]; exact hconjA _) g hg' (fun j₁ => by
        simp only [hU₂, hU₃, Set.mem_setOf_eq]
        intro m₂ m₃
        rw [word_comm₂ κ (tB m₃) (tA2 m₂) k (tA1 j₁)]
        exact hVA (j₁, m₂, m₃))
    simpa only [hmv1] using this

  have hA2 : whittaker3 𝓟 psiQ ψ₂ g =
      (∑ j, e₂ j * psiV p ((h : M₂) 1 1 * y₂ j)) *
        whittaker3 𝓟 psiQ ψ₃ g := by
    have := whittaker3_surgery p ψ₃ hψ₃c hψ₃a U₃ hψ₃U e₂ tA2 κ q₀ k (fun _ => 0)
      (fun j => ((h : M₂) *ᵥ ![0, y₂ j]) 1)
      (fun j => ((h : M₂) *ᵥ ![0, y₂ j]) 0)
      (fun j => by rw [htA2]; exact hconjA _) g hg' (fun j₂ => by
        simp only [hU₃, Set.mem_setOf_eq]
        intro m₃
        rw [word_comm₁ κ (tB m₃) k (tA2 j₂)]
        exact hVB (j₂, m₃))
    simpa only [hmv2] using this

  have hP1 : ϖ ^ (n₀ + 1) * (h : M₂) 1 0 ∉ 𝒪ₚ →
      whittaker3 𝓟 psiQ ψ₂ g = 0 := by
    intro hγ
    obtain ⟨y₀, hy₀, hne⟩ := exists_psiV_ne_one p hϖ0 hϖ1 (n₀ + 1) _ hγ
    have hy₀int : y₀ ∈ 𝒪ₚ := mem_integers_of_level p hϖ0 hϖ1 hy₀
    have huK : (radicalP21 ![y₀, 0] : G₃) ∈ K₃ :=
      radicalP21_mem_localMaximalCompact3 p fun i => by fin_cases i <;> simp [hy₀int, zero_mem]
    have huL : IsLevel p ϖ n₀ (radicalP21 ![y₀, 0]) :=
      isLevel_radicalP21 p fun i => by
        fin_cases i
        · simpa using level_mono p hϖ0 hϖ1 (Nat.le_succ n₀) hy₀
        · simp [zero_mem]
    refine whittaker3_eq_zero_of_psiV_ne_one p ψ₂ hψ₂c hψ₂a U₂ hψ₂U (k * κ) q₀ 1 (radicalP21 ![y₀, 0]) 0
      (((h : M₂) *ᵥ ![y₀, 0]) 1)
      (((h : M₂) *ᵥ ![y₀, 0]) 0) (hconjA _) ?_ g
      (by rw [hg', mul_one, mul_assoc]) (by
        simp only [hU₂, hU₃, Set.mem_setOf_eq, inv_one, one_mul, inv_mul_cancel, mul_one]
        exact fun _ _ => hU1) ?_
    · simp only [hU₂, hU₃, Set.mem_setOf_eq]
      intro j₂ j₃
      have key := habs _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hVC (j₂, j₃))) huK)
        (hVC (j₂, j₃))) (huL.conj p (hVC (j₂, j₃)))
      rw [word_conj₂ κ (tB j₃) (tA2 j₂) k (radicalP21 ![y₀, 0]),
        show (tA2 j₂)⁻¹ * (radicalP21 ![y₀, 0] : G₃) * tA2 j₂ = radicalP21 ![y₀, 0] from by
          rw [htA2]; exact hradcomm _ _, hBconjrad]
      simpa using key
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hne

  have hP2 : ϖ ^ (n₀ + 1) * (h : M₂) 1 1 ∉ 𝒪ₚ →
      whittaker3 𝓟 psiQ ψ₃ g = 0 := by
    intro hδ
    obtain ⟨y₀, hy₀, hne⟩ := exists_psiV_ne_one p hϖ0 hϖ1 (n₀ + 1) _ hδ
    have hy₀int : y₀ ∈ 𝒪ₚ := mem_integers_of_level p hϖ0 hϖ1 hy₀
    have hy₀n : (ϖ ^ n₀)⁻¹ * y₀ ∈ 𝒪ₚ := level_mono p hϖ0 hϖ1 (Nat.le_succ n₀) hy₀
    have hxy : ∀ j, (ϖ ^ n₀)⁻¹ * (y₃ j * y₀) ∈ 𝒪ₚ := fun j => level_mul_of_region p hϖ0 (hy₃' j) hy₀
    have hu''K : ∀ j, (radicalP21 ![0 - y₃ j * y₀, y₀] : G₃) ∈ K₃ := fun j =>
      radicalP21_mem_localMaximalCompact3 p fun i => by
        fin_cases i
        · simpa using neg_mem (mem_integers_of_level p hϖ0 hϖ1 (hxy j))
        · simpa using hy₀int
    have hu''L : ∀ j, IsLevel p ϖ n₀ (radicalP21 ![0 - y₃ j * y₀, y₀]) := fun j =>
      isLevel_radicalP21 p fun i => by
        fin_cases i
        · simpa [mul_neg] using neg_mem (hxy j)
        · simpa using hy₀n
    refine whittaker3_eq_zero_of_psiV_ne_one p ψ₃ hψ₃c hψ₃a U₃ hψ₃U (k * κ) q₀ 1 (radicalP21 ![0, y₀]) 0
      (((h : M₂) *ᵥ ![0, y₀]) 1)
      (((h : M₂) *ᵥ ![0, y₀]) 0) (hconjA _) ?_ g
      (by rw [hg', mul_one, mul_assoc]) (by
        simp only [hU₃, Set.mem_setOf_eq, inv_one, one_mul, inv_mul_cancel, mul_one]
        exact fun _ => hU1) ?_
    · simp only [hU₃, Set.mem_setOf_eq]
      intro j₃
      have key := habs _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hVD j₃).1) (hu''K j₃))
        (hVD j₃).1) ((hu''L j₃).conj p (hVD j₃).1)
      rw [word_conj₁ κ (tB j₃) k (radicalP21 ![0, y₀]), hBconjrad]
      simpa using key
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hne
  exact ⟨hA1, hA2, hP1, hP2⟩

private theorem surgery_coreB
    {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {n₀ : ℕ}
    {U : Set (G₃)} (hU1 : (1 : G₃) ∈ U) (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U)
    (κ : G₃)
    (habs : ∀ m ∈ K₃, IsLevel p ϖ n₀ m → κ⁻¹ * m * κ ∈ U)
    {J₃ : Type} [Fintype J₃] (y₃ : J₃ → p.adicCompletion ℚ) (e₃ : J₃ → ℂ)
    (tB : J₃ → G₃) (htB : ∀ j, tB j = upperUnipotent3 (y₃ j) 0 0)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (hUφ : FixedAt p U φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (w : Fin 2 → p.adicCompletion ℚ)
    (h b c : GL (Fin 2) (p.adicCompletion ℚ)) (hbc : h = b * c)
    (hb10 : (b : M₂) 1 0 = 0) (hb11 : (b : M₂) 1 1 = 1)
    (k : G₃) (hkK : k ∈ K₃) (hkn₀ : IsLevel p ϖ n₀ k)
    (hg : componentAt3 (𝓞 ℚ) ℚ p g = radicalP21 w * iotaGL h * k * κ)
    (hcK : iotaGL c ∈ K₃) (hcL : IsLevel p ϖ n₀ (iotaGL c))
    (hcB : ∀ j, (tB j)⁻¹ * iotaGL c * tB j ∈ K₃ ∧ IsLevel p ϖ n₀ ((tB j)⁻¹ * iotaGL c * tB j))
    (hVD : ∀ j : J₃, (tB j)⁻¹ * k * tB j ∈ K₃ ∧ IsLevel p ϖ n₀ ((tB j)⁻¹ * k * tB j)) :
    (whittaker3 𝓟 psiQ (comb e₃ (fun j => localToAdelic3 p (κ⁻¹ * tB j * κ)) φ) g =
      (∑ j, e₃ j * psiV p ((b : M₂) 0 0 * y₃ j)) *
        whittaker3 𝓟 psiQ φ g) ∧
    (ϖ ^ (n₀ + 1) * (b : M₂) 0 0 ∉ 𝒪ₚ →
      whittaker3 𝓟 psiQ φ g = 0) := by

  set β : G₃ := radicalP21 w * iotaGL b with hβ
  have hgB : componentAt3 (𝓞 ℚ) ℚ p g = β * (iotaGL c * k) * κ := by
    rw [hg, hbc, MonoidHom.map_mul, hβ]; simp only [mul_assoc]
  have hconjB : ∀ x : p.adicCompletion ℚ, β * upperUnipotent3 x 0 0 * β⁻¹ =
      upperUnipotent3 ((b : M₂) 0 0 * x) 0
        (-((b : M₂) 0 0 * x * w 1)) := fun x => by
    rw [mul_inv_eq_iff_eq_mul, hβ, radicalP21_mul_iotaGL_mul_upperUnipotent3 w b hb10 hb11]
  have hkBK : iotaGL c * k ∈ K₃ := Subgroup.mul_mem _ hcK hkK
  have hkBL : IsLevel p ϖ n₀ (iotaGL c * k) := hcL.mul p hkn₀ hkK
  have hkB1 : κ⁻¹ * (iotaGL c * k)⁻¹ * κ ∈ U :=
    habs _ (Subgroup.inv_mem _ hkBK) (hkBL.inv p hkBK)
  refine ⟨?_, fun ht => ?_⟩
  · have := whittaker3_surgery p φ hφc haut U hUφ e₃ tB κ β (iotaGL c * k)
      (fun j => (b : M₂) 0 0 * y₃ j) (fun _ => 0)
      (fun j => -((b : M₂) 0 0 * y₃ j * w 1))
      (fun j => by rw [htB]; exact hconjB _) g hgB (fun j => by
        have h2 : κ⁻¹ * ((tB j)⁻¹ * ((iotaGL c : G₃) * k) * tB j) * κ ∈ U := by
          rw [word_split (tB j) (iotaGL c : G₃) k]
          exact habs _ (Subgroup.mul_mem _ (hcB j).1 (hVD j).1) ((hcB j).2.mul p (hVD j).2 (hVD j).1)
        rw [word_conj₃ κ ((iotaGL c : G₃) * k) (tB j)]
        exact hUmul _ hkB1 _ h2)
    simpa only [add_zero] using this
  · obtain ⟨x₀, hx₀, hne⟩ := exists_psiV_ne_one p hϖ0 hϖ1 (n₀ + 1) _ ht
    have hx₀int : x₀ ∈ 𝒪ₚ := mem_integers_of_level p hϖ0 hϖ1 hx₀
    have huK : (upperUnipotent3 x₀ 0 0 : G₃) ∈ K₃ := upperUnipotent3_mem_localMaximalCompact3 p hx₀int
    have huL : IsLevel p ϖ n₀ (upperUnipotent3 x₀ 0 0) :=
      isLevel_upperUnipotent3 p (level_mono p hϖ0 hϖ1 (Nat.le_succ n₀) hx₀)
    refine whittaker3_eq_zero_of_psiV_ne_one p φ hφc haut U hUφ (iotaGL c * k * κ) β 1 (upperUnipotent3 x₀ 0 0)
      _ _ _ (hconjB x₀) ?_ g (by rw [hgB, mul_one, mul_assoc]) ?_ (by simpa only [add_zero] using hne)
    · rw [word_conj₀ ((iotaGL c : G₃) * k) κ (upperUnipotent3 x₀ 0 0)]
      exact habs _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkBK) huK) hkBK) (huL.conj p hkBK)
    · simp only [inv_one, one_mul, inv_mul_cancel, mul_one]
      exact hU1

private theorem exists_surgery (κ : GL (Fin 3) (p.adicCompletion ℚ)) (hκ : κ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (U : Set (GL (Fin 3) (p.adicCompletion ℚ))) (hUo : IsOpen U) (hU1 : (1 : GL (Fin 3) (p.adicCompletion ℚ)) ∈ U)
    (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) {ϖ : p.adicCompletion ℚ} (hϖ0 : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) :
    ∃ (J : Type) (_ : Fintype J) (coef : J → ℂ) (t : J → GL (Fin 3) (p.adicCompletion ℚ)) (N : ℕ),
      ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous φ →
        (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) →
        FixedAt p U φ →
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (w : Fin 2 → p.adicCompletion ℚ) (h : GL (Fin 2) (p.adicCompletion ℚ))
            (k : GL (Fin 3) (p.adicCompletion ℚ)), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p → IsLevel p ϖ N k →
          componentAt3 (𝓞 ℚ) ℚ p g = radicalP21 w * iotaGL h * k * κ →
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ
              (comb coef (fun j => localToAdelic3 p (κ⁻¹ * t j * κ)) φ) g = 0 ∨
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ
              (comb coef (fun j => localToAdelic3 p (κ⁻¹ * t j * κ)) φ) g =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ g ∧
            ∃ (x y z : p.adicCompletion ℚ) (k' : GL (Fin 3) (p.adicCompletion ℚ)),
              k' ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ radicalP21 w * iotaGL h = upperUnipotent3 x y z * k')) ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x y z : p.adicCompletion ℚ),
          componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * κ →
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ
              (comb coef (fun j => localToAdelic3 p (κ⁻¹ * t j * κ)) φ) g =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ g) ∧
        (∀ (q : HeightOneSpectrum (𝓞 ℚ)) (V : Set (GL (Fin 3) (q.adicCompletion ℚ))), q ≠ p → FixedAt q V φ →
          FixedAt q V (comb coef (fun j => localToAdelic3 p (κ⁻¹ * t j * κ)) φ)) := by
  classical
  have _ := hκ

  obtain ⟨n₀, hn₀⟩ := exists_levelBall_subset p hϖ0 hϖ1 (U := {m | κ⁻¹ * m * κ ∈ U})
    (hUo.preimage (continuous_mul_mul κ⁻¹ κ)) (by simpa only [Set.mem_setOf_eq, mul_one, inv_mul_cancel] using hU1)
  have habs : ∀ m ∈ K₃, IsLevel p ϖ n₀ m → κ⁻¹ * m * κ ∈ U :=
    fun m hm hl => hn₀ m hm hl
  have h0reg : ϖ ^ (n₀ + 1) * (0 : p.adicCompletion ℚ) ∈ 𝒪ₚ := by rw [mul_zero]; exact zero_mem _
  have hϖint : ϖ ∈ 𝒪ₚ := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).2 hϖ1.le
  have h1reg : ϖ ^ (n₀ + 1) * (1 : p.adicCompletion ℚ) ∈ 𝒪ₚ := by rw [mul_one]; exact pow_mem hϖint _

  obtain ⟨J₁, _, y₁, e₁, hy₁, hF₁⟩ := exists_charSum_eq_indicator p hϖ0 hϖ1 (n₀ + 1) (n₀ + 3) 0 h0reg
  obtain ⟨J₂, _, y₂, e₂, hy₂, hF₂⟩ := exists_charSum_eq_indicator p hϖ0 hϖ1 (n₀ + 1) (n₀ + 2) 1 h1reg
  obtain ⟨J₃, _, y₃, e₃, hy₃, hF₃⟩ := exists_charSum_eq_indicator p hϖ0 hϖ1 (n₀ + 1) 1 1 h1reg

  set tA1 : J₁ → G₃ := fun j => radicalP21 ![y₁ j, 0] with htA1
  set tA2 : J₂ → G₃ := fun j => radicalP21 ![0, y₂ j] with htA2
  set tB : J₃ → G₃ := fun j => upperUnipotent3 (y₃ j) 0 0 with htB
  have hy₃' : ∀ j, ϖ * y₃ j ∈ 𝒪ₚ := fun j => by simpa only [pow_one] using hy₃ j

  set V : Set (G₃) :=
    (⋂ jj : J₁ × J₂ × J₃, {k | κ⁻¹ * ((tB jj.2.2)⁻¹ * ((tA2 jj.2.1)⁻¹ * (k⁻¹ * (tA1 jj.1)⁻¹ * k * tA1 jj.1) *
      tA2 jj.2.1) * tB jj.2.2) * κ ∈ U}) ∩
    (⋂ jj : J₂ × J₃, {k | κ⁻¹ * ((tB jj.2)⁻¹ * (k⁻¹ * (tA2 jj.1)⁻¹ * k * tA2 jj.1) * tB jj.2) * κ ∈
      U}) ∩
    (⋂ jj : J₂ × J₃, {k | (tB jj.2)⁻¹ * ((tA2 jj.1)⁻¹ * k * tA2 jj.1) * tB jj.2 ∈ K₃}) ∩
    (⋂ j : J₃, {k | (tB j)⁻¹ * k * tB j ∈ K₃ ∧ IsLevel p ϖ n₀ ((tB j)⁻¹ * k * tB j)}) with hV

  have c1 : ∀ jj : J₁ × J₂ × J₃, Continuous fun k : G₃ =>
      κ⁻¹ * ((tB jj.2.2)⁻¹ * ((tA2 jj.2.1)⁻¹ * (k⁻¹ * (tA1 jj.1)⁻¹ * k * tA1 jj.1) * tA2 jj.2.1) * tB jj.2.2) * κ :=
    fun jj => (continuous_mul_mul κ⁻¹ κ).comp ((continuous_mul_mul (tB jj.2.2)⁻¹ (tB jj.2.2)).comp
      ((continuous_mul_mul (tA2 jj.2.1)⁻¹ (tA2 jj.2.1)).comp (continuous_commWord (tA1 jj.1)⁻¹ (tA1 jj.1))))
  have c2 : ∀ jj : J₂ × J₃, Continuous fun k : G₃ =>
      κ⁻¹ * ((tB jj.2)⁻¹ * (k⁻¹ * (tA2 jj.1)⁻¹ * k * tA2 jj.1) * tB jj.2) * κ :=
    fun jj => (continuous_mul_mul κ⁻¹ κ).comp ((continuous_mul_mul (tB jj.2)⁻¹ (tB jj.2)).comp
      (continuous_commWord (tA2 jj.1)⁻¹ (tA2 jj.1)))
  have c3 : ∀ jj : J₂ × J₃, Continuous fun k : G₃ => (tB jj.2)⁻¹ * ((tA2 jj.1)⁻¹ * k * tA2 jj.1) * tB jj.2 :=
    fun jj => (continuous_mul_mul (tB jj.2)⁻¹ (tB jj.2)).comp (continuous_mul_mul (tA2 jj.1)⁻¹ (tA2 jj.1))
  have c4 : ∀ j : J₃, Continuous fun k : G₃ => (tB j)⁻¹ * k * tB j := fun j => continuous_mul_mul (tB j)⁻¹ (tB j)
  have hVo : IsOpen V :=
    ((IsOpen.inter (isOpen_iInter_of_finite fun jj => (c1 jj).isOpen_preimage _ hUo)
      (isOpen_iInter_of_finite fun jj => (c2 jj).isOpen_preimage _ hUo)).inter
      (isOpen_iInter_of_finite fun jj => (c3 jj).isOpen_preimage _ (isOpen_localMaximalCompact3 p))).inter
      (isOpen_iInter_of_finite fun j => ((c4 j).isOpen_preimage _ (isOpen_localMaximalCompact3 p)).inter
        ((c4 j).isOpen_preimage _ (isOpen_setOf_isLevel p ϖ n₀)))
  have hV1 : (1 : G₃) ∈ V := by
    simp only [hV, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, inv_one, mul_one, one_mul, inv_mul_cancel]
    exact ⟨⟨⟨fun _ => hU1, fun _ => hU1⟩, fun _ => Subgroup.one_mem _⟩,
      fun _ => ⟨Subgroup.one_mem _, isLevel_one p ϖ n₀⟩⟩
  obtain ⟨N₁, hN₁⟩ := exists_levelBall_subset p hϖ0 hϖ1 hVo hV1
  refine ⟨(J₁ × J₂) × J₃, inferInstance, fun jj => e₁ jj.1.1 * e₂ jj.1.2 * e₃ jj.2,
    fun jj => tA1 jj.1.1 * tA2 jj.1.2 * tB jj.2, N₁ + n₀, fun φ hφc haut hUφ => ?_⟩

  have hflat : comb (fun jj : (J₁ × J₂) × J₃ => e₁ jj.1.1 * e₂ jj.1.2 * e₃ jj.2)
      (fun jj => localToAdelic3 p (κ⁻¹ * (tA1 jj.1.1 * tA2 jj.1.2 * tB jj.2) * κ)) φ =
      comb e₁ (fun j => localToAdelic3 p (κ⁻¹ * tA1 j * κ))
        (comb e₂ (fun j => localToAdelic3 p (κ⁻¹ * tA2 j * κ))
          (comb e₃ (fun j => localToAdelic3 p (κ⁻¹ * tB j * κ)) φ)) := by
    rw [comb_comb, comb_comb]
    congr 1
    funext jj
    rw [← MonoidHom.map_mul, ← MonoidHom.map_mul]
    congr 1
    exact word_conj_triple κ _ _ _
  rw [hflat]
  refine ⟨fun g w h k hkK hkN hg => ?_, fun g x y z hg => ?_, fun q' V' hq' hV'φ => ?_⟩
  ·
    have hkn₀ : IsLevel p ϖ n₀ k := hkN.mono p hϖ0 hϖ1 (Nat.le_add_left _ _)
    have hkV : k ∈ V := hN₁ k hkK (hkN.mono p hϖ0 hϖ1 (Nat.le_add_right _ _))
    simp only [hV, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hkV
    obtain ⟨⟨⟨hVA, hVB⟩, hVC⟩, hVD⟩ := hkV
    obtain ⟨hA1, hA2, hP1, hP2⟩ := surgery_coreA p hϖ0 hϖ1 hU1 κ habs y₁ y₂ y₃ e₁ e₂ e₃ hy₃' tA1 (fun _ => rfl)
      tA2 (fun _ => rfl) tB (fun _ => rfl) φ hφc haut hUφ g w h k hg hVA hVB hVC hVD
    by_cases hγ : ϖ ^ (n₀ + 1) * (h : M₂) 1 0 ∈ 𝒪ₚ
    swap
    · left; rw [hA1, hP1 hγ, mul_zero]
    by_cases hγL : (ϖ ^ (n₀ + 3))⁻¹ * (h : M₂) 1 0 ∈ 𝒪ₚ
    swap
    · left; rw [hA1, (hF₁ _ hγ).2 (by rwa [sub_zero]), zero_mul]
    rw [(hF₁ _ hγ).1 (by rwa [sub_zero]), one_mul] at hA1
    by_cases hδ : ϖ ^ (n₀ + 1) * (h : M₂) 1 1 ∈ 𝒪ₚ
    swap
    · left; rw [hA1, hA2, hP2 hδ, mul_zero]
    by_cases hδL : (ϖ ^ (n₀ + 2))⁻¹ * ((h : M₂) 1 1 - 1) ∈ 𝒪ₚ
    swap
    · left; rw [hA1, hA2, (hF₂ _ hδ).2 hδL, zero_mul]
    rw [(hF₂ _ hδ).1 hδL, one_mul] at hA2

    have hδ0 : (h : M₂) 1 1 ≠ 0 :=
      ne_zero_of_sub_one_lt p (valued_sub_one_lt_of_level p hϖ0 hϖ1 hδL)
    obtain ⟨b, c, hbc, hb, hc⟩ := exists_eq_upper_mul_lower h hδ0
    obtain ⟨hb10, hb11, hc', hcK, hcL, hcB⟩ := lower_factor_facts p hϖ0 hϖ1 n₀ h b c hb hc hγL hδL
    obtain ⟨hB1, hB2⟩ := surgery_coreB p hϖ0 hϖ1 hU1 hUmul κ habs y₃ e₃ tB (fun _ => rfl) φ hφc haut hUφ g w h b c hbc
      hb10 hb11 k hkK hkn₀ hg hcK hcL (fun j => hcB (y₃ j) (hy₃' j)) hVD
    by_cases ht : ϖ ^ (n₀ + 1) * (b : M₂) 0 0 ∈ 𝒪ₚ
    swap
    · left; rw [hA1, hA2, hB1, hB2 ht, mul_zero]
    by_cases htL : (ϖ ^ 1)⁻¹ * ((b : M₂) 0 0 - 1) ∈ 𝒪ₚ
    swap
    · left; rw [hA1, hA2, hB1, (hF₃ _ ht).2 htL, zero_mul]
    rw [(hF₃ _ ht).1 htL, one_mul] at hB1
    right
    refine ⟨by rw [hA1, hA2, hB1], ?_⟩

    have htv : Valued.v ((b : M₂) 0 0) = 1 :=
      valued_eq_one_of_sub_one_lt p (valued_sub_one_lt_of_level p hϖ0 hϖ1 (n := 0) (by simpa using htL))
    obtain ⟨x, y, z, k', hk', hcell⟩ := exists_upperUnipotent3_mul_of_unit p w b hb10 hb11 htv (iotaGL c) hcK
    exact ⟨x, y, z, k', hk', by rw [hbc, MonoidHom.map_mul, ← mul_assoc, hcell]⟩
  ·
    have hg' : componentAt3 (𝓞 ℚ) ℚ p g = radicalP21 ![z, y] * iotaGL (unipotentGL2 x) * 1 * κ := by
      rw [hg, mul_one, upperUnipotent3_eq_radicalP21_mul_iotaGL]
    have h1V := hV1
    simp only [hV, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at h1V
    obtain ⟨⟨⟨hVA, hVB⟩, hVC⟩, hVD⟩ := h1V
    obtain ⟨hA1, hA2, -, -⟩ := surgery_coreA p hϖ0 hϖ1 hU1 κ habs y₁ y₂ y₃ e₁ e₂ e₃ hy₃' tA1 (fun _ => rfl)
      tA2 (fun _ => rfl) tB (fun _ => rfl) φ hφc haut hUφ g ![z, y] (unipotentGL2 x) 1 hg' hVA hVB hVC hVD
    have hu10 : ((unipotentGL2 x : GL (Fin 2) (p.adicCompletion ℚ)) : M₂) 1 0 = 0 := rfl
    have hu11 : ((unipotentGL2 x : GL (Fin 2) (p.adicCompletion ℚ)) : M₂) 1 1 = 1 := rfl
    have hu00 : ((unipotentGL2 x : GL (Fin 2) (p.adicCompletion ℚ)) : M₂) 0 0 = 1 := rfl
    rw [hu10, (hF₁ _ h0reg).1 (by rw [sub_zero, mul_zero]; exact zero_mem _), one_mul] at hA1
    rw [hu11, (hF₂ _ h1reg).1 (by rw [sub_self, mul_zero]; exact zero_mem _), one_mul] at hA2
    have h1K : iotaGL (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ K₃ := by rw [MonoidHom.map_one]; exact Subgroup.one_mem _
    have h1L : IsLevel p ϖ n₀ (iotaGL (1 : GL (Fin 2) (p.adicCompletion ℚ))) := by
      rw [MonoidHom.map_one]; exact isLevel_one p ϖ _
    obtain ⟨hB1, -⟩ := surgery_coreB p hϖ0 hϖ1 hU1 hUmul κ habs y₃ e₃ tB (fun _ => rfl) φ hφc haut hUφ g ![z, y]
      (unipotentGL2 x) (unipotentGL2 x) 1 (mul_one _).symm hu10 hu11 1 (Subgroup.one_mem _) (isLevel_one p ϖ _) hg'
      h1K h1L
      (fun j => by rw [MonoidHom.map_one, mul_one, inv_mul_cancel]; exact ⟨Subgroup.one_mem _, isLevel_one p ϖ _⟩)
      hVD
    rw [hu00, (hF₃ _ h1reg).1 (by rw [sub_self, mul_zero]; exact zero_mem _), one_mul] at hB1
    rw [hA1, hA2, hB1]
  ·
    have key : ∀ {φ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (t' : G₃), FixedAt q' V' φ' →
        FixedAt q' V' fun x => φ' (x * localToAdelic3 p (κ⁻¹ * t' * κ)) := by
      intro φ' t' h
      have := fixedAt_translate q' h (localToAdelic3 p (κ⁻¹ * t' * κ))
      rw [componentAt3_localToAdelic3_of_ne p hq'] at this
      exact this.anti fun m hm => by simpa using hm
    refine fixedAt_comb q' _ _ fun _ => key _ ?_
    refine fixedAt_comb q' _ _ fun _ => key _ ?_
    exact fixedAt_comb q' _ _ fun _ => key _ hV'φ

end Surgery

section ShellCondition

private theorem upperUnipotent3_mul_upperUnipotent3' {A : Type*} [CommRing A] (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem upperUnipotent3_inv' {A : Type*} [CommRing A] (x y z : A) :
    (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [upperUnipotent3_mul_upperUnipotent3', show x + -x = (0 : A) by ring, show y + -y = (0 : A) by ring,
    show z + (x * y - z) + x * -y = (0 : A) by ring, upperUnipotent3_zero]

private theorem exists_upperUnipotent3_mul_iff {A : Type*} [CommRing A] (P : GL (Fin 3) A → Prop) (a b c : A)
    (h : GL (Fin 3) A) :
    (∃ (x y z : A) (k : GL (Fin 3) A), P k ∧ upperUnipotent3 a b c * h = upperUnipotent3 x y z * k) ↔
      ∃ (x y z : A) (k : GL (Fin 3) A), P k ∧ h = upperUnipotent3 x y z * k := by
  constructor
  · rintro ⟨x, y, z, k, hk, hh⟩
    refine ⟨-a + x, -b + y, a * b - c + z + -a * y, k, hk, ?_⟩
    calc h = (upperUnipotent3 a b c)⁻¹ * (upperUnipotent3 a b c * h) := (inv_mul_cancel_left _ _).symm
      _ = (upperUnipotent3 a b c)⁻¹ * (upperUnipotent3 x y z * k) := by rw [hh]
      _ = upperUnipotent3 (-a + x) (-b + y) (a * b - c + z + -a * y) * k := by
        rw [← mul_assoc, upperUnipotent3_inv', upperUnipotent3_mul_upperUnipotent3']
  · rintro ⟨x, y, z, k, hk, hh⟩
    exact ⟨a + x, b + y, c + z + a * y, k, hk, by rw [hh, ← mul_assoc, upperUnipotent3_mul_upperUnipotent3']⟩

private def InShellAt (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k

private theorem zerothShell_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    WhittakerBlock.zerothShell S = {q | ∀ p, p ∉ S → InShellAt p q.out} := rfl

private theorem inShellAt_upperUnipotent3_mul (p : HeightOneSpectrum (𝓞 ℚ)) (x y z : AdeleRing (𝓞 ℚ) ℚ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : InShellAt p (upperUnipotent3 x y z * g) ↔ InShellAt p g := by
  simp only [InShellAt, map_mul, componentAt3_upperUnipotent3]
  exact exists_upperUnipotent3_mul_iff (fun k => k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) _ _ _ _

private theorem inShellAt_out (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    InShellAt p (Quotient.mk'' g :
      MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)).out ↔ InShellAt p g := by
  have hrel := Quotient.mk_out' (s₁ := MulAction.orbitRel WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)) g
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨n, hn⟩ := hrel
  obtain ⟨x, y, z, hxyz⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff (n : AdelicGL 3 (𝓞 ℚ) ℚ)).1 n.2
  rw [← hn, Subgroup.smul_def, smul_eq_mul, hxyz]
  exact inShellAt_upperUnipotent3_mul p x y z g

private def shellAtPrimes (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Set (MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)) :=
  {q | ∀ p ∈ S, InShellAt p q.out}

private theorem shellAtPrimes_inter_zerothShell (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    shellAtPrimes S ∩ WhittakerBlock.zerothShell S = WhittakerBlock.zerothShell ∅ := by
  ext q
  simp only [shellAtPrimes, zerothShell_eq, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h₁, h₂⟩ p _
    by_cases hp : p ∈ S
    · exact h₁ p hp
    · exact h₂ p hp
  · intro h
    exact ⟨fun p _ => h p (by simp), fun p _ => h p (by simp)⟩

private theorem isOpen_setOf_inShellAt (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen {g : AdelicGL 3 (𝓞 ℚ) ℚ | InShellAt p g} := by
  have hset : {g : AdelicGL 3 (𝓞 ℚ) ℚ | InShellAt p g} = componentAt3 (𝓞 ℚ) ℚ p ⁻¹'
      ⋃ (x : p.adicCompletion ℚ) (y : p.adicCompletion ℚ) (z : p.adicCompletion ℚ),
        (upperUnipotent3 x y z * ·) '' (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))) := by
    ext g
    simp only [InShellAt, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨x, y, z, k, hk, hg⟩
      exact ⟨x, y, z, k, hk, hg.symm⟩
    · rintro ⟨x, y, z, k, hk, hg⟩
      exact ⟨x, y, z, k, hk, hg.symm⟩
  rw [hset]
  refine (continuous_componentAt3 p).isOpen_preimage _ ?_
  refine isOpen_iUnion fun x => isOpen_iUnion fun y => isOpen_iUnion fun z => ?_
  exact isOpenMap_mul_left (upperUnipotent3 x y z) _ (isOpen_localMaximalCompact3 p)

private theorem measurableSet_shellAtPrimes (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    @MeasurableSet _ (@Quotient.instMeasurableSpace _ _ (NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ))
      (shellAtPrimes S) := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  rw [measurableSet_quotient]
  have hpre : (Quotient.mk'' ⁻¹' shellAtPrimes S : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) =
      ⋂ p ∈ S, {g : AdelicGL 3 (𝓞 ℚ) ℚ | InShellAt p g} := by
    ext g
    simp only [shellAtPrimes, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iInter]
    exact forall_congr' fun p => forall_congr' fun _ => inShellAt_out p g
  rw [hpre]
  exact (isOpen_biInter_finset fun p _ => isOpen_setOf_inShellAt p).measurableSet

end ShellCondition

section MeasureSide

attribute [local instance] NumberField.AdelicHaar.glBorel

private theorem block_le_block_empty (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ₀ v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (Φ' Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ) (hΦ : ∀ x, ‖Φ' x‖ ≤ ‖Φ x‖)
    (hW : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Φ' (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) ≠ 0 →
      ‖whittaker3 pins ψ φ₀ g‖ ≤ ‖whittaker3 pins ψ v g‖)
    (hT : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, whittaker3 pins ψ φ₀ g ≠ 0 →
      Φ' (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) ≠ 0 →
      ∀ p ∈ S, ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
        k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k) :
    WhittakerBlock.block pins ψ φ₀ Φ' σ S ≤ WhittakerBlock.block pins ψ v Φ σ ∅ := by
  classical
  set T : Set (MulAction.orbitRel.Quotient ↥WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)) :=
    {q | ∀ p ∈ S, ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p q.out = upperUnipotent3 x y z * k} with hTdef
  have hTm : MeasurableSet T := measurableSet_shellAtPrimes S
  have hsub : T ∩ WhittakerBlock.zerothShell S ⊆ WhittakerBlock.zerothShell ∅ := by
    rintro q ⟨hqT, hqS⟩ p -
    by_cases hp : p ∈ S
    · exact hqT p hp
    · exact hqS p hp

  have hpt : ∀ q : MulAction.orbitRel.Quotient ↥WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ),
      (‖whittaker3 pins ψ φ₀ q.out‖₊ : ℝ≥0∞) ^ 2 *
          (‖Φ' fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det q.out) ^ σ) ≤
        T.indicator (fun q => (‖whittaker3 pins ψ v q.out‖₊ : ℝ≥0∞) ^ 2 *
          (‖Φ fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det q.out) ^ σ)) q := by
    intro q
    by_cases h0 : whittaker3 pins ψ φ₀ q.out = 0
    · simp [h0]
    by_cases h1 : Φ' (fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) = 0
    · simp [h1]
    have hq : q ∈ T := fun p hp => hT q.out h0 h1 p hp
    rw [Set.indicator_of_mem hq]
    have a1 : (‖whittaker3 pins ψ φ₀ q.out‖₊ : ℝ≥0∞) ≤ ‖whittaker3 pins ψ v q.out‖₊ :=
      ENNReal.coe_le_coe.mpr (hW q.out h1)
    have a2 : (‖Φ' fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) ≤
        ‖Φ fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ :=
      ENNReal.coe_le_coe.mpr (hΦ _)
    exact mul_le_mul' (mul_le_mul' (pow_le_pow_left' a1 2) a2) le_rfl
  unfold WhittakerBlock.block
  refine (lintegral_mono fun q => hpt q).trans ?_
  rw [lintegral_indicator hTm, Measure.restrict_restrict hTm]
  exact lintegral_mono_set hsub

end MeasureSide

section Assembly

open LanglandsTunnell

local notation "𝓟" => productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

private theorem exists_unif (p : HeightOneSpectrum (𝓞 ℚ)) : ∃ ϖ : p.adicCompletion ℚ, ϖ ≠ 0 ∧ Valued.v ϖ < 1 := by
  have hv := valued_natGenerator p
  refine ⟨((Rat.HeightOneSpectrum.natGenerator p : ℕ) : p.adicCompletion ℚ), fun h0 => ?_, ?_⟩
  · rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    decide

private theorem whittaker3_zero_fun (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : whittaker3 pins ψ (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g = 0 := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := pins.nS
  show (∫ x, ∫ y, ∫ z, (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (upperUnipotent3 x y z * g) * ψ (-(x + y))
    ∂pins.ν ∂pins.ν ∂pins.ν) = 0
  simp only [Pi.zero_apply, zero_mul, integral_zero]

private theorem whittaker3_out_ne_zero (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hW : whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ g₀ ≠ 0) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ
      (Quotient.mk'' g₀ :
        MulAction.orbitRel.Quotient ↥WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)).out ≠ 0 := by
  have h1 : @Setoid.r _ (MulAction.orbitRel ↥WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ))
      (Quotient.mk'' g₀ :
        MulAction.orbitRel.Quotient ↥WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)).out g₀ :=
    Quotient.eq''.1 (by rw [Quotient.out_eq'])
  obtain ⟨u, hu⟩ := MulAction.orbitRel_apply.1 h1
  intro h0
  apply hW
  have := (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul φ haut).2 u u.2 g₀
  rw [show (u : AdelicGL 3 (𝓞 ℚ) ℚ) * g₀ = _ from hu, h0, norm_zero] at this
  exact norm_eq_zero.1 this.symm

private theorem comb_reindex {J : Type} [Fintype J] {n : ℕ} (coef : J → ℂ) (τ : J → AdelicGL 3 (𝓞 ℚ) ℚ)
    (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    (fun x => ∑ i, coef ((Fintype.equivFin (J × Fin n)).symm i).1 * c ((Fintype.equivFin (J × Fin n)).symm i).2 *
        f (x * (τ ((Fintype.equivFin (J × Fin n)).symm i).1 * t ((Fintype.equivFin (J × Fin n)).symm i).2))) =
      comb coef τ (comb c t f) := by
  rw [comb_comb]
  funext x
  simp only [comb]
  exact (Fintype.equivFin (J × Fin n)).symm.sum_comp (fun jj => coef jj.1 * c jj.2 * f (x * (τ jj.1 * t jj.2)))

private theorem main
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (_hmg : IsModerateGrowth3 ℚ f)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
    (_hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g)
    (_hsa : WhittakerBlock.IsArchSmooth3 f)
    (_hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (_hzf : LanglandsTunnell.CubicInduction.WhittakerBlock.IsCentreFinite f)
    (_hf : f ≠ 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1 ∧
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t i) = 1) ∧
      (fun x => ∑ i, c i * f (x * t i)) ≠ 0 ∧
      ∃ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) ∧
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
          WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * f (x * t i)) Φ σ S ≤ C := by
  classical
  obtain ⟨n, c, t, ht, ⟨g₀, hg₀, hW₀⟩, Φ, ⟨Φc, hΦc, hΦst, hΦeq⟩, hΦreal, hΦmass, C, hC, hblock⟩ :=
    LanglandsTunnell.CubicInduction.exists_sum_translate_whittaker_ne_zero_and_whittakerBlock_empty_le_of_isCentreFinite S ω _hω
      lam1 lam2 f _hc _haut _hcen _hmg _hP21 _hP12 _hK _hT1 _hT2 _hsm _hsa _hKf _hzf _hf

  have hv : (fun x => ∑ i, c i * f (x * t i)) = comb c t f := rfl
  rw [hv] at hW₀ hblock
  have hvc : Continuous (comb c t f) := continuous_comb c t _hc
  have hva : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      comb c t f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = comb c t f g := comb_globalPointsGL_mul c t _haut

  choose Uf hUfo hUf using _hsm
  set V : (q : HeightOneSpectrum (𝓞 ℚ)) → Set (GL (Fin 3) (q.adicCompletion ℚ)) := fun q =>
    {m | ∀ i, (componentAt3 (𝓞 ℚ) ℚ q (t i))⁻¹ * m * componentAt3 (𝓞 ℚ) ℚ q (t i) ∈ (Uf q : Set (LocalGL3 q))}
    with hV
  have hVo : ∀ q, IsOpen (V q) := fun q => by
    simp only [hV, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => (hUfo q).preimage (continuous_mul_mul _ _)
  have hV1 : ∀ q, (1 : GL (Fin 3) (q.adicCompletion ℚ)) ∈ V q := fun q i => by
    simpa only [mul_one, inv_mul_cancel, SetLike.mem_coe] using (Uf q).one_mem
  have hVmul : ∀ q, ∀ a ∈ V q, ∀ b ∈ V q, a * b ∈ V q := fun q a ha b hb i => by
    rw [word_split]
    exact (Uf q).mul_mem (ha i) (hb i)
  have hvV : ∀ q, FixedAt q (V q) (comb c t f) := fun q =>
    fixedAt_comb q c t fun i =>
      (fixedAt_translate q (U := (Uf q : Set (LocalGL3 q))) (fun m hm x => hUf q m hm x) (t i)).anti
        fun m hm => hm i

  set g₁ : AdelicGL 3 (𝓞 ℚ) ℚ :=
    (Quotient.mk'' g₀ : MulAction.orbitRel.Quotient ↥WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)).out
    with hg₁
  have hsh : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p g₁ = upperUnipotent3 x y z * k :=
    fun p => hg₀ p (Finset.notMem_empty p)
  choose xs ys zs κ hκK hκ using hsh
  have hW₁ : whittaker3 𝓟 psiQ (comb c t f) g₁ ≠ 0 := whittaker3_out_ne_zero _ hva g₀ hW₀

  choose ϖ hϖ0 hϖ1 using exists_unif

  have main : ∀ S' : Finset (HeightOneSpectrum (𝓞 ℚ)), S' ⊆ S →
      ∃ (J : Type) (_ : Fintype J) (coef : J → ℂ) (τ : J → AdelicGL 3 (𝓞 ℚ) ℚ)
        (N : HeightOneSpectrum (𝓞 ℚ) → ℕ),
        (∀ j, archComponent3 (𝓞 ℚ) ℚ (τ j) = 1 ∧
          ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S' → componentAt3 (𝓞 ℚ) ℚ q (τ j) = 1) ∧
        (∀ q, q ∉ S' → FixedAt q (V q) (comb coef τ (comb c t f))) ∧
        whittaker3 𝓟 psiQ (comb coef τ (comb c t f)) g₁ = whittaker3 𝓟 psiQ (comb c t f) g₁ ∧
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p ∈ S', ∀ l : Fin 3, (ϖ p ^ N p)⁻¹ *
            (((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) :
                Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l -
              ((κ p : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l) ∈
            p.adicCompletionIntegers ℚ) →
          whittaker3 𝓟 psiQ (comb coef τ (comb c t f)) g = 0 ∨
          (whittaker3 𝓟 psiQ (comb coef τ (comb c t f)) g = whittaker3 𝓟 psiQ (comb c t f) g ∧
            ∀ p ∈ S', ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
              k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k) := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      intro _
      have h1 : comb (fun _ : PUnit => (1 : ℂ)) (fun _ => (1 : AdelicGL 3 (𝓞 ℚ) ℚ)) (comb c t f) = comb c t f := by
        funext x
        simp only [comb, Finset.univ_unique, Finset.sum_singleton, one_mul, mul_one]
      refine ⟨PUnit, inferInstance, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => ⟨map_one _, fun q _ => map_one _⟩,
        fun q _ => by rw [h1]; exact hvV q, by rw [h1], fun g _ => Or.inr ⟨by rw [h1], fun p hp => ?_⟩⟩
      exact absurd hp (Finset.notMem_empty p)
    | @insert p S' hpS' ih =>
      intro hsub
      obtain ⟨J, _, coef, τ, N, hτ, hlev, hg₁eq, hpt⟩ := ih ((Finset.subset_insert p S').trans hsub)
      set φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := comb coef τ (comb c t f) with hφ
      have hφc : Continuous φ := continuous_comb _ _ hvc
      have hφa : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g :=
        comb_globalPointsGL_mul coef τ hva
      obtain ⟨J', _, coef', t', N', hsur⟩ :=
        exists_surgery p (κ p) (hκK p) (V p) (hVo p) (hV1 p) (hVmul p) (hϖ0 p) (hϖ1 p)
      obtain ⟨hcl1, hcl2, hcl3⟩ := hsur φ hφc hφa (hlev p hpS')
      have hcc : comb coef' (fun j => localToAdelic3 p ((κ p)⁻¹ * t' j * κ p)) φ =
          comb (fun jj : J' × J => coef' jj.1 * coef jj.2)
            (fun jj => localToAdelic3 p ((κ p)⁻¹ * t' jj.1 * κ p) * τ jj.2) (comb c t f) := by
        rw [hφ, comb_comb]
      refine ⟨J' × J, inferInstance, fun jj => coef' jj.1 * coef jj.2,
        fun jj => localToAdelic3 p ((κ p)⁻¹ * t' jj.1 * κ p) * τ jj.2, fun q => if q = p then N' + 1 else N q,
        fun jj => ⟨?_, fun q hq => ?_⟩, fun q hq => ?_, ?_, fun g hg => ?_⟩
      · rw [map_mul, archComponent3_localToAdelic3, one_mul]
        exact (hτ jj.2).1
      · rw [Finset.mem_insert, not_or] at hq
        rw [map_mul, componentAt3_localToAdelic3_of_ne p hq.1, one_mul]
        exact (hτ jj.2).2 q hq.2
      · rw [Finset.mem_insert, not_or] at hq
        rw [← hcc]
        exact hcl3 q (V q) hq.1 (hlev q hq.2)
      · rw [← hcc, hcl2 g₁ (xs p) (ys p) (zs p) (hκ p), hg₁eq]
      · rw [← hcc]

        have hgp : ∀ l : Fin 3, (ϖ p ^ (N' + 1))⁻¹ *
            (((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) :
                Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l -
              ((κ p : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l) ∈
            p.adicCompletionIntegers ℚ := fun l => by
          simpa only [if_pos rfl, if_true] using hg p (Finset.mem_insert_self p S') l
        have hϖ'0 : ϖ p ^ (N' + 1) ≠ 0 := pow_ne_zero _ (hϖ0 p)
        have hϖ'1 : Valued.v (ϖ p ^ (N' + 1)) < 1 := by
          rw [map_pow]
          exact pow_lt_one₀ zero_le' (hϖ1 p) (Nat.succ_ne_zero _)
        have hrow := bottomRow_mul_inv_congr p (componentAt3 (𝓞 ℚ) ℚ p g) (κ p) (hκK p) hgp
        obtain ⟨w, h, k, hkK, hkN, hdec⟩ := exists_radicalP21_mul_iotaGL_mul_of_bottomRow p hϖ'0 hϖ'1
          (componentAt3 (𝓞 ℚ) ℚ p g * (κ p)⁻¹) (by simpa using hrow 0) (by simpa using hrow 1) (by simpa using hrow 2)
        have hkN' : IsLevel p (ϖ p) N' k := IsLevel.mono p (hϖ0 p) (hϖ1 p) (Nat.le_succ N') hkN
        have hgdec : componentAt3 (𝓞 ℚ) ℚ p g = radicalP21 w * iotaGL h * k * κ p := by
          rw [← hdec, inv_mul_cancel_right]
        rcases hcl1 g w h k hkK hkN' hgdec with h0 | ⟨heq, x, y, z, k', hk'K, hcell⟩
        · exact Or.inl h0
        have hg' : ∀ p' ∈ S', ∀ l : Fin 3, (ϖ p' ^ N p')⁻¹ *
            (((componentAt3 (𝓞 ℚ) ℚ p' g : GL (Fin 3) (p'.adicCompletion ℚ)) :
                Matrix (Fin 3) (Fin 3) (p'.adicCompletion ℚ)) 2 l -
              ((κ p' : GL (Fin 3) (p'.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p'.adicCompletion ℚ)) 2 l) ∈
            p'.adicCompletionIntegers ℚ := fun p' hp' l => by
          simpa only [if_neg (fun h => hpS' (h ▸ hp') : p' ≠ p)] using hg p' (Finset.mem_insert_of_mem hp') l
        rcases hpt g hg' with h0 | ⟨heq', hcells⟩
        · exact Or.inl (heq.trans h0)
        refine Or.inr ⟨heq.trans heq', fun p' hp' => ?_⟩
        rw [Finset.mem_insert] at hp'
        rcases hp' with rfl | hp'
        · exact ⟨x, y, z, k' * k * κ _, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk'K hkK) (hκK _),
            by rw [hgdec, hcell]; simp only [mul_assoc]⟩
        · exact hcells p' hp'
  obtain ⟨J, _, coef, τ, N, hτ, -, hg₁eq, hpt⟩ := main S (Finset.Subset.refl S)

  have hflat := comb_reindex coef τ c t f
  set e : Fin (Fintype.card (J × Fin n)) ≃ J × Fin n := (Fintype.equivFin (J × Fin n)).symm with he

  set A : Fin 3 → (p : HeightOneSpectrum (𝓞 ℚ)) → Set (p.adicCompletion ℚ) := fun i p =>
    bottomRowBall p (ϖ p ^ (N p + 1))
      (fun l => ((κ p : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l) i
    with hA
  have hAclopen : ∀ i p, IsClopen (A i p) := fun i p => isClopen_bottomRowBall p _ _ i
  have hAint : ∀ i p, A i p ⊆ (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := fun i p =>
    bottomRowBall_subset_integers p (pow_ne_zero _ (hϖ0 p))
      (by rw [map_pow]; exact pow_lt_one₀ zero_le' (hϖ1 p) (Nat.succ_ne_zero _))
      (fun l => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).2
        (((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ p).1 (hκK p)).1 2 l)) i
  have hAne : ∀ i p, (A i p).Nonempty := fun i p => ⟨_, centre_mem_bottomRowBall p _ _ i⟩
  obtain ⟨Φ', ⟨hΦ'shape, hΦ'real, hΦ'mass⟩, hΦ'box, hΦ'dom⟩ :=
    exists_testFunction_box S A hAclopen hAint hAne Φ Φc hΦc hΦst hΦeq hΦreal hΦmass

  have hregion : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Φ' (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) ≠ 0 →
      ∀ p ∈ S, ∀ l : Fin 3, (ϖ p ^ N p)⁻¹ *
        (((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) :
            Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l -
          ((κ p : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l) ∈
        p.adicCompletionIntegers ℚ := by
    intro g hg p hp l
    have hbox : (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) ∈ integralBox S A := by
      by_contra hx
      exact hg (by rw [hΦ'box, Set.indicator_of_notMem hx, mul_zero])
    have h1 : (ϖ p ^ (N p + 1))⁻¹ *
        (((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) :
            Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l -
          ((κ p : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l) ∈
        p.adicCompletionIntegers ℚ := (mem_integralBox_iff S A _).1 hbox l p hp
    exact level_mono p (hϖ0 p) (hϖ1 p) (Nat.le_succ _) h1
  refine ⟨Fintype.card (J × Fin n), fun i => coef (e i).1 * c (e i).2, fun i => τ (e i).1 * t (e i).2,
    fun i => ⟨?_, fun p hp => ?_⟩, fun h0 => hW₁ ?_, Φ', hΦ'shape, hΦ'real, hΦ'mass, C, hC, fun σ hσ => ?_⟩
  · beta_reduce
    rw [map_mul, (hτ _).1, (ht _).1, one_mul]
  · beta_reduce
    rw [map_mul, (hτ _).2 p hp, (ht _).2 p hp, one_mul]
  · beta_reduce at h0
    rw [← hg₁eq, hflat.symm.trans h0]
    exact whittaker3_zero_fun _ _ _
  · beta_reduce
    rw [hflat]
    refine (block_le_block_empty 𝓟 psiQ S _ (comb c t f) Φ' Φ σ (fun x => ?_) (fun g hg => ?_)
      (fun g hW hg p hp => ?_)).trans (hblock σ hσ)
    · obtain ⟨h1, h2⟩ := hΦ'dom x
      have e1 : Φ' x = ((Φ' x).re : ℂ) := Complex.ext (by simp) (by simp [(hΦ'real x).2])
      have e2 : Φ x = ((Φ x).re : ℂ) := Complex.ext (by simp) (by simp [(hΦreal x).2])
      rw [e1, e2, Complex.norm_of_nonneg h1, Complex.norm_of_nonneg (hΦreal x).1]
      exact h2
    · rcases hpt g (hregion g hg) with h0 | ⟨heq, -⟩
      · rw [h0, norm_zero]; exact norm_nonneg _
      · rw [heq]
    · rcases hpt g (hregion g hg) with h0 | ⟨-, hcells⟩
      · exact absurd h0 hW
      · exact hcells p hp

end Assembly

end WhittakerBlockTransfer

open LanglandsTunnell LanglandsTunnell.CubicInduction in

theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (_hmg : IsModerateGrowth3 ℚ f)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
    (_hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g)
    (_hsa : WhittakerBlock.IsArchSmooth3 f)
    (_hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (_hzf : LanglandsTunnell.CubicInduction.WhittakerBlock.IsCentreFinite f)
    (_hf : f ≠ 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1 ∧
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t i) = 1) ∧
      (fun x => ∑ i, c i * f (x * t i)) ≠ 0 ∧
      ∃ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) ∧
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
          WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * f (x * t i)) Φ σ S ≤ C :=
  WhittakerBlockTransfer.main S ω _hω lam1 lam2 f _hc _haut _hcen _hmg _hP21 _hP12 _hK _hT1 _hT2 _hsm _hsa _hKf _hzf _hf

end
end S_LanglandsTunnell_CubicInduction_exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite (solution)
