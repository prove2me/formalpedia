-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b1f55e1c-7334-5514-a801-ada552d02516

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~isProbabilityMeasure_productionPins_ν"
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

namespace ArchPkgTop

noncomputable abbrev W (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
    NumberField.StandardAddChar.psiQ u g

noncomputable abbrev L (y₁ y₂ : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)

noncomputable abbrev word (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (w : List (Fin 3 × Fin 3)) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w

section WhittakerLinearity

open MeasureTheory

private theorem continuous_upperUnipotent3 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun p : A × A × A => upperUnipotent3 p.1 p.2.1 p.2.2 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun p : A × A × A =>
      (Matrix.of ![![1, p.1, p.2.2], ![0, 1, p.2.1], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun p : A × A × A =>
      (Matrix.of ![![1, -p.1, p.1 * p.2.1 - p.2.2], ![0, 1, -p.2.1], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem isProbabilityMeasure_productionPins_ν :
    @IsProbabilityMeasure _ (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ _ _ _ _ (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
    (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

private theorem borelSpace_productionPins_nS :
    @BorelSpace (AdeleRing (𝓞 ℚ) ℚ) _
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS := by
  rw [productionPinsOf_nS]
  exact AdelicHaar.borelSpace_adeleBorel _ _

private theorem ae_mem_adelicBox_productionPins_ν :
    ∀ᵐ a ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν,
      a ∈ AdelicBox.adelicBox ℚ := by
  rw [productionPinsOf_ν]
  unfold ProbabilityTheory.cond
  exact MeasureTheory.Measure.ae_smul_measure (ae_restrict_mem (AdelicBox.measurableSet_adelicBox ℚ)) _

private theorem continuous_integral_of_continuous {β : Type*} [TopologicalSpace β] {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α)
    (hC : IsCompact C) (hae : ∀ᵐ a ∂μ, a ∈ C) (H : β → α → ℂ) (hH : Continuous fun q : β × α => H q.1 q.2) :
    Continuous fun b => ∫ a, H b a ∂μ := by
  have hslice : ∀ b : β, Continuous fun a => H b a := fun b => hH.comp (Continuous.prodMk_right b)
  have hint : ∀ b : β, Integrable (fun a => H b a) μ := by
    intro b
    obtain ⟨Mb, hMb⟩ := hC.exists_bound_of_continuousOn (hslice b).continuousOn
    exact Integrable.of_bound (hslice b).aestronglyMeasurable Mb (hae.mono fun a ha => hMb a ha)
  refine continuous_iff_continuousAt.mpr fun b₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hH₀ : Continuous fun q : β × α => H b₀ q.2 :=
    hH.comp ((continuous_const : Continuous fun _ : β × α => b₀).prodMk continuous_snd)
  have hdist : Continuous fun q : β × α => ‖H q.1 q.2 - H b₀ q.2‖ := (hH.sub hH₀).norm
  have htube : ∀ᶠ b in nhds b₀, ∀ a ∈ C, ‖H b a - H b₀ a‖ < ε / 2 := by
    refine hC.eventually_forall_of_forall_eventually fun a _ => ?_
    refine hdist.continuousAt.eventually_lt continuous_const.continuousAt ?_
    show ‖H b₀ a - H b₀ a‖ < ε / 2
    rw [sub_self, norm_zero]
    exact half_pos hε
  refine htube.mono fun b hb => ?_
  rw [dist_eq_norm, ← integral_sub (hint b) (hint b₀)]
  have hbound : ∀ᵐ a ∂μ, ‖H b a - H b₀ a‖ ≤ ε / 2 := hae.mono fun a ha => (hb a ha).le
  calc ‖∫ a, H b a - H b₀ a ∂μ‖ ≤ ε / 2 * μ.real Set.univ := norm_integral_le_of_norm_le_const hbound
    _ = ε / 2 := by simp
    _ < ε := half_lt_self hε

private theorem integrable_of_continuous_of_ae_mem_compact {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α) (hC : IsCompact C)
    (hae : ∀ᵐ a ∂μ, a ∈ C) (K : α → ℂ) (hK : Continuous K) : Integrable K μ := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hK.continuousOn
  exact Integrable.of_bound hK.aestronglyMeasurable M (hae.mono fun a ha => hM a ha)

private theorem integral3_sum_of_continuous {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α) (hC : IsCompact C)
    (hae : ∀ᵐ a ∂μ, a ∈ C) {ι : Type*} [Fintype ι] (c : ι → ℂ) (G : ι → α → α → α → ℂ)
    (hG : ∀ i, Continuous fun p : α × α × α => G i p.1 p.2.1 p.2.2) :
    (∫ x, ∫ y, ∫ z, ∑ i, c i * G i x y z ∂μ ∂μ ∂μ) = ∑ i, c i * ∫ x, ∫ y, ∫ z, G i x y z ∂μ ∂μ ∂μ := by
  have key : ∀ K : ι → α → ℂ, (∀ i, Continuous (K i)) →
      (∫ a, ∑ i, c i * K i a ∂μ) = ∑ i, c i * ∫ a, K i a ∂μ := by
    intro K hK
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
    · intro i _
      exact (integrable_of_continuous_of_ae_mem_compact μ C hC hae (K i) (hK i)).const_mul (c i)
  have hz : ∀ i x y, Continuous fun z => G i x y z := fun i x y =>
    (hG i).comp ((Continuous.prodMk_right x).comp (Continuous.prodMk_right y))
  have hI : ∀ i, Continuous fun p : α × α => ∫ z, G i p.1 p.2 z ∂μ := fun i =>
    continuous_integral_of_continuous μ C hC hae (fun (p : α × α) z => G i p.1 p.2 z)
      ((hG i).comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)))
  have hJ : ∀ i, Continuous fun x => ∫ y, ∫ z, G i x y z ∂μ ∂μ := fun i =>
    continuous_integral_of_continuous μ C hC hae (fun x y => ∫ z, G i x y z ∂μ) (hI i)
  have h1 : ∀ x y, (∫ z, ∑ i, c i * G i x y z ∂μ) = ∑ i, c i * ∫ z, G i x y z ∂μ := fun x y =>
    key (fun i z => G i x y z) fun i => hz i x y
  have h2 : ∀ x, (∫ y, ∑ i, c i * ∫ z, G i x y z ∂μ ∂μ) = ∑ i, c i * ∫ y, ∫ z, G i x y z ∂μ ∂μ := fun x =>
    key (fun i y => ∫ z, G i x y z ∂μ) fun i => (hI i).comp (Continuous.prodMk_right x)
  simp_rw [h1, h2]
  exact key (fun i x => ∫ y, ∫ z, G i x y z ∂μ ∂μ) hJ

private theorem whittaker3_sum_mul_of_continuous {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : ∀ i, Continuous (F i)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * F i x) g =
      ∑ i, c i *
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (F i) g := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) :=
    (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
  haveI := borelSpace_productionPins_nS
  haveI := isProbabilityMeasure_productionPins_ν
  obtain ⟨C, hC, hBC⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hae : ∀ᵐ a ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν, a ∈ C :=
    ae_mem_adelicBox_productionPins_ν.mono fun a ha => hBC ha
  have hG : ∀ i, Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      F i (upperUnipotent3 p.1 p.2.1 p.2.2 * g) * NumberField.StandardAddChar.psiQ (-(p.1 + p.2.1)) := fun i =>
    ((hF i).comp ((continuous_upperUnipotent3 (A := AdeleRing (𝓞 ℚ) ℚ)).mul continuous_const)).mul
      (NumberField.StandardAddChar.continuous_psiQ.comp ((continuous_fst.add continuous_snd.fst).neg))
  unfold whittaker3
  simp_rw [Finset.sum_mul, mul_assoc]
  exact integral3_sum_of_continuous _ C hC hae c
    (fun i x y z => F i (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y))) hG

end WhittakerLinearity

private theorem whittaker3_mul_right (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (k g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (fun x => φ (x * k)) g =
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ (g * k) := by
  unfold whittaker3
  simp_rw [mul_assoc]

private theorem isArchSmooth3_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) {n : ℕ} (c : Fin n → ℂ)
    (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (hsm : ∀ i, WhittakerBlock.IsArchSmooth3 fun x => f (x * t i)) :
    WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) := by
  intro g
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul (hsm i g)

theorem W_sum_mul_translate {ι : Type*} [Fintype ι] (a : ι → ℂ) (φ : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : ∀ i, Continuous (φ i)) (k g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    W (fun x => ∑ i, a i * φ i (x * k)) g = ∑ i, a i * W (φ i) (g * k) := by
  show whittaker3 _ _ (fun x => ∑ i, a i * (fun y => φ i (y * k)) x) g = _
  rw [whittaker3_sum_mul_of_continuous a (fun i y => φ i (y * k)) (fun i => (hφ i).comp (continuous_mul_right k)) g]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [whittaker3_mul_right]

theorem W_add (u₁ u₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h₁ : Continuous u₁) (h₂ : Continuous u₂)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : W (u₁ + u₂) g = W u₁ g + W u₂ g := by
  have hfun : (u₁ + u₂) = fun x => ∑ i : Fin 2, (1 : ℂ) * (![u₁, u₂] i) x := by
    funext x; simp [Fin.sum_univ_two]
  have hc : ∀ i : Fin 2, Continuous (![u₁, u₂] i) := by
    intro i; fin_cases i
    · simpa using h₁
    · simpa using h₂
  show whittaker3 _ _ (u₁ + u₂) g = _
  rw [hfun, whittaker3_sum_mul_of_continuous (fun _ : Fin 2 => (1 : ℂ)) ![u₁, u₂] hc g]
  simp [Fin.sum_univ_two]

theorem W_smul (a : ℂ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : Continuous u) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    W (a • u) g = a * W u g := by
  have hfun : (a • u) = fun x => ∑ i : Fin 1, a * (fun _ : Fin 1 => u) i x := by
    funext x; simp
  show whittaker3 _ _ (a • u) g = _
  rw [hfun, whittaker3_sum_mul_of_continuous (fun _ : Fin 1 => a) (fun _ => u) (fun _ => hu) g]
  simp

theorem W_zero (g : AdelicGL 3 (𝓞 ℚ) ℚ) : W (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g = 0 := by
  have hfun : (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = fun x => ∑ i : Fin 0, (0 : ℂ) * (fun (_ : Fin 0) (_ : AdelicGL 3 (𝓞 ℚ) ℚ) => (0 : ℂ)) i x := by
    funext x; simp
  show whittaker3 _ _ (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g = _
  rw [hfun, whittaker3_sum_mul_of_continuous (fun _ : Fin 0 => (0 : ℂ)) (fun _ _ => (0 : ℂ)) (fun _ => continuous_const) g]
  simp

theorem span_ray (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsaF : WhittakerBlock.IsArchSmooth3 F)
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hcontw : ∀ w : List (Fin 3 × Fin 3), Continuous (word (fun x => ∑ i, c i * F (x * t i)) w))
    (θ θ₀ : ℝ) (hθ : θ ≤ θ₀)
    (hray : ∀ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ), ∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ,
      ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 → ‖W (word (fun x => ∑ i, c i * F (x * t i)) w) (L y₁ y₂ * h)‖ ≤ C * y₁ ^ θ₀)
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun g => ∑ i, c i * F (g * h * t i)) w})
    (h₀ : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous u ∧ ∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
      ‖W u (L y₁ y₂ * h₀)‖ ≤ C * y₁ ^ θ := by
  induction hu using Submodule.span_induction generalizing h₀ with
  | mem φ hφ =>
    obtain ⟨w, h, rfl⟩ := hφ

    obtain ⟨coeff, -, hexp⟩ := exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum w
    have hsaV : WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * F (x * t i)) :=
      isArchSmooth3_sum_translate F c t fun i => isArchSmooth3_mul_right F hsaF (t i)
    have hfun : (fun g => ∑ i, c i * F (g * h * t i)) = (fun x => (fun y => ∑ i, c i * F (y * t i)) (x * h)) := rfl
    have hrew : List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun g => ∑ i, c i * F (g * h * t i)) w =
        fun g => ∑ f : Fin w.length → Fin 3 × Fin 3,
          coeff h f * word (fun x => ∑ i, c i * F (x * t i)) (List.ofFn f) (g * h) := by
      funext g; rw [hfun]; exact hexp _ hsaV h g
    refine ⟨?_, ?_⟩
    · rw [hrew]
      exact continuous_finset_sum _ fun f _ =>
        (continuous_const.mul ((hcontw (List.ofFn f)).comp (continuous_mul_right h)))
    · intro y₂ hy₂
      choose Cf hCf using fun f : Fin w.length → Fin 3 × Fin 3 => hray (List.ofFn f) (h₀ * h) y₂ hy₂
      refine ⟨∑ f, ‖coeff h f‖ * |Cf f|, fun y₁ hy₁ hy₁' => ?_⟩
      rw [hrew, W_sum_mul_translate (fun f => coeff h f) (fun f => word (fun x => ∑ i, c i * F (x * t i)) (List.ofFn f))
        (fun f => hcontw _) h (L y₁ y₂ * h₀)]
      calc ‖∑ f, coeff h f * W (word (fun x => ∑ i, c i * F (x * t i)) (List.ofFn f)) (L y₁ y₂ * h₀ * h)‖
          ≤ ∑ f, ‖coeff h f * W (word (fun x => ∑ i, c i * F (x * t i)) (List.ofFn f)) (L y₁ y₂ * h₀ * h)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ f, ‖coeff h f‖ * |Cf f| * y₁ ^ θ := by
            refine Finset.sum_le_sum fun f _ => ?_
            rw [norm_mul, mul_assoc ‖coeff h f‖]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (coeff h f))
            have h1 := hCf f y₁ hy₁ hy₁'
            rw [← mul_assoc] at h1
            calc ‖W (word (fun x => ∑ i, c i * F (x * t i)) (List.ofFn f)) (L y₁ y₂ * h₀ * h)‖
                ≤ Cf f * y₁ ^ θ₀ := h1
              _ ≤ |Cf f| * y₁ ^ θ₀ := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hy₁.le _)
              _ ≤ |Cf f| * y₁ ^ θ := mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow_of_exponent_ge hy₁ hy₁' hθ) (abs_nonneg _)
        _ = (∑ f, ‖coeff h f‖ * |Cf f|) * y₁ ^ θ := by rw [Finset.sum_mul]
  | zero =>
    refine ⟨continuous_const, fun y₂ hy₂ => ⟨0, fun y₁ hy₁ _ => ?_⟩⟩
    rw [W_zero, norm_zero, zero_mul]
  | add u₁ u₂ _ _ ih₁ ih₂ =>
    refine ⟨(ih₁ h₀).1.add (ih₂ h₀).1, fun y₂ hy₂ => ?_⟩
    obtain ⟨C₁, hC₁⟩ := (ih₁ h₀).2 y₂ hy₂
    obtain ⟨C₂, hC₂⟩ := (ih₂ h₀).2 y₂ hy₂
    refine ⟨C₁ + C₂, fun y₁ hy₁ hy₁' => ?_⟩
    rw [W_add u₁ u₂ (ih₁ h₀).1 (ih₂ h₀).1, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC₁ y₁ hy₁ hy₁') (hC₂ y₁ hy₁ hy₁'))
  | smul a u _ ih =>
    refine ⟨(ih h₀).1.const_smul a, fun y₂ hy₂ => ?_⟩
    obtain ⟨C, hC⟩ := (ih h₀).2 y₂ hy₂
    refine ⟨‖a‖ * C, fun y₁ hy₁ hy₁' => ?_⟩
    rw [W_smul a u (ih h₀).1, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC y₁ hy₁ hy₁') (norm_nonneg _)

end ArchPkgTop

open ArchPkgTop in

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hmg : IsModerateGrowth3 ℚ f)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i)) :
    ∃ θ₀ : ℝ, 1 / 2 < θ₀ ∧ ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (g * h * t i)) w} →
      (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
      (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀) := by

  have hz0 := hz
  obtain ⟨-, ⟨N₂, a₂, ha₂, hr₂⟩, ⟨N₃, a₃, ha₃, hr₃⟩⟩ := hz0
  obtain ⟨θ₁, hθ₁, H₁⟩ :=
    exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant ω hω N₂ a₂ ha₂ N₃ a₃ ha₃

  obtain ⟨hc', haut', hcen', hω', hmg', hP21', hP12', hK', hsm', hsa', hKf', ht', hz', Htr⟩ :=
    rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant ω hω f hc haut hcen hmg hP21 hP12 S hK hsm hsa hKf n c t ht hz
  have hz'0 := hz'
  obtain ⟨-, ⟨N₂', a₂', ha₂', hr₂'⟩, ⟨N₃', a₃', ha₃', hr₃'⟩⟩ := hz'0
  obtain ⟨θ₂, hθ₂, H₂⟩ :=
    exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant ω⁻¹ hω' N₂' a₂' ha₂' N₃' a₃' ha₃'
  refine ⟨min θ₁ θ₂, lt_min hθ₁ hθ₂, fun u hu => ⟨?_, ?_⟩⟩
  ·
    have hcw := (continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite f hc hmg hsa hKf n c t ht
      hz).1
    have H₁' := H₁ f hc haut hcen hmg hP21 hP12 S hK hsm hsa hKf n c t ht hz hr₂ hr₃
    intro y₂ hy₂
    obtain ⟨C, hC⟩ := (span_ray f hsa c t hcw (min θ₁ θ₂) θ₁ (min_le_left _ _) H₁' u hu 1).2 y₂ hy₂
    refine ⟨C, fun y₁ hy₁ hy₁' => ?_⟩
    have := hC y₁ hy₁ hy₁'
    rwa [mul_one] at this
  ·
    obtain ⟨h', Hh'⟩ := Htr 1
    obtain ⟨hu', hWeq⟩ := Hh' u hu
    have hcw' := (continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
      (fun g => f (transposeInv3 g)) hc' hmg' hsa' hKf' n c (fun i => transposeInv3 (t i)) ht' hz').1
    have H₂' := H₂ (fun g => f (transposeInv3 g)) hc' haut' hcen' hmg' hP21' hP12' S hK' hsm' hsa' hKf' n c
      (fun i => transposeInv3 (t i)) ht' hz' hr₂' hr₃'
    intro y₁ hy₁
    obtain ⟨C, hC⟩ := (span_ray (fun g => f (transposeInv3 g)) hsa' c (fun i => transposeInv3 (t i)) hcw'
      (min θ₁ θ₂) θ₂ (min_le_right _ _) H₂' (fun g => u (transposeInv3 g)) hu' h').2 y₁ hy₁
    refine ⟨C, fun y₂ hy₂ hy₂' => ?_⟩
    have h1 := hWeq y₁ y₂ hy₁ hy₂
    rw [mul_one] at h1
    rw [h1]
    exact hC y₂ hy₂ hy₂'

end S_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant (solution)
