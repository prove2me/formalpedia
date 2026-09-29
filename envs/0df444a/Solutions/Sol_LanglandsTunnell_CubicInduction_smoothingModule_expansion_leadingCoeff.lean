-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.smoothingModule_expansion_leadingCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e7525017-aa29-5142-a663-a76bc7d1fe50

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel
import Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_seed_package_of_mem_span_archDeriv_translate
import Theorems.Thm_LanglandsTunnell_CubicInduction_smoothingModule_regularity_and_growth
import Theorems.Thm_LanglandsTunnell_CubicInduction_smoothingModule_orthFinite_and_archDeriv_mem
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_expansion_leadingCoeff
p2m_attr_erase "instance" "instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~isProbabilityMeasure_productionPins_ν MeasureTheory"
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)
open Matrix

noncomputable section

namespace MemExp48

section WhittakerLinearity

open MeasureTheory

theorem continuous_upperUnipotent3 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
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

theorem isProbabilityMeasure_productionPins_ν :
    @IsProbabilityMeasure _ (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ _ _ _ _ (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
    (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

theorem borelSpace_productionPins_nS :
    @BorelSpace (AdeleRing (𝓞 ℚ) ℚ) _
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS := by
  rw [productionPinsOf_nS]
  exact AdelicHaar.borelSpace_adeleBorel _ _

theorem ae_mem_adelicBox_productionPins_ν :
    ∀ᵐ a ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν,
      a ∈ AdelicBox.adelicBox ℚ := by
  rw [productionPinsOf_ν]
  unfold ProbabilityTheory.cond
  exact MeasureTheory.Measure.ae_smul_measure (ae_restrict_mem (AdelicBox.measurableSet_adelicBox ℚ)) _

theorem continuous_integral_of_continuous {β : Type*} [TopologicalSpace β] {α : Type*} [MeasurableSpace α]
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

theorem integrable_of_continuous_of_ae_mem_compact {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α) (hC : IsCompact C)
    (hae : ∀ᵐ a ∂μ, a ∈ C) (K : α → ℂ) (hK : Continuous K) : Integrable K μ := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hK.continuousOn
  exact Integrable.of_bound hK.aestronglyMeasurable M (hae.mono fun a ha => hM a ha)

theorem integral3_sum_of_continuous {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
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

theorem whittaker3_sum_mul_of_continuous {ι : Type*} [Fintype ι] (c : ι → ℂ)
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

attribute [local instance] NumberField.AdelicHaar.glBorel

scoped instance borelSpace_G48 : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.glBorel

def LeftOrthFinite (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
      (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))

def kernels : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := {φ | IsSmoothingKernel φ ∧ LeftOrthFinite φ}

def modl (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
  Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' kernels)

def HasExpansion (m J : ℕ) (e : Fin m → ℂ) (τ : ℝ) (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ

open scoped Classical in

def coeffA (m J : ℕ) (e : Fin m → ℂ) (τ : ℝ) (i₀ : Fin m) (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, HasExpansion m J e τ w b then
    (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
  else 0

theorem coeff_eq_of_hasExpansion (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e) (τ : ℝ)
    (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (b₁ b₂ : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (h₁ : HasExpansion m J e τ w b₁) (h₂ : HasExpansion m J e τ w b₂)
    (i : Fin m) (hi : (e i).re < τ) (j : Fin J) (y₂ : ℝ) (hy₂ : 0 < y₂) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    b₁ i j y₂ k = b₂ i j y₂ k := by
  classical

  set bd : ℝ := max y₂ y₂⁻¹ with hbd
  have hbd1 : 1 ≤ bd := by
    rcases le_or_gt 1 y₂ with h | h
    · exact h.trans (le_max_left _ _)
    · exact (one_le_inv₀ hy₂ |>.mpr h.le).trans (le_max_right _ _)
  have hlo : bd⁻¹ ≤ y₂ := by
    rw [hbd]; calc (max y₂ y₂⁻¹)⁻¹ ≤ (y₂⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hy₂) (le_max_right _ _)
      _ = y₂ := inv_inv y₂
  have hhi : y₂ ≤ bd := le_max_left _ _
  obtain ⟨C₁, hC₁⟩ := h₁.2 {k} isCompact_singleton bd hbd1
  obtain ⟨C₂, hC₂⟩ := h₂.2 {k} isCompact_singleton bd hbd1

  have key := LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
    (ι := Fin m × Fin J) (fun p => e p.1) (fun p => (p.2 : ℕ)) (fun p => b₂ p.1 p.2 y₂ k - b₁ p.1 p.2 y₂ k)
    (fun p q hpq => by
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext (he hpq.1) (Fin.ext hpq.2))
    τ (fun y => ∑ p : Fin m × Fin J, (b₂ p.1 p.2 y₂ k - b₁ p.1 p.2 y₂ k) * ((y : ℂ) ^ e p.1 * (Real.log y : ℂ) ^ (p.2 : ℕ)))
    (fun _ => 0) (fun y _ _ => by simp) ⟨0, fun y _ _ => by simp⟩
    ⟨C₁ + C₂, fun y₁ hy₁ hy₁' => by
      have e₁ := hC₁ k (Set.mem_singleton k) y₂ hlo hhi y₁ hy₁ hy₁'
      have e₂ := hC₂ k (Set.mem_singleton k) y₂ hlo hhi y₁ hy₁ hy₁'
      have hsplit : (∑ p : Fin m × Fin J, (b₂ p.1 p.2 y₂ k - b₁ p.1 p.2 y₂ k) *
            ((y₁ : ℂ) ^ e p.1 * (Real.log y₁ : ℂ) ^ (p.2 : ℕ))) =
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ w (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            ∑ i : Fin m, ∑ j : Fin J, b₁ i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))) -
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ w (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            ∑ i : Fin m, ∑ j : Fin J, b₂ i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))) := by
        rw [Fintype.sum_prod_type]
        simp only [sub_mul, Finset.sum_sub_distrib]
        ring
      beta_reduce
      rw [hsplit]
      calc _ ≤ C₁ * y₁ ^ τ + C₂ * y₁ ^ τ := (norm_sub_le _ _).trans (add_le_add e₁ e₂)
        _ = (C₁ + C₂) * y₁ ^ τ := by ring⟩
    (i, j) hi
  exact (sub_eq_zero.mp key).symm

theorem coeffA_eq_of_hasExpansion (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e) (τ : ℝ) (hτ : 1 / 2 < τ)
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2) (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hb : HasExpansion m J e τ w b) (j : Fin J) (hj : (j : ℕ) = 0) (y₂ : ℝ) (hy₂ : 0 < y₂) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    coeffA m J e τ i₀ w y₂ k = b i₀ j y₂ k := by
  classical
  have hJ : 0 < J := Fin.pos j
  have hex : ∃ b' : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, HasExpansion m J e τ w b' := ⟨b, hb⟩
  have hj' : (⟨0, hJ⟩ : Fin J) = j := Fin.ext (by simp [hj])
  unfold coeffA
  rw [dif_pos ⟨hy₂, hJ, hex⟩, hj']
  exact coeff_eq_of_hasExpansion m J e he τ w _ b (Classical.choose_spec hex) hb i₀ (by rw [hD]; exact hτ) j y₂ hy₂ k

def formB (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (w w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : ℂ :=
  ∫ g, w g * (starRingEnd ℂ) (w' g) ∂(domainMeasure 1 2 Φ₀)

theorem whittaker3_smul_add_of_continuous (z : ℂ) (w₁ w₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h₁ : Continuous w₁) (h₂ : Continuous w₂)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ (z • w₁ + w₂) g = z * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ w₁ g + whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ w₂ g := by
  have key := whittaker3_sum_mul_of_continuous (ι := Fin 2) ![z, 1] ![w₁, w₂]
    (by intro i; fin_cases i <;> simpa) g
  have hfun : (z • w₁ + w₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = fun x => ∑ i : Fin 2, (![z, 1] : Fin 2 → ℂ) i * (![w₁, w₂] : Fin 2 → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) i x := by
    funext x
    simp [Fin.sum_univ_two]
  rw [hfun, key]
  simp [Fin.sum_univ_two]

theorem hasExpansion_zero (m J : ℕ) (e : Fin m → ℂ) (τ : ℝ) :
    HasExpansion m J e τ (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (fun _ _ _ _ => 0) := by
  refine ⟨fun i j => continuousOn_const, fun K _ bd _ => ⟨0, fun k _ y₂ _ _ y₁ _ _ => ?_⟩⟩
  simp [whittaker3]

theorem hasExpansion_smul_add (m J : ℕ) (e : Fin m → ℂ) (τ : ℝ) (z : ℂ) {w₁ w₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) {b₁ b₂ : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (h₁ : HasExpansion m J e τ w₁ b₁) (h₂ : HasExpansion m J e τ w₂ b₂) :
    HasExpansion m J e τ (z • w₁ + w₂) (fun i j y₂ k => z * b₁ i j y₂ k + b₂ i j y₂ k) := by
  refine ⟨fun i j => (continuousOn_const.mul (h₁.1 i j)).add (h₂.1 i j), fun K hK bd hbd => ?_⟩
  obtain ⟨C₁, hC₁⟩ := h₁.2 K hK bd hbd
  obtain ⟨C₂, hC₂⟩ := h₂.2 K hK bd hbd
  refine ⟨‖z‖ * C₁ + C₂, fun k hk y₂ hlo hhi y₁ hy hy' => ?_⟩
  have e₁ := hC₁ k hk y₂ hlo hhi y₁ hy hy'
  have e₂ := hC₂ k hk y₂ hlo hhi y₁ hy hy'
  rw [whittaker3_smul_add_of_continuous z w₁ w₂ hw₁ hw₂]
  have hsplit : z * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ w₁ (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) +
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ w₂ (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
        ∑ i : Fin m, ∑ j : Fin J, (z * b₁ i j y₂ k + b₂ i j y₂ k) * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)) =
      z * (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ w₁ (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
        ∑ i : Fin m, ∑ j : Fin J, b₁ i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))) +
      (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ w₂ (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
        ∑ i : Fin m, ∑ j : Fin J, b₂ i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))) := by
    simp only [add_mul, Finset.sum_add_distrib, mul_sub, Finset.mul_sum, mul_assoc]
    ring
  rw [hsplit]
  calc _ ≤ ‖z‖ * (C₁ * y₁ ^ τ) + C₂ * y₁ ^ τ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ e₂)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left e₁ (norm_nonneg _)
    _ = (‖z‖ * C₁ + C₂) * y₁ ^ τ := by ring

theorem mem_continuous_and_hasExpansion (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hUc : Continuous u) (m J : ℕ) (e : Fin m → ℂ)
    (a : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => a i j p.1 p.2) {p | 0 < p.1}) (τ : ℝ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ u (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, a i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hw : w ∈ modl u) :
    Continuous w ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, HasExpansion m J e τ w b := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI : IsLocallyFiniteMeasure (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  have hUli : LocallyIntegrable u (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := hUc.locallyIntegrable
  refine Submodule.span_induction (p := fun w _ => Continuous w ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
    HasExpansion m J e τ w b) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨(LanglandsTunnell.CubicInduction.SlabL2.continuous_and_isArchSmooth3_smoothingOperator φ u hφ.1 hUli).1,
      fun i j y₂ k => ∫ h, φ h * a i j y₂ (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ), ?_⟩
    exact LanglandsTunnell.CubicInduction.SlabL2.exists_expansion_whittaker3_smoothingOperator u hUc φ hφ.1 m J e a hcont τ hexp
  · exact ⟨continuous_const, _, hasExpansion_zero m J e τ⟩
  · rintro w₁ w₂ - - ⟨hc₁, b₁, hb₁⟩ ⟨hc₂, b₂, hb₂⟩
    have h := hasExpansion_smul_add m J e τ 1 hc₁ hc₂ hb₁ hb₂
    rw [one_smul] at h
    exact ⟨hc₁.add hc₂, _, h⟩
  · rintro z w - ⟨hc, b, hb⟩
    have h := hasExpansion_smul_add m J e τ z (w₂ := (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) hc continuous_zero hb
      (hasExpansion_zero m J e τ)
    rw [add_zero] at h
    exact ⟨hc.const_smul z, _, h⟩

theorem coeffA_eq_zero_of_not (m J : ℕ) (e : Fin m → ℂ) (τ : ℝ) (i₀ : Fin m) (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (h : ¬ (0 < y₂ ∧ 0 < J)) : coeffA m J e τ i₀ w y₂ k = 0 := by
  classical
  unfold coeffA
  rw [dif_neg]
  exact fun h' => h ⟨h'.1, h'.2.1⟩

theorem coeffA_smoothing_eq (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hUc : Continuous u) (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e)
    (a : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => a i j p.1 p.2) {p | 0 < p.1}) (τ : ℝ) (hτ : 1 / 2 < τ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ u (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, a i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (j : Fin J) (hj : (j : ℕ) = 0) (y₂ : ℝ) (hy₂ : 0 < y₂) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    coeffA m J e τ i₀ (smoothingOperator φ u) y₂ k =
      ∫ h, φ h * a i₀ j y₂ (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  have hb : HasExpansion m J e τ (smoothingOperator φ u)
      (fun i j y₂ k => ∫ h, φ h * a i j y₂ (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) :=
    LanglandsTunnell.CubicInduction.SlabL2.exists_expansion_whittaker3_smoothingOperator u hUc φ hφ m J e a hcont τ hexp
  exact coeffA_eq_of_hasExpansion m J e he τ hτ i₀ hD _ _ hb j hj y₂ hy₂ k

theorem coeffA_zero (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e) (τ : ℝ) (hτ : 1 / 2 < τ) (i₀ : Fin m)
    (hD : (e i₀).re = 1 / 2) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) : coeffA m J e τ i₀ (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) y₂ k = 0 := by
  by_cases h : 0 < y₂ ∧ 0 < J
  · exact coeffA_eq_of_hasExpansion m J e he τ hτ i₀ hD 0 _ (hasExpansion_zero m J e τ) ⟨0, h.2⟩ rfl y₂ h.1 k
  · exact coeffA_eq_zero_of_not m J e τ i₀ 0 y₂ k h

theorem archDeriv_add_of_isArchSmooth3 {φ ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ)
    (hψ : WhittakerBlock.IsArchSmooth3 ψ) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (φ + ψ) = WhittakerBlock.archDeriv i j φ + WhittakerBlock.archDeriv i j ψ :=
  congrArg Subtype.val ((WhittakerBlock.archDerivₗ i j).map_add ⟨φ, hφ⟩ ⟨ψ, hψ⟩)

theorem archDeriv_smul_of_isArchSmooth3 {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ) (c : ℂ) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (c • φ) = c • WhittakerBlock.archDeriv i j φ :=
  congrArg Subtype.val ((WhittakerBlock.archDerivₗ i j).map_smul c ⟨φ, hφ⟩)

theorem archDeriv_zero (i j : Fin 3) : WhittakerBlock.archDeriv i j (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = 0 := by
  funext g
  simp [WhittakerBlock.archDeriv]

def archHom : AdeleRing (𝓞 ℚ) ℚ →+* ℝ :=
  realCoordinate.comp (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ →+* InfiniteAdeleRing ℚ)

theorem archEntries_eq (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    archEntries g i j = archHom ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) := rfl

theorem archEntries_mul (x y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Matrix.of (archEntries (x * y)) = Matrix.of (archEntries x) * Matrix.of (archEntries y) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, archEntries_eq, Units.val_mul, map_sum, map_mul]

theorem archEntries_one : Matrix.of (archEntries (1 : AdelicGL 3 (𝓞 ℚ) ℚ)) = 1 := by
  ext i j
  simp only [Matrix.of_apply, archEntries_eq, Units.val_one, Matrix.one_apply]
  split_ifs with h
  · exact map_one _
  · exact map_zero _

theorem det_archEntries_ne_zero (x : AdelicGL 3 (𝓞 ℚ) ℚ) : (Matrix.of (archEntries x)).det ≠ 0 := by
  have h : Matrix.of (archEntries x) * Matrix.of (archEntries x⁻¹) = 1 := by
    rw [← archEntries_mul, mul_inv_cancel, archEntries_one]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

def mulLeftEquiv (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : P.det ≠ 0) : (Fin 3 → Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun M a b => (P * Matrix.of M) a b
      map_add' := fun M N => by
        funext a b
        show (P * (Matrix.of M + Matrix.of N)) a b = (P * Matrix.of M) a b + (P * Matrix.of N) a b
        rw [Matrix.mul_add]; rfl
      map_smul' := fun c M => by
        funext a b
        show (P * (c • Matrix.of M)) a b = c * (P * Matrix.of M) a b
        rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
      invFun := fun M a b => (P⁻¹ * Matrix.of M) a b
      left_inv := fun M => by
        funext a b
        have : (P⁻¹ * (P * Matrix.of M)) = Matrix.of M := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mul]
        exact congrFun (congrFun this a) b
      right_inv := fun M => by
        funext a b
        have : (P * (P⁻¹ * Matrix.of M)) = Matrix.of M := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mul]
        exact congrFun (congrFun this a) b }

theorem mulLeftEquiv_apply (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : P.det ≠ 0) (M : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (mulLeftEquiv P hP M) = P * Matrix.of M := by
  ext a b; rfl

theorem isSmoothingKernel_comp_mul_left (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) :
    IsSmoothingKernel (fun g => φ (k⁻¹ * g)) := by
  obtain ⟨α, K', ⟨hαs, hαc, hαt⟩, hK', hcof, hφ⟩ := hφ
  set P : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (archEntries k⁻¹) with hP
  have hPdet : P.det ≠ 0 := det_archEntries_ne_zero k⁻¹
  let L := mulLeftEquiv P hPdet
  have hL : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, archEntries (k⁻¹ * g) = L (archEntries g) := by
    intro g
    have h1 := archEntries_mul k⁻¹ g
    have h2 := mulLeftEquiv_apply P hPdet (archEntries g)
    have : Matrix.of (archEntries (k⁻¹ * g)) = Matrix.of (L (archEntries g)) := by rw [h1, h2]
    exact Matrix.of.injective this
  refine ⟨α ∘ L, K', ⟨hαs.comp L.contDiff, ?_, ?_⟩, hK', hcof, fun g => ?_⟩
  · exact hαc.comp_homeomorph L.toHomeomorph
  · intro M hM
    have hsub : tsupport (α ∘ L) ⊆ L ⁻¹' tsupport α := by
      rw [tsupport, tsupport, Function.support_comp_eq_preimage]
      exact closure_minimal (Set.preimage_mono subset_closure) (isClosed_closure.preimage L.continuous)
    have hdet : (Matrix.of (L M)).det ≠ 0 := hαt (hsub hM)
    rw [mulLeftEquiv_apply, Matrix.det_mul] at hdet
    exact fun h0 => hdet (by rw [show (Matrix.of M).det = 0 from h0, mul_zero])
  · show φ (k⁻¹ * g) = _
    rw [hφ (k⁻¹ * g)]
    have hind : (k⁻¹ * g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}) ↔
        (g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}) := by
      simp only [Set.mem_setOf_eq, map_mul, map_inv, hk, inv_one, one_mul]
    simp only [Function.comp_apply, hL g]
    congr 1
    by_cases hg : g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hind.mpr hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt hind.mp hg)]

theorem leftOrthFinite_comp_mul_left (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hfin : ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1)
    (hko : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) :
    ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
        (fun g => (fun g => φ (k⁻¹ * g)) (k'⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
  obtain ⟨S, hS⟩ := hfin
  refine ⟨S, fun k' hk' hk'o => ?_⟩
  have hprod : (fun g => (fun g => φ (k⁻¹ * g)) (k'⁻¹ * g)) = fun g => φ ((k' * k)⁻¹ * g) := by
    funext g; simp [_root_.mul_inv_rev, mul_assoc]
  rw [hprod]
  refine hS (k' * k) (fun p => by rw [map_mul, hk p, hk' p, one_mul]) ?_
  show (((archComponent3 (𝓞 ℚ) ℚ (k' * k) : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)))ᵀ * ((archComponent3 (𝓞 ℚ) ℚ (k' * k) : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = 1
  have h1 : (((archComponent3 (𝓞 ℚ) ℚ k' : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)))ᵀ * ((archComponent3 (𝓞 ℚ) ℚ k' : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = 1 := hk'o
  have h2 : (((archComponent3 (𝓞 ℚ) ℚ k : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)))ᵀ * ((archComponent3 (𝓞 ℚ) ℚ k : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = 1 := hko
  rw [map_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (((archComponent3 (𝓞 ℚ) ℚ k' : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) _, h1, Matrix.one_mul, h2]

theorem smoothingOperator_mul_right (φ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (k x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    smoothingOperator φ u (x * k) = smoothingOperator (fun g => φ (k⁻¹ * g)) u x := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  rw [smoothingOperator_apply, smoothingOperator_apply]
  rw [← integral_mul_left_eq_self (fun g => φ (k⁻¹ * g) * u (x * g)) k]
  simp only [inv_mul_cancel_left, mul_assoc]

theorem whittaker3_mul_right (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (k g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ (fun x => φ (x * k)) g = whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ (g * k) := by
  unfold whittaker3
  simp_rw [mul_assoc]

end MemExp48
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_expansion_leadingCoeff.MemExp48"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_expansion_leadingCoeff.MemExp48"

attribute [local instance] NumberField.AdelicHaar.glBorel

open MemExp48 in
open scoped Classical in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hmg : IsModerateGrowth3 ℚ f)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i))
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
          φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
            (fun g => ∑ i, c i * f (g * h * t i)) w})
    (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e)
    (a : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => a i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, a i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2) :
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}) ∧
            ∀ (y₂ : ℝ) (k' : AdelicGL 3 (𝓞 ℚ) ℚ), (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (fun g => w (g * k)) y₂ k' = (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w y₂ (k' * k)) ∧
    (∀ (z : ℂ), ∀ w₁ ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ w₂ ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (z • w₁ + w₂) y₂ k = z * (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w₁ y₂ k + (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w₂ y₂ k) ∧
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ j : Fin J, (j : ℕ) = 0 → ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, b i₀ j y₂ k = (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w y₂ k) ∧
        ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) ∧
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ i j : Fin 3, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))
          ((fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (WhittakerBlock.archDeriv i j w) y₂ k) 0) ∧
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ c₁ c₂ : Fin 3, c₁ < c₂ → ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w y₂ (k * WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0)))
          ((fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (WhittakerBlock.archDeriv c₂ c₁ w) y₂ k - (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (WhittakerBlock.archDeriv c₁ c₂ w) y₂ k) 0) := by
  classical
  obtain ⟨hUc, hUaut, hUcen, hUmg, hUP21, hUP12, hUsa, hUcw⟩ :=
    LanglandsTunnell.CubicInduction.seed_package_of_mem_span_archDeriv_translate ω hω f hc haut hcen hmg hP21 hP12 hsa hKf n c t
      ht hz u hu m J e he a hcont τ hτ hexp i₀ hD
  have hC6 : (∀ (z : ℂ), ∀ w₁ ∈ modl u, ∀ w₂ ∈ modl u, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        coeffA m J e τ i₀ (z • w₁ + w₂) y₂ k = z * coeffA m J e τ i₀ w₁ y₂ k + coeffA m J e τ i₀ w₂ y₂ k) := by
    intro z w₁ hw₁ w₂ hw₂ y₂ k
    by_cases hy : 0 < y₂
    · by_cases hJ : 0 < J
      · obtain ⟨hc₁, b₁, hb₁⟩ := mem_continuous_and_hasExpansion u hUc m J e a hcont τ hexp w₁ hw₁
        obtain ⟨hc₂, b₂, hb₂⟩ := mem_continuous_and_hasExpansion u hUc m J e a hcont τ hexp w₂ hw₂
        have hb := hasExpansion_smul_add m J e τ z hc₁ hc₂ hb₁ hb₂
        rw [coeffA_eq_of_hasExpansion m J e he τ hτ i₀ hD _ _ hb ⟨0, hJ⟩ rfl y₂ hy k,
          coeffA_eq_of_hasExpansion m J e he τ hτ i₀ hD _ _ hb₁ ⟨0, hJ⟩ rfl y₂ hy k,
          coeffA_eq_of_hasExpansion m J e he τ hτ i₀ hD _ _ hb₂ ⟨0, hJ⟩ rfl y₂ hy k]
      · have hcond : ∀ w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
            ¬ (0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, HasExpansion m J e τ w b) :=
          fun w h => hJ h.2.1
        simp [coeffA, hcond]
    · have hcond : ∀ w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          ¬ (0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, HasExpansion m J e τ w b) :=
        fun w h => hy h.1
      simp [coeffA, hcond]

  obtain ⟨hC1, -⟩ := LanglandsTunnell.CubicInduction.smoothingModule_regularity_and_growth ω hω f hc haut hcen hmg hP21 hP12
    hsa hKf n c t ht hz u hu m J e he a hcont τ hτ hexp i₀ hD
  obtain ⟨-, hC5⟩ := LanglandsTunnell.CubicInduction.smoothingModule_orthFinite_and_archDeriv_mem ω hω f hc haut hcen hmg hP21
    hP12 hsa hKf n c t ht hz u hu m J e he a hcont τ hτ hexp i₀ hD
  have hSm : ∀ w ∈ modl u, WhittakerBlock.IsArchSmooth3 w := fun w hw => (hC1 w hw).1
  have hDm : ∀ w ∈ modl u, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ modl u := fun w hw => hC5 w hw
  have hAadd : ∀ w₁ ∈ modl u, ∀ w₂ ∈ modl u, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
      coeffA m J e τ i₀ (w₁ + w₂) y₂ k = coeffA m J e τ i₀ w₁ y₂ k + coeffA m J e τ i₀ w₂ y₂ k := by
    intro w₁ hw₁ w₂ hw₂ y₂ k
    have h := hC6 1 w₁ hw₁ w₂ hw₂ y₂ k
    rwa [one_smul, one_mul] at h
  have hAsmul : ∀ (z : ℂ), ∀ w ∈ modl u, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
      coeffA m J e τ i₀ (z • w) y₂ k = z * coeffA m J e τ i₀ w y₂ k := by
    intro z w hw y₂ k
    have h := hC6 z w hw 0 (Submodule.zero_mem _) y₂ k
    rwa [add_zero, coeffA_zero m J e he τ hτ i₀ hD, add_zero] at h
  refine ⟨?C4, ?C6, ?C7, ?C8, ?C9⟩
  case C4 =>
    intro w hw k hk1 hk2
    constructor
    · refine Submodule.span_induction (p := fun w _ => (fun g => w (g * k)) ∈ modl u) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨φ, hφ, rfl⟩
        have heq : (fun g => smoothingOperator φ u (g * k)) = smoothingOperator (fun g => φ (k⁻¹ * g)) u := by
          funext x; exact smoothingOperator_mul_right φ u k x
        rw [heq]
        exact Submodule.subset_span ⟨_, ⟨isSmoothingKernel_comp_mul_left φ hφ.1 k hk1,
          leftOrthFinite_comp_mul_left φ hφ.2 k hk1 hk2⟩, rfl⟩
      · exact (modl u).zero_mem
      · intro w₁ w₂ _ _ h₁ h₂
        exact (modl u).add_mem h₁ h₂
      · intro z w _ h
        exact (modl u).smul_mem z h
    · intro y₂ k'
      show coeffA m J e τ i₀ (fun g => w (g * k)) y₂ k' = coeffA m J e τ i₀ w y₂ (k' * k)
      by_cases hyJ : 0 < y₂ ∧ 0 < J
      · obtain ⟨hy₂, hJ⟩ := hyJ
        obtain ⟨hwc, b, hb⟩ := mem_continuous_and_hasExpansion u hUc m J e a hcont τ hexp w hw
        have hb' : HasExpansion m J e τ (fun g => w (g * k)) (fun i j y₂ k' => b i j y₂ (k' * k)) := by
          refine ⟨fun i j => ?_, fun K hK bd hbd => ?_⟩
          · exact (hb.1 i j).comp (continuous_fst.prodMk (continuous_snd.mul continuous_const)).continuousOn
              (fun p hp => hp)
          · obtain ⟨C, hC⟩ := hb.2 ((fun x => x * k) '' K) (hK.image (continuous_mul_right k)) bd hbd
            refine ⟨C, fun k' hk' y₂ hlo hhi y₁ hy hy' => ?_⟩
            have h := hC (k' * k) ⟨k', hk', rfl⟩ y₂ hlo hhi y₁ hy hy'
            rw [whittaker3_mul_right w k, mul_assoc]
            exact h
        rw [coeffA_eq_of_hasExpansion m J e he τ hτ i₀ hD _ _ hb' ⟨0, hJ⟩ rfl y₂ hy₂ k',
          coeffA_eq_of_hasExpansion m J e he τ hτ i₀ hD w b hb ⟨0, hJ⟩ rfl y₂ hy₂ (k' * k)]
      · rw [coeffA_eq_zero_of_not m J e τ i₀ _ y₂ k' hyJ, coeffA_eq_zero_of_not m J e τ i₀ w y₂ (k' * k) hyJ]
  case C6 => exact hC6
  case C7 =>
    intro w hw
    obtain ⟨-, b, hb⟩ := mem_continuous_and_hasExpansion u hUc m J e a hcont τ hexp w hw
    exact ⟨b, hb.1, fun j hj y₂ hy₂ k => (coeffA_eq_of_hasExpansion m J e he τ hτ i₀ hD w b hb j hj y₂ hy₂ k).symm, hb.2⟩
  case C8 =>

    haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
    haveI : IsLocallyFiniteMeasure (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
      isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
    have hUli : LocallyIntegrable u (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := hUc.locallyIntegrable
    have gen : ∀ φ ∈ kernels, ∀ i j : Fin 3, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt (fun s : ℝ => coeffA m J e τ i₀ (smoothingOperator φ u) y₂ (k * (WhittakerBlock.archRealLift3 fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)))
          (coeffA m J e τ i₀ (WhittakerBlock.archDeriv i j (smoothingOperator φ u)) y₂ k) 0 := by
      intro φ hφ i j y₂ k
      obtain ⟨hXK, hXeq⟩ := LanglandsTunnell.CubicInduction.SlabL2.archDeriv_smoothingOperator φ u hφ.1 hUli i j
      by_cases hyJ : 0 < y₂ ∧ 0 < J
      · obtain ⟨hy₂, hJ⟩ := hyJ
        have hcA : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => a i₀ ⟨0, hJ⟩ y₂ g :=
          (hcont i₀ ⟨0, hJ⟩).comp_continuous (Continuous.prodMk continuous_const continuous_id) fun g => hy₂
        have hfun : (fun s : ℝ => coeffA m J e τ i₀ (smoothingOperator φ u) y₂ (k * (WhittakerBlock.archRealLift3 fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) =
            fun s : ℝ => ∫ h, φ h * a i₀ ⟨0, hJ⟩ y₂ (k * (WhittakerBlock.archRealLift3 fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * h)
              ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
          funext s
          exact coeffA_smoothing_eq u hUc m J e he a hcont τ hτ hexp i₀ hD φ hφ.1 ⟨0, hJ⟩ rfl y₂ hy₂ _
        have hval : coeffA m J e τ i₀ (WhittakerBlock.archDeriv i j (smoothingOperator φ u)) y₂ k =
            ∫ h, (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * y)) 0) h * a i₀ ⟨0, hJ⟩ y₂ (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
          rw [hXeq]
          exact coeffA_smoothing_eq u hUc m J e he a hcont τ hτ hexp i₀ hD _ hXK ⟨0, hJ⟩ rfl y₂ hy₂ k
        rw [hfun, hval]
        exact (LanglandsTunnell.CubicInduction.SlabL2.hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel
          (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => a i₀ ⟨0, hJ⟩ y₂ g) hcA φ hφ.1 k).1 i j
      · have h0 : ∀ w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, coeffA m J e τ i₀ w y₂ k' = 0 :=
          fun w k' => coeffA_eq_zero_of_not m J e τ i₀ w y₂ k' hyJ
        simp only [h0]
        exact hasDerivAt_const 0 0

    intro w hw
    refine Submodule.span_induction (p := fun w _ => ∀ (i j : Fin 3) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
      HasDerivAt (fun s : ℝ => coeffA m J e τ i₀ w y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))
        (coeffA m J e τ i₀ (WhittakerBlock.archDeriv i j w) y₂ k) 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨φ, hφ, rfl⟩ i j y₂ k
      exact gen φ hφ i j y₂ k
    · intro i j y₂ k
      simp only [coeffA_zero m J e he τ hτ i₀ hD, archDeriv_zero]
      exact hasDerivAt_const 0 0
    · intro w₁ w₂ hw₁ hw₂ h₁ h₂ i j y₂ k
      have e1 : (fun s : ℝ => coeffA m J e τ i₀ (w₁ + w₂) y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) =
          fun s : ℝ => coeffA m J e τ i₀ w₁ y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) +
          coeffA m J e τ i₀ w₂ y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) := by
        funext s; exact hAadd w₁ hw₁ w₂ hw₂ y₂ _
      rw [e1, archDeriv_add_of_isArchSmooth3 (hSm w₁ hw₁) (hSm w₂ hw₂),
        hAadd _ (hDm w₁ hw₁ i j) _ (hDm w₂ hw₂ i j)]
      exact (h₁ i j y₂ k).add (h₂ i j y₂ k)
    · intro z w hw h i j y₂ k
      have e1 : (fun s : ℝ => coeffA m J e τ i₀ (z • w) y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) =
          fun s : ℝ => z * coeffA m J e τ i₀ w y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) := by
        funext s; exact hAsmul z w hw y₂ _
      rw [e1, archDeriv_smul_of_isArchSmooth3 (hSm w hw), hAsmul z _ (hDm w hw i j)]
      exact (h i j y₂ k).const_mul z
  case C9 =>
    haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
    haveI : IsLocallyFiniteMeasure (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
    have hUli : LocallyIntegrable u (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := hUc.locallyIntegrable
    have gen : ∀ φ ∈ kernels, ∀ c₁ c₂ : Fin 3, c₁ < c₂ → ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt (fun s : ℝ => coeffA m J e τ i₀ (smoothingOperator φ u) y₂ (k * (WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0))))
          (coeffA m J e τ i₀ (WhittakerBlock.archDeriv c₂ c₁ (smoothingOperator φ u)) y₂ k -
            coeffA m J e τ i₀ (WhittakerBlock.archDeriv c₁ c₂ (smoothingOperator φ u)) y₂ k) 0 := by
      intro φ hφ c₁ c₂ hlt y₂ k
      obtain ⟨hXK₂₁, hXeq₂₁⟩ := LanglandsTunnell.CubicInduction.SlabL2.archDeriv_smoothingOperator φ u hφ.1 hUli c₂ c₁
      obtain ⟨hXK₁₂, hXeq₁₂⟩ := LanglandsTunnell.CubicInduction.SlabL2.archDeriv_smoothingOperator φ u hφ.1 hUli c₁ c₂
      by_cases hyJ : 0 < y₂ ∧ 0 < J
      · obtain ⟨hy₂, hJ⟩ := hyJ
        have hcA : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => a i₀ ⟨0, hJ⟩ y₂ g :=
          (hcont i₀ ⟨0, hJ⟩).comp_continuous (Continuous.prodMk continuous_const continuous_id) fun g => hy₂
        have hfun : (fun s : ℝ => coeffA m J e τ i₀ (smoothingOperator φ u) y₂ (k * (WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0)))) =
            fun s : ℝ => ∫ h, φ h * a i₀ ⟨0, hJ⟩ y₂ (k * (WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0)) * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
          funext s
          exact coeffA_smoothing_eq u hUc m J e he a hcont τ hτ hexp i₀ hD φ hφ.1 ⟨0, hJ⟩ rfl y₂ hy₂ _
        have hval₂₁ : coeffA m J e τ i₀ (WhittakerBlock.archDeriv c₂ c₁ (smoothingOperator φ u)) y₂ k =
            ∫ h, (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₂ ∧ b = c₁ then s else 0) * y)) 0) h * a i₀ ⟨0, hJ⟩ y₂ (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
          rw [hXeq₂₁]
          exact coeffA_smoothing_eq u hUc m J e he a hcont τ hτ hexp i₀ hD _ hXK₂₁ ⟨0, hJ⟩ rfl y₂ hy₂ k
        have hval₁₂ : coeffA m J e τ i₀ (WhittakerBlock.archDeriv c₁ c₂ (smoothingOperator φ u)) y₂ k =
            ∫ h, (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₁ ∧ b = c₂ then s else 0) * y)) 0) h * a i₀ ⟨0, hJ⟩ y₂ (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
          rw [hXeq₁₂]
          exact coeffA_smoothing_eq u hUc m J e he a hcont τ hτ hexp i₀ hD _ hXK₁₂ ⟨0, hJ⟩ rfl y₂ hy₂ k
        rw [hfun, hval₂₁, hval₁₂]
        exact (LanglandsTunnell.CubicInduction.SlabL2.hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel
          (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => a i₀ ⟨0, hJ⟩ y₂ g) hcA φ hφ.1 k).2 c₁ c₂ hlt
      · have h0 : ∀ w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, coeffA m J e τ i₀ w y₂ k' = 0 :=
          fun w k' => coeffA_eq_zero_of_not m J e τ i₀ w y₂ k' hyJ
        simp only [h0, sub_zero]
        exact hasDerivAt_const 0 0
    intro w hw
    refine Submodule.span_induction (p := fun w _ => ∀ c₁ c₂ : Fin 3, c₁ < c₂ → ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
      HasDerivAt (fun s : ℝ => coeffA m J e τ i₀ w y₂ (k * (WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0))))
        (coeffA m J e τ i₀ (WhittakerBlock.archDeriv c₂ c₁ w) y₂ k - coeffA m J e τ i₀ (WhittakerBlock.archDeriv c₁ c₂ w) y₂ k) 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨φ, hφ, rfl⟩ c₁ c₂ hlt y₂ k
      exact gen φ hφ c₁ c₂ hlt y₂ k
    · intro c₁ c₂ hlt y₂ k
      simp only [coeffA_zero m J e he τ hτ i₀ hD, archDeriv_zero, sub_zero]
      exact hasDerivAt_const 0 0
    · intro w₁ w₂ hw₁ hw₂ h₁ h₂ c₁ c₂ hlt y₂ k
      have e1 : (fun s : ℝ => coeffA m J e τ i₀ (w₁ + w₂) y₂ (k * (WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0)))) =
          fun s : ℝ => coeffA m J e τ i₀ w₁ y₂ (k * (WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0))) + coeffA m J e τ i₀ w₂ y₂ (k * (WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0))) := by
        funext s; exact hAadd w₁ hw₁ w₂ hw₂ y₂ _
      rw [e1, archDeriv_add_of_isArchSmooth3 (hSm w₁ hw₁) (hSm w₂ hw₂),
        archDeriv_add_of_isArchSmooth3 (hSm w₁ hw₁) (hSm w₂ hw₂),
        hAadd _ (hDm w₁ hw₁ c₂ c₁) _ (hDm w₂ hw₂ c₂ c₁), hAadd _ (hDm w₁ hw₁ c₁ c₂) _ (hDm w₂ hw₂ c₁ c₂)]
      exact ((h₁ c₁ c₂ hlt y₂ k).add (h₂ c₁ c₂ hlt y₂ k)).congr_deriv (by ring)
    · intro z w hw h c₁ c₂ hlt y₂ k
      have e1 : (fun s : ℝ => coeffA m J e τ i₀ (z • w) y₂ (k * (WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0)))) =
          fun s : ℝ => z * coeffA m J e τ i₀ w y₂ (k * (WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0))) := by
        funext s; exact hAsmul z w hw y₂ _
      rw [e1, archDeriv_smul_of_isArchSmooth3 (hSm w hw), archDeriv_smul_of_isArchSmooth3 (hSm w hw),
        hAsmul z _ (hDm w hw c₂ c₁), hAsmul z _ (hDm w hw c₁ c₂)]
      exact ((h c₁ c₂ hlt y₂ k).const_mul z).congr_deriv (by ring)

end S_LanglandsTunnell_CubicInduction_smoothingModule_expansion_leadingCoeff
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_expansion_leadingCoeff (solution)
