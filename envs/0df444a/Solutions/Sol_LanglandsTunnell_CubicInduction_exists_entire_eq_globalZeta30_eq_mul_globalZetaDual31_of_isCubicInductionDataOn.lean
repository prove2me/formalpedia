-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/25f04885-5d86-568b-a117-99df87ee08db

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_differentiable_boundedOnStrips_globalZeta31_eq_add_of_integrable
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasSum_torus_radicalCoefficient_mirabolicSeries
import Theorems.Thm_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual
import Theorems.Thm_LanglandsTunnell_CubicInduction_summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3
import Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionData_dualWhittaker_eq_dualWhittakerFn3
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul"
p2m_attr_erase "simp" "FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse

section Auxiliary

open MeasureTheory

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.addCharLevel LDatum LDatum.BoundedOnStrips"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 dualWhittakerFn3 weylPrime3 transposeInv3_weylPrime3 globalZeta30 globalZetaDual31 transposeInv3 psiLoc dualForm mirabolicTranslate AdelicGL globalPointsGL embedMat2 iotaGL MirabolicIndex IsBadPlace diagUnitGL2 diagHom_apply IsGaugeMajorised3 exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable exists_differentiable_boundedOnStrips_globalZeta31_eq_add_of_integrable hasSum_torus_radicalCoefficient_mirabolicSeries box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 CubicInductionData IsCubicInductionDataOn"
namespace ZetaFunctionalEquation
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem isAdmissibleTwist_inv (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ) :
    IsAdmissibleTwist ℚ χ⁻¹ := by
  obtain ⟨hcls, hcont, hunit⟩ := hχ
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · simp [hcls u]
  · have h : ⇑χ⁻¹ = fun x => (χ x)⁻¹ := by ext x; simp
    rw [h]; exact continuous_inv.comp hcont
  · simp [hunit x]

private theorem boundedOnStrips_combine (E₁ E₂ : ℂ → ℂ) (h₁ : LanglandsTunnell.LDatum.BoundedOnStrips E₁)
    (h₂ : LanglandsTunnell.LDatum.BoundedOnStrips E₂) (c : ℂ) :
    LanglandsTunnell.LDatum.BoundedOnStrips fun s => E₁ s + c * E₂ (1 - s) := by
  intro a b
  obtain ⟨C₁, hC₁⟩ := h₁ a b
  obtain ⟨C₂, hC₂⟩ := h₂ (1 - b) (1 - a)
  refine ⟨C₁ + ‖c‖ * C₂, fun s ha hb => ?_⟩
  have h1 : ‖E₁ s‖ ≤ C₁ := hC₁ s ha hb
  have h2 : ‖E₂ (1 - s)‖ ≤ C₂ := hC₂ (1 - s) (by simp; linarith) (by simp; linarith)
  calc ‖E₁ s + c * E₂ (1 - s)‖ ≤ ‖E₁ s‖ + ‖c * E₂ (1 - s)‖ := norm_add_le _ _
    _ = ‖E₁ s‖ + ‖c‖ * ‖E₂ (1 - s)‖ := by rw [norm_mul]
    _ ≤ C₁ + ‖c‖ * C₂ := by gcongr

private theorem differentiable_combine (E₁ E₂ : ℂ → ℂ) (h₁ : Differentiable ℂ E₁) (h₂ : Differentiable ℂ E₂)
    (c : ℂ) : Differentiable ℂ fun s => E₁ s + c * E₂ (1 - s) :=
  h₁.add ((h₂.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul c)

section Form

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
variable (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)

private theorem tsum_whittaker_translate (X : CubicInductionData) (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∑' i : MirabolicIndex ℚ, X.whittaker (mirabolicTranslate i * x)) = X.form x :=
  (hX.expansion x).tsum_eq

private theorem transposeInv3_mul (a b : AdelicGL 3 (𝓞 ℚ) ℚ) :
    transposeInv3 (a * b) = transposeInv3 a * transposeInv3 b := by
  apply Units.ext
  simp [transposeInv3, Matrix.transpose_mul, mul_inv_rev]

private theorem transposeInv3_transposeInv3 (a : AdelicGL 3 (𝓞 ℚ) ℚ) : transposeInv3 (transposeInv3 a) = a :=
  Units.ext (Matrix.transpose_transpose _)

private theorem globalPointsGL_weylPrime3 :
    globalPointsGL 3 (𝓞 ℚ) ℚ (weylPrime3 : GL (Fin 3) ℚ) = (weylPrime3 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPointsGL, weylPrime3]

private theorem form_weylPrime3_mul (X : CubicInductionData) (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X) (x : AdelicGL 3 (𝓞 ℚ) ℚ) : X.form (weylPrime3 * x) = X.form x := by
  rw [← globalPointsGL_weylPrime3]
  exact hX.automorphic _ x

private theorem tsum_dualWhittakerFn3_translate (X : CubicInductionData) (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X) (_hcont : Continuous X.form) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∑' i : MirabolicIndex ℚ,
        dualWhittakerFn3 X.whittaker (mirabolicTranslate i * (weylPrime3 * transposeInv3 x))) = X.form x := by
  rw [← CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 ψ D U gen X hX.automorphic hX.whittaker_eq hX.whittaker_law hX.expansion hX.dualWhittaker_eq _hcont,
    (hX.dual_expansion _).tsum_eq, dualForm, transposeInv3_mul, transposeInv3_weylPrime3,
    transposeInv3_transposeInv3]
  exact form_weylPrime3_mul K ψ μ D U gen X S hX x

private theorem volume_mul_tsum_whittaker_eq_ideleNorm_mul_tsum_dual (X : CubicInductionData) (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X) (hψ : IsGlobalAddChar ℚ ψ)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker)
    (hsum : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => X.whittaker (mirabolicTranslate i * x))
    (hsum' : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 X.whittaker (mirabolicTranslate i * x))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hfin : (∑' α : ℚˣ, ∫⁻ x : AdeleRing (𝓞 ℚ) ℚ,
        (‖dualWhittakerFn3 X.whittaker
            (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
              lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))‖₊ : ENNReal)
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) < ⊤) :
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
        ∑' α : ℚˣ, X.whittaker (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α)) *
          (iotaGL (diagUnitGL2 a) * g)) =
      ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) *
        ∑' α : ℚˣ, ∫ x : AdeleRing (𝓞 ℚ) ℚ,
          dualWhittakerFn3 X.whittaker
            (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
              lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  have hB := hasSum_torus_radicalCoefficient_mirabolicSeries ψ hψ X.whittaker hX.whittaker_law hsum
    (iotaGL (diagUnitGL2 a) * g)
  have hDual := box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual ψ hψ X.whittaker hcontW
    hX.whittaker_law hsum' g a hfin
  simp only [tsum_whittaker_translate K ψ μ D U gen X S hX] at hB
  simp only [tsum_dualWhittakerFn3_translate K ψ μ D U gen X S hX hcont] at hDual
  rw [hB.tsum_eq]
  exact hDual

end Form

noncomputable section Fold

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
  NumberField.AdeleRing.secondCountableTopology

private theorem locallyCompactSpace_ideles : LocallyCompactSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

attribute [local instance] locallyCompactSpace_ideles

private theorem regular_idelicHaar : (NumberField.Idele.idelicHaar ℚ).Regular := by
  rw [NumberField.Idele.idelicHaar]; infer_instance

attribute [local instance] regular_idelicHaar

private theorem isInvInvariant_idelicHaar : (NumberField.Idele.idelicHaar ℚ).IsInvInvariant := inferInstance

private theorem secondCountableTopology_ideles : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 ℚ) ℚ)).symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

attribute [local instance] secondCountableTopology_ideles

private theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar ℚ) := inferInstance

attribute [local instance] isInvInvariant_idelicHaar sigmaFinite_idelicHaar

private abbrev ratIdele (α : ℚˣ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ := Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α

private theorem ideleNorm_ratIdele (α : ℚˣ) : TateGlobal.ideleNorm ℚ (ratIdele α) = 1 := by
  have h : distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (ratIdele α) = 1 :=
    NumberField.AdeleRing.distribHaarChar_algebraMap ℚ α
  simp only [TateGlobal.ideleNorm, h, NNReal.coe_one]

private theorem ideleNorm_ratIdele_mul (α : ℚˣ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    TateGlobal.ideleNorm ℚ (ratIdele α * a) = TateGlobal.ideleNorm ℚ a := by
  rw [TateGlobal.ideleNorm_mul, ideleNorm_ratIdele, one_mul]

private theorem ideleNorm_one' : TateGlobal.ideleNorm ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
  have h := ideleNorm_ratIdele 1
  simpa only [ratIdele, map_one] using h

private theorem ideleNorm_inv (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    TateGlobal.ideleNorm ℚ a⁻¹ = (TateGlobal.ideleNorm ℚ a)⁻¹ := by
  have h := TateGlobal.ideleNorm_mul a a⁻¹
  rw [mul_inv_cancel, ideleNorm_one'] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem twist_ratIdele_mul (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ) (α : ℚˣ)
    (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : χ (ratIdele α * a) = χ a := by
  rw [map_mul, hχ.1 α, one_mul]

private theorem iotaGL_diagUnitGL2_mul (x y : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    iotaGL (diagUnitGL2 (x * y)) = iotaGL (diagUnitGL2 x) * iotaGL (diagUnitGL2 y) := by
  rw [← diagHom_apply, ← diagHom_apply, ← diagHom_apply, ← map_mul, ← map_mul]

private theorem ratIdele_injective : Function.Injective fun α : ℚˣ => ratIdele α :=
  Units.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ)

private def principalIdelesEquiv : ℚˣ ≃ M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ :=
  Equiv.ofBijective (fun α => ⟨ratIdele α, MonoidHom.mem_range.mpr ⟨α, rfl⟩⟩)
    ⟨fun α β h => ratIdele_injective (congrArg Subtype.val h), fun x => by
      obtain ⟨α, hα⟩ := MonoidHom.mem_range.mp x.2
      exact ⟨α, Subtype.ext hα⟩⟩

private theorem principalIdelesEquiv_apply (α : ℚˣ) :
    ((principalIdelesEquiv α : M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = ratIdele α :=
  rfl

private scoped instance : Countable ℚˣ := Units.val_injective.countable

private scoped instance : Countable (M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ) := Countable.of_equiv ℚˣ principalIdelesEquiv

private theorem continuous_iotaGL_diagUnitGL2 :
    Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (iotaGL (diagUnitGL2 a) : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> first | exact Units.continuous_val | exact continuous_const
  · show Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      embedMat2 !![((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ), 0; 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] <;>
      first | exact Units.continuous_coe_inv | exact continuous_const

private theorem norm_zetaIntegrand (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχ : IsAdmissibleTwist ℚ χ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ‖W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)‖ =
      ‖W (iotaGL (diagUnitGL2 a) * g)‖ * TateGlobal.ideleNorm ℚ a ^ (s.re - 1) := by
  rw [norm_mul, norm_mul, hχ.2.2 a, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (TateGlobal.ideleNorm_pos a),
    Complex.sub_re, Complex.one_re]

private theorem continuous_zetaIntegrand (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hWc : Continuous W)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ) :
    Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) := by
  have h₁ : Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => W (iotaGL (diagUnitGL2 a) * g) :=
    hWc.comp (continuous_iotaGL_diagUnitGL2.mul continuous_const)
  have h₂ : Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((χ a : ℂˣ) : ℂ) := Units.continuous_val.comp hχ.2.1
  have h₃ : Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) :=
    (Complex.continuous_ofReal.comp (TateGlobal.continuous_ideleNorm ℚ)).cpow continuous_const fun a =>
      Complex.ofReal_mem_slitPlane.mpr (TateGlobal.ideleNorm_pos a)
  exact (h₁.mul h₂).mul h₃

private theorem integrable_zetaIntegrand (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hWc : Continuous W)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (σ₀ : ℝ)
    (hint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      ‖W (iotaGL (diagUnitGL2 x) * g)‖ * (TateGlobal.ideleNorm ℚ x : ℝ) ^ (σ - 1)) (NumberField.Idele.idelicHaar ℚ))
    (s : ℂ) (hs : σ₀ ≤ s.re) :
    Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
      (NumberField.Idele.idelicHaar ℚ) :=
  (hint s.re hs).mono' (continuous_zetaIntegrand W hWc χ hχ g s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => (norm_zetaIntegrand W χ hχ g s a).le)

private theorem integrableOn_zetaIntegrand_large (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hWc : Continuous W)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (σ₀ : ℝ)
    (hint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      ‖W (iotaGL (diagUnitGL2 x) * g)‖ * (TateGlobal.ideleNorm ℚ x : ℝ) ^ (σ - 1)) (NumberField.Idele.idelicHaar ℚ))
    (s : ℂ) :
    IntegrableOn (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
      {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | 1 ≤ TateGlobal.ideleNorm ℚ a} (NumberField.Idele.idelicHaar ℚ) := by
  have hm : MeasurableSet {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | 1 ≤ TateGlobal.ideleNorm ℚ a} :=
    (TateGlobal.continuous_ideleNorm ℚ).measurable measurableSet_Ici
  refine (hint (max σ₀ s.re) (le_max_left _ _)).integrableOn.mono'
    (continuous_zetaIntegrand W hWc χ hχ g s).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_mem hm).mono fun a ha => ?_
  rw [norm_zetaIntegrand W χ hχ g s a]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ha (sub_le_sub_right (le_max_right σ₀ s.re) 1)) (norm_nonneg _)

private theorem continuous_lowerUnipotent21 :
    Continuous fun x : AdeleRing (𝓞 ℚ) ℚ => (lowerUnipotent21 x : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_id | exact continuous_const
  · show Continuous fun x : AdeleRing (𝓞 ℚ) ℚ => !![(1 : AdeleRing (𝓞 ℚ) ℚ), 0, 0; -x, 1, 0; 0, 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_neg | exact continuous_const

private theorem continuous_jointPoint (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
      iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h :=
  ((continuous_iotaGL_diagUnitGL2.comp continuous_fst).mul (continuous_lowerUnipotent21.comp continuous_snd)).mul
    continuous_const

private theorem norm_jointIntegrand (V : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hη : IsAdmissibleTwist ℚ η) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (t : ℂ) (p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ) :
    ‖V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h) * ((η p.1 : ℂˣ) : ℂ) *
        ((TateGlobal.ideleNorm ℚ p.1 : ℝ) : ℂ) ^ (t - 1)‖ =
      ‖V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h)‖ * TateGlobal.ideleNorm ℚ p.1 ^ (t.re - 1) := by
  rw [norm_mul, norm_mul, hη.2.2 p.1, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (TateGlobal.ideleNorm_pos p.1),
    Complex.sub_re, Complex.one_re]

private theorem continuous_jointIntegrand (V : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hVc : Continuous V)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsAdmissibleTwist ℚ η) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (t : ℂ) :
    Continuous fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
      V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h) * ((η p.1 : ℂˣ) : ℂ) *
        ((TateGlobal.ideleNorm ℚ p.1 : ℝ) : ℂ) ^ (t - 1) := by
  have h₂ : Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((η a : ℂˣ) : ℂ) := Units.continuous_val.comp hη.2.1
  have h₃ : Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (t - 1) :=
    (Complex.continuous_ofReal.comp (TateGlobal.continuous_ideleNorm ℚ)).cpow continuous_const fun a =>
      Complex.ofReal_mem_slitPlane.mpr (TateGlobal.ideleNorm_pos a)
  exact ((hVc.comp (continuous_jointPoint h)).mul (h₂.comp continuous_fst)).mul (h₃.comp continuous_fst)

private theorem integrableOn_innerIntegrand_of_integrable_joint (V : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (t : ℂ) (S : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hI : Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
        V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h) * ((η p.1 : ℂˣ) : ℂ) *
          ((TateGlobal.ideleNorm ℚ p.1 : ℝ) : ℂ) ^ (t - 1))
      (((NumberField.Idele.idelicHaar ℚ).restrict S).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) :
    IntegrableOn (fun b : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        (∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
          ((η b : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ b : ℝ) : ℂ) ^ (t - 1))
      S (NumberField.Idele.idelicHaar ℚ) :=
  hI.integral_prod_left.congr (Filter.Eventually.of_forall fun b => by simp only [integral_mul_const])

private theorem integrableOn_innerIntegrand_large (V : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hVc : Continuous V)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsAdmissibleTwist ℚ η) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (σ₀ : ℝ)
    (hjoint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
      ‖V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h)‖ * (TateGlobal.ideleNorm ℚ p.1 : ℝ) ^ (σ - 1))
      ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (t : ℂ) :
    IntegrableOn (fun b : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        (∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
          ((η b : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ b : ℝ) : ℂ) ^ (t - 1))
      {b : (AdeleRing (𝓞 ℚ) ℚ)ˣ | 1 ≤ TateGlobal.ideleNorm ℚ b} (NumberField.Idele.idelicHaar ℚ) := by
  refine integrableOn_innerIntegrand_of_integrable_joint V η h t _ ?_
  have hS : MeasurableSet {b : (AdeleRing (𝓞 ℚ) ℚ)ˣ | 1 ≤ TateGlobal.ideleNorm ℚ b} :=
    (TateGlobal.continuous_ideleNorm ℚ).measurable measurableSet_Ici
  rw [Measure.restrict_prod_eq_prod_univ]
  refine (hjoint (max σ₀ t.re) (le_max_left _ _)).restrict.mono'
    (continuous_jointIntegrand V hVc η hη h t).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_mem (hS.prod MeasurableSet.univ)).mono fun p hp => ?_
  rw [norm_jointIntegrand V η hη h t p]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp.1 (sub_le_sub_right (le_max_right σ₀ t.re) 1)) (norm_nonneg _)

private theorem integrableOn_innerIntegrand_small (V : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hVc : Continuous V)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsAdmissibleTwist ℚ η) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (σ₀ : ℝ)
    (hjoint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
      ‖V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h)‖ * (TateGlobal.ideleNorm ℚ p.1 : ℝ) ^ (σ - 1))
      ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (t : ℂ) (ht : σ₀ ≤ t.re) :
    IntegrableOn (fun b : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        (∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
          ((η b : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ b : ℝ) : ℂ) ^ (t - 1))
      {b : (AdeleRing (𝓞 ℚ) ℚ)ˣ | TateGlobal.ideleNorm ℚ b < 1} (NumberField.Idele.idelicHaar ℚ) := by
  refine integrableOn_innerIntegrand_of_integrable_joint V η h t _ ?_
  rw [Measure.restrict_prod_eq_prod_univ]
  refine Integrable.restrict ((hjoint t.re ht).mono' (continuous_jointIntegrand V hVc η hη h t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_))
  exact (norm_jointIntegrand V η hη h t p).le

private theorem ae_tsum_lintegral_lt_top (V : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hVc : Continuous V)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (σ₀ : ℝ)
    (hjoint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
      ‖V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h)‖ * (TateGlobal.ideleNorm ℚ p.1 : ℝ) ^ (σ - 1))
      ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (D : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ) D (NumberField.Idele.idelicHaar ℚ)) :
    ∀ᵐ a ∂((NumberField.Idele.idelicHaar ℚ).restrict D),
      (∑' α : ℚˣ, ∫⁻ x : AdeleRing (𝓞 ℚ) ℚ,
        ‖V (iotaGL (diagUnitGL2 (ratIdele α * a⁻¹)) * lowerUnipotent21 x * h)‖ₑ
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) < ⊤ := by

  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ENNReal, Φ = fun b => ∫⁻ x : AdeleRing (𝓞 ℚ) ℚ,
      ‖V (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h)‖ₑ ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ENNReal,
      ω = fun b => ENNReal.ofReal (TateGlobal.ideleNorm ℚ b ^ (σ₀ - 1)) := ⟨_, rfl⟩
  have hVm : Measurable fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
      ‖V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h)‖ₑ :=
    (hVc.comp (continuous_jointPoint h)).measurable.enorm
  have hΦm : Measurable Φ := by rw [hΦ]; exact hVm.lintegral_prod_right'
  have hωm : Measurable ω := by
    rw [hω]
    exact ENNReal.measurable_ofReal.comp (((TateGlobal.continuous_ideleNorm ℚ).measurable).pow_const (σ₀ - 1))
  have hω0 : ∀ b, ω b ≠ 0 := fun b => by
    simp only [hω]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (TateGlobal.ideleNorm_pos b) _)).ne'
  have hωtop : ∀ b, ω b ≠ ⊤ := fun b => by simp only [hω]; exact ENNReal.ofReal_ne_top
  have hωrat : ∀ (α : ℚˣ) (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ), ω (ratIdele α * b) = ω b := fun α b => by
    simp only [hω, ideleNorm_ratIdele_mul]

  have hfin : ∫⁻ b, Φ b * ω b ∂(NumberField.Idele.idelicHaar ℚ) < ⊤ := by
    have h1 := (hjoint σ₀ le_rfl).hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h1
    have h2 : ∫⁻ p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ,
        ‖V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h)‖ₑ * ω p.1
        ∂((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) < ⊤ := by
      refine lt_of_eq_of_lt (lintegral_congr fun p => ?_) h1
      simp only [hω]
      rw [Real.enorm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (TateGlobal.ideleNorm_pos p.1).le _)),
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
    have hjm : Measurable fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
        ‖V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h)‖ₑ * ω p.1 :=
      hVm.mul (hωm.comp measurable_fst)
    rw [lintegral_prod _ hjm.aemeasurable] at h2
    refine lt_of_eq_of_lt (lintegral_congr fun b => ?_) h2
    simp only [hΦ]
    rw [lintegral_mul_const' _ _ (hωtop b)]

  have hinv : ∫⁻ c, Φ c⁻¹ * ω c⁻¹ ∂(NumberField.Idele.idelicHaar ℚ) < ⊤ := by
    rw [lintegral_inv_eq_self (fun b => Φ b * ω b)]; exact hfin
  have hsum : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∑' γ : M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ, Φ (γ⁻¹ • a)⁻¹ * ω (γ⁻¹ • a)⁻¹) =
        (∑' α : ℚˣ, Φ (ratIdele α * a⁻¹)) * ω a⁻¹ := by
    intro a
    rw [← ENNReal.tsum_mul_right, ← principalIdelesEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    have hpt : ((principalIdelesEquiv α)⁻¹ • a)⁻¹ = ratIdele α * a⁻¹ := by
      simp only [Subgroup.smul_def, smul_eq_mul, InvMemClass.coe_inv, principalIdelesEquiv_apply, mul_inv, inv_inv]
    rw [hpt, hωrat]
  have hfold : ∫⁻ a in D, (∑' α : ℚˣ, Φ (ratIdele α * a⁻¹)) * ω a⁻¹ ∂(NumberField.Idele.idelicHaar ℚ) < ⊤ := by
    refine lt_of_eq_of_lt ?_ hinv
    rw [hD.lintegral_eq_tsum' (fun c => Φ c⁻¹ * ω c⁻¹), ← lintegral_tsum]
    · exact lintegral_congr fun a => (hsum a).symm
    · intro γ
      exact ((hΦm.comp (measurable_inv.comp (measurable_const_mul _))).mul
        (hωm.comp (measurable_inv.comp (measurable_const_mul _)))).aemeasurable
  have hmeas : Measurable fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (∑' α : ℚˣ, Φ (ratIdele α * a⁻¹)) * ω a⁻¹ :=
    (Measurable.tsum fun α => hΦm.comp ((measurable_const_mul _).comp measurable_inv)).mul
      (hωm.comp measurable_inv)
  refine (ae_lt_top hmeas hfold.ne).mono fun a ha => ?_
  have hlt := ENNReal.lt_top_of_mul_ne_top_left ha.ne (hω0 a⁻¹)
  simpa only [hΦ] using hlt

private theorem integral_eq_setIntegral_tsum (D : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ) D (NumberField.Idele.idelicHaar ℚ))
    (φ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (hφ : Integrable φ (NumberField.Idele.idelicHaar ℚ)) :
    (∫ a, φ a ∂(NumberField.Idele.idelicHaar ℚ)) =
      ∫ a in D, ∑' α : ℚˣ, φ (ratIdele α * a) ∂(NumberField.Idele.idelicHaar ℚ) := by
  let e : ℚˣ ≃ M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ := principalIdelesEquiv
  have hsmul : ∀ (α : ℚˣ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ), (e α • a) = ratIdele α * a := fun α a => rfl
  have hmeas : ∀ α : ℚˣ, AEStronglyMeasurable (fun a => φ (ratIdele α * a))
      ((NumberField.Idele.idelicHaar ℚ).restrict D) :=
    fun α => (hφ.comp_mul_left (ratIdele α)).aestronglyMeasurable.restrict
  have hfin : (∑' α : ℚˣ, ∫⁻ a in D, ‖φ (ratIdele α * a)‖ₑ ∂(NumberField.Idele.idelicHaar ℚ)) ≠ ⊤ := by
    have h := hD.lintegral_eq_tsum'' fun a => ‖φ a‖ₑ
    rw [← e.tsum_eq] at h
    simp only [hsmul] at h
    rw [← h]
    exact hφ.2.ne
  rw [hD.integral_eq_tsum'' φ hφ, ← e.tsum_eq]
  simp only [hsmul]
  rw [integral_tsum hmeas hfin]

private theorem setIntegral_indicator_congr (D : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hDm : MeasurableSet D)
    (hD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ) D (NumberField.Idele.idelicHaar ℚ))
    (T₁ T₂ : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hT : ∀ a, TateGlobal.ideleNorm ℚ a ≠ 1 → (a ∈ T₁ ↔ a ∈ T₂))
    (Φ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) :
    (∫ a in D, T₁.indicator Φ a ∂(NumberField.Idele.idelicHaar ℚ)) =
      ∫ a in D, T₂.indicator Φ a ∂(NumberField.Idele.idelicHaar ℚ) := by
  obtain ⟨V, -, hVtop, hV⟩ := NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi ℚ D hDm hD
  have hm : MeasurableSet {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | TateGlobal.ideleNorm ℚ a = 1} :=
    (TateGlobal.continuous_ideleNorm ℚ).measurable (measurableSet_singleton (1 : ℝ))
  have hnull : ((NumberField.Idele.idelicHaar ℚ).restrict D)
      {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | TateGlobal.ideleNorm ℚ a = 1} = 0 := by
    have h1 : ((NumberField.Idele.idelicHaar ℚ).restrict D)
        {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | TateGlobal.ideleNorm ℚ a = 1} =
        ∫⁻ a in D, ({(1 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ENNReal)) (TateGlobal.ideleNorm ℚ a)
          ∂(NumberField.Idele.idelicHaar ℚ) := by
      rw [← lintegral_indicator_one hm]
      rfl
    rw [h1, hV _ (measurable_const.indicator (measurableSet_singleton _))]
    have h2 : (∫⁻ y in Set.Ioi (0 : ℝ), ({(1 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ENNReal)) y *
        ENNReal.ofReal y⁻¹) = 0 := by
      have hle : ∀ y : ℝ, ({(1 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ENNReal)) y * ENNReal.ofReal y⁻¹ =
          ({(1 : ℝ)} : Set ℝ).indicator (fun y => ENNReal.ofReal y⁻¹) y := by
        intro y
        by_cases hy : y ∈ ({(1 : ℝ)} : Set ℝ)
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
      have hz : (volume.restrict (Set.Ioi (0 : ℝ))) ({(1 : ℝ)} : Set ℝ) = 0 := by
        rw [Measure.restrict_apply (measurableSet_singleton _)]
        exact measure_mono_null Set.inter_subset_left (Real.volume_singleton)
      simp_rw [hle]
      rw [lintegral_indicator (measurableSet_singleton _), Measure.restrict_eq_zero.mpr hz,
        lintegral_zero_measure]
    rw [h2, mul_zero]
  refine integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with a ha
  have hne : TateGlobal.ideleNorm ℚ a ≠ 1 := ha
  by_cases h₁ : a ∈ T₁
  · rw [Set.indicator_of_mem h₁, Set.indicator_of_mem ((hT a hne).mp h₁)]
  · rw [Set.indicator_of_notMem h₁, Set.indicator_of_notMem (fun h₂ => h₁ ((hT a hne).mpr h₂))]

private theorem ideleNorm_inv_cpow (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (s : ℂ) :
    ((TateGlobal.ideleNorm ℚ a⁻¹ : ℝ) : ℂ) ^ (1 - s - 1) = ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ s := by
  have hpos : 0 ≤ TateGlobal.ideleNorm ℚ a := (TateGlobal.ideleNorm_pos a).le
  have harg : ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hpos]; exact Real.pi_pos.ne
  rw [ideleNorm_inv, Complex.ofReal_inv, show (1 - s - 1 : ℂ) = -s by ring, Complex.inv_cpow _ _ harg,
    Complex.cpow_neg, inv_inv]

private theorem twist_inv_inv (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : χ⁻¹ a⁻¹ = χ a := by
  simp

private theorem ratIdele_inv (α : ℚˣ) : (ratIdele α)⁻¹ = ratIdele α⁻¹ := (map_inv _ α).symm

private theorem tsum_indicator_zeta_coset (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχ : IsAdmissibleTwist ℚ χ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ) (P : ℝ → Prop) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (∑' α : ℚˣ, {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)}.indicator
        (fun x => W (iotaGL (diagUnitGL2 x) * g) * ((χ x : ℂˣ) : ℂ) *
          ((TateGlobal.ideleNorm ℚ x : ℝ) : ℂ) ^ (s - 1)) (ratIdele α * a)) =
      {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)}.indicator
        (fun a => ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) *
          ∑' α : ℚˣ, W (iotaGL (diagUnitGL2 (ratIdele α)) * (iotaGL (diagUnitGL2 a) * g))) a := by
  have hmem : ∀ α : ℚˣ, ratIdele α * a ∈ {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)} ↔
      a ∈ {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)} := fun α => by
    simp only [Set.mem_setOf_eq, ideleNorm_ratIdele_mul]
  by_cases ha : a ∈ {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)}
  · rw [Set.indicator_of_mem ha]
    have hterm : ∀ α : ℚˣ, {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)}.indicator
        (fun x => W (iotaGL (diagUnitGL2 x) * g) * ((χ x : ℂˣ) : ℂ) *
          ((TateGlobal.ideleNorm ℚ x : ℝ) : ℂ) ^ (s - 1)) (ratIdele α * a) =
        W (iotaGL (diagUnitGL2 (ratIdele α)) * (iotaGL (diagUnitGL2 a) * g)) * ((χ a : ℂˣ) : ℂ) *
          ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) := fun α => by
      rw [Set.indicator_of_mem ((hmem α).mpr ha), twist_ratIdele_mul χ hχ, ideleNorm_ratIdele_mul,
        iotaGL_diagUnitGL2_mul, mul_assoc (iotaGL (diagUnitGL2 (ratIdele α))) (iotaGL (diagUnitGL2 a)) g]
    simp_rw [hterm]
    rw [tsum_mul_right, tsum_mul_right]
    ring
  · rw [Set.indicator_of_notMem ha]
    simp only [Set.indicator_of_notMem (fun hh => ha ((hmem _).mp hh)), tsum_zero]

private theorem tsum_indicator_inner_coset_inv (V : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχ : IsAdmissibleTwist ℚ χ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ) (P : ℝ → Prop) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (∑' α : ℚˣ, {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)}.indicator
        (fun b => (∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
          ((χ⁻¹ b : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ b : ℝ) : ℂ) ^ (1 - s - 1)) (ratIdele α * a)⁻¹) =
      {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)⁻¹}.indicator
        (fun a => ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ s *
          ∑' α : ℚˣ, ∫ x : AdeleRing (𝓞 ℚ) ℚ,
            V (iotaGL (diagUnitGL2 (ratIdele α * a⁻¹)) * lowerUnipotent21 x * h)
              ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) a := by
  have hmem : ∀ α : ℚˣ, (ratIdele α * a)⁻¹ ∈ {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)} ↔
      a ∈ {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)⁻¹} := fun α => by
    simp only [Set.mem_setOf_eq, ideleNorm_inv, ideleNorm_ratIdele_mul]
  by_cases ha : a ∈ {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)⁻¹}
  · rw [Set.indicator_of_mem ha]
    have hterm : ∀ α : ℚˣ, {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)}.indicator
        (fun b => (∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
          ((χ⁻¹ b : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ b : ℝ) : ℂ) ^ (1 - s - 1)) (ratIdele α * a)⁻¹ =
        (∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 (ratIdele α⁻¹ * a⁻¹)) * lowerUnipotent21 x * h)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
          ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ s := fun α => by
      rw [Set.indicator_of_mem ((hmem α).mpr ha), twist_inv_inv, twist_ratIdele_mul χ hχ, ideleNorm_inv_cpow,
        ideleNorm_ratIdele_mul, mul_inv, ratIdele_inv]
    simp_rw [hterm]
    rw [tsum_mul_right, tsum_mul_right]
    have hre := (Equiv.inv ℚˣ).tsum_eq fun β : ℚˣ =>
      ∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 (ratIdele β * a⁻¹)) * lowerUnipotent21 x * h)
        ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    simp only [Equiv.inv_apply] at hre
    rw [hre]
    ring
  · rw [Set.indicator_of_notMem ha]
    simp only [Set.indicator_of_notMem (fun hh => ha ((hmem _).mp hh)), tsum_zero]

private theorem coset_identity (c vol : ℂ) (hc : c * vol = 1) (t u sw sd : ℂ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hdag : vol * sw = ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) * sd) :
    c * (t * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ u * sd) =
      t * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (u - 1) * sw := by
  have hna : ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (TateGlobal.ideleNorm_pos a).ne'
  rw [Complex.cpow_sub _ _ hna, Complex.cpow_one]
  have hsd : sd = vol * sw / ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) := by
    rw [eq_div_iff hna, mul_comm sd, hdag]
  rw [hsd]
  linear_combination (t * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ u * sw / ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ)) * hc

private theorem measurableSet_small :
    MeasurableSet {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | TateGlobal.ideleNorm ℚ x < 1} :=
  (TateGlobal.continuous_ideleNorm ℚ).measurable measurableSet_Iio

private theorem measurableSet_large :
    MeasurableSet {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | 1 ≤ TateGlobal.ideleNorm ℚ x} :=
  (TateGlobal.continuous_ideleNorm ℚ).measurable measurableSet_Ici

private theorem folded_sides (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχ : IsAdmissibleTwist ℚ χ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (V : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hVc : Continuous V)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (σ₀' : ℝ)
    (hjoint : ∀ σ : ℝ, σ₀' ≤ σ → Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
      ‖V (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h)‖ * (TateGlobal.ideleNorm ℚ p.1 : ℝ) ^ (σ - 1))
      ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (c : ℂ) (hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1)
    (hdag : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∑' α : ℚˣ, ∫⁻ x : AdeleRing (𝓞 ℚ) ℚ,
          (‖V (iotaGL (diagUnitGL2 (ratIdele α * a⁻¹)) * lowerUnipotent21 x * h)‖₊ : ENNReal)
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) < ⊤ →
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
          ∑' α : ℚˣ, W (iotaGL (diagUnitGL2 (ratIdele α)) * (iotaGL (diagUnitGL2 a) * g)) =
        ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) *
          ∑' α : ℚˣ, ∫ x : AdeleRing (𝓞 ℚ) ℚ,
            V (iotaGL (diagUnitGL2 (ratIdele α * a⁻¹)) * lowerUnipotent21 x * h)
              ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))
    (s : ℂ) (P Q : ℝ → Prop)
    (hP : MeasurableSet {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)})
    (hQ : MeasurableSet {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Q (TateGlobal.ideleNorm ℚ x)})
    (hPQ : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, TateGlobal.ideleNorm ℚ a ≠ 1 →
      (P (TateGlobal.ideleNorm ℚ a) ↔ Q (TateGlobal.ideleNorm ℚ a)⁻¹))
    (hfwd : IntegrableOn (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        W (iotaGL (diagUnitGL2 x) * g) * ((χ x : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ x : ℝ) : ℂ) ^ (s - 1))
      {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)} (NumberField.Idele.idelicHaar ℚ))
    (hdual : IntegrableOn (fun b : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        (∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
          ((χ⁻¹ b : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ b : ℝ) : ℂ) ^ (1 - s - 1))
      {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Q (TateGlobal.ideleNorm ℚ x)} (NumberField.Idele.idelicHaar ℚ)) :
    (∫ a in {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)},
        W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
        ∂(NumberField.Idele.idelicHaar ℚ)) =
      c * ∫ b in {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Q (TateGlobal.ideleNorm ℚ x)},
        (∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
          ((χ⁻¹ b : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ b : ℝ) : ℂ) ^ (1 - s - 1)
        ∂(NumberField.Idele.idelicHaar ℚ) := by
  obtain ⟨Ω, hΩm, hΩ, -⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow ℚ
      (NumberField.Idele.idelicHaar ℚ)
  set G : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ := fun a =>
    ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) *
      ∑' α : ℚˣ, W (iotaGL (diagUnitGL2 (ratIdele α)) * (iotaGL (diagUnitGL2 a) * g)) with hG

  have hL : (∫ a in {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)},
        W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
        ∂(NumberField.Idele.idelicHaar ℚ)) =
      ∫ a in Ω, {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | P (TateGlobal.ideleNorm ℚ x)}.indicator G a
        ∂(NumberField.Idele.idelicHaar ℚ) := by
    rw [← integral_indicator hP, integral_eq_setIntegral_tsum Ω hΩ _ (hfwd.integrable_indicator hP)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => tsum_indicator_zeta_coset W χ hχ g s P a)

  have hR : (c * ∫ b in {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Q (TateGlobal.ideleNorm ℚ x)},
        (∫ x : AdeleRing (𝓞 ℚ) ℚ, V (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
          ((χ⁻¹ b : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ b : ℝ) : ℂ) ^ (1 - s - 1)
        ∂(NumberField.Idele.idelicHaar ℚ)) =
      ∫ a in Ω, {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Q (TateGlobal.ideleNorm ℚ x)⁻¹}.indicator G a
        ∂(NumberField.Idele.idelicHaar ℚ) := by
    rw [← integral_indicator hQ, ← integral_inv_eq_self _ (NumberField.Idele.idelicHaar ℚ),
      integral_eq_setIntegral_tsum Ω hΩ _ (hdual.integrable_indicator hQ).comp_inv, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_tsum_lintegral_lt_top V hVc h σ₀' hjoint Ω hΩ] with a hfin
    rw [tsum_indicator_inner_coset_inv V χ hχ h s Q a]
    by_cases ha : a ∈ {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Q (TateGlobal.ideleNorm ℚ x)⁻¹}
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, hG]
      exact coset_identity c _ hc _ s _ _ a (hdag a (by simpa only [enorm_eq_nnnorm] using hfin))
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero]
  rw [hL, hR]
  exact setIntegral_indicator_congr Ω hΩm hΩ _ _ hPQ G

end Fold

end LanglandsTunnell.CubicInduction.ZetaFunctionalEquation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell.CubicInduction.ZetaFunctionalEquation"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell"

end Auxiliary
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell.CubicInduction.ZetaFunctionalEquation"

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.LanglandsTunnell.CubicInduction in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (c : ℂ) (hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1) :
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ∀ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ →
        ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧ ∃ σ₁ σ₂ : ℝ,
          (∀ s : ℂ, σ₁ < s.re → E s = globalZeta30 X.whittaker χ s g) ∧
          (∀ s : ℂ, s.re < σ₂ → E s = c * globalZetaDual31 X.whittaker χ (1 - s) g) := by
  intro g χ hχ

  have hbridge : X.dualWhittaker = dualWhittakerFn3 X.whittaker :=
    CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 ψ D U gen X hX.automorphic hX.whittaker_eq hX.whittaker_law hX.expansion hX.dualWhittaker_eq hcont
  have hWd : IsGaugeMajorised3 ℚ (dualWhittakerFn3 X.whittaker) := hbridge ▸ hW'
  have hcontWd : Continuous (dualWhittakerFn3 X.whittaker) := hbridge ▸ hcontW'

  obtain ⟨E₁, hE₁d, hE₁b, hE₁, σ₁, hσ₁⟩ :=
    exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable X.whittaker hcontW hW χ hχ g
  obtain ⟨E₂, hE₂d, hE₂b, hE₂, σ₂, hσ₂⟩ :=
    exists_differentiable_boundedOnStrips_globalZeta31_eq_add_of_integrable (dualWhittakerFn3 X.whittaker)
      hcontWd hWd χ⁻¹ (ZetaFunctionalEquation.isAdmissibleTwist_inv χ hχ) (weylPrime3 * transposeInv3 g)

  obtain ⟨hsumW, -, -, -, hintW, -⟩ :=
    summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 X.whittaker hcontW hW
  obtain ⟨hsumWd, -, -, -, -, hjointWd⟩ :=
    summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 (dualWhittakerFn3 X.whittaker) hcontWd hWd
  obtain ⟨σ₀, hσ₀⟩ := hintW g
  obtain ⟨σ₀', hσ₀'⟩ := hjointWd (weylPrime3 * transposeInv3 g)
  have hχ' : IsAdmissibleTwist ℚ χ⁻¹ := ZetaFunctionalEquation.isAdmissibleTwist_inv χ hχ
  have hdag := fun (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) hfin =>
    ZetaFunctionalEquation.volume_mul_tsum_whittaker_eq_ideleNorm_mul_tsum_dual K ψ μ D U gen X S hX _hψ hcont hcontW
      hsumW hsumWd g a hfin
  have hlt := ZetaFunctionalEquation.measurableSet_small
  have hle := ZetaFunctionalEquation.measurableSet_large

  have hright : ∀ s : ℂ, max σ₁ σ₀ < s.re →
      (∫ a in {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | TateGlobal.ideleNorm ℚ a < 1},
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
            ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) ∂(NumberField.Idele.idelicHaar ℚ)) =
        c * E₂ (1 - s) := by
    intro s hs
    rw [hE₂ (1 - s)]
    refine ZetaFunctionalEquation.folded_sides X.whittaker χ hχ g (dualWhittakerFn3 X.whittaker) hcontWd
      (weylPrime3 * transposeInv3 g) σ₀' hσ₀' c hc hdag s (· < 1) (1 ≤ ·) hlt hle (fun a hne => ?_)
      (ZetaFunctionalEquation.integrable_zetaIntegrand X.whittaker hcontW χ hχ g σ₀ hσ₀ s
        ((le_max_right σ₁ σ₀).trans hs.le)).integrableOn
      (ZetaFunctionalEquation.integrableOn_innerIntegrand_large (dualWhittakerFn3 X.whittaker) hcontWd χ⁻¹ hχ'
        (weylPrime3 * transposeInv3 g) σ₀' hσ₀' (1 - s))
    have hpos := TateGlobal.ideleNorm_pos a
    exact ⟨fun hl => (one_le_inv₀ hpos).mpr hl.le, fun hl => lt_of_le_of_ne ((one_le_inv₀ hpos).mp hl) hne⟩
  have hleft : ∀ s : ℂ, max σ₂ σ₀' < (1 - s).re →
      c * (∫ a in {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | TateGlobal.ideleNorm ℚ a < 1},
          (∫ x : AdeleRing (𝓞 ℚ) ℚ,
              dualWhittakerFn3 X.whittaker
                (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))
              ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
            ((χ⁻¹ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (1 - s - 1)
          ∂(NumberField.Idele.idelicHaar ℚ)) =
        E₁ s := by
    intro s hs
    rw [hE₁ s]
    refine (ZetaFunctionalEquation.folded_sides X.whittaker χ hχ g (dualWhittakerFn3 X.whittaker) hcontWd
      (weylPrime3 * transposeInv3 g) σ₀' hσ₀' c hc hdag s (1 ≤ ·) (· < 1) hle hlt (fun a hne => ?_)
      (ZetaFunctionalEquation.integrableOn_zetaIntegrand_large X.whittaker hcontW χ hχ g σ₀ hσ₀ s)
      (ZetaFunctionalEquation.integrableOn_innerIntegrand_small (dualWhittakerFn3 X.whittaker) hcontWd χ⁻¹ hχ'
        (weylPrime3 * transposeInv3 g) σ₀' hσ₀' (1 - s) ((le_max_right σ₂ σ₀').trans hs.le))).symm
    have hpos := TateGlobal.ideleNorm_pos a
    exact ⟨fun hl => (inv_lt_one₀ hpos).mpr (lt_of_le_of_ne hl (Ne.symm hne)),
      fun hl => ((inv_lt_one₀ hpos).mp hl).le⟩
  refine ⟨fun s => E₁ s + c * E₂ (1 - s), ZetaFunctionalEquation.differentiable_combine E₁ E₂ hE₁d hE₂d c,
    ZetaFunctionalEquation.boundedOnStrips_combine E₁ E₂ hE₁b hE₂b c, max σ₁ σ₀, 1 - max σ₂ σ₀',
    fun s hs => ?_, fun s hs => ?_⟩
  · rw [hσ₁ s ((le_max_left σ₁ σ₀).trans_lt hs), hright s hs]
  · have hs' : max σ₂ σ₀' < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    rw [globalZetaDual31, hσ₂ (1 - s) ((le_max_left σ₂ σ₀').trans_lt hs'), mul_add, hleft s hs', add_comm]

end S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn (solution)
