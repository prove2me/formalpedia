-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ccdf1ca2-2b56-534d-8568-5ef2e192236a

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCubicInductionDataOn_twist_det
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_twist_det_localPackage
import Theorems.Thm_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det
import Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_twist_det_package
import Theorems.Thm_LanglandsTunnell_Converse_conductorExponentAt_localChar_eq_zero_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_LanglandsTunnell_Converse_isArchCompAt_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_NumberField_TateGlobal_eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_LanglandsTunnell_Converse_isAdmissibleTwist_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_NumberField_TateGlobal_isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_whittakerLoc_scalar_mul_eq_localChar_centralChar_mul
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3
import Theorems.Thm_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace
import Theorems.Thm_LanglandsTunnell_CubicInduction_psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_mem_span_of_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deepAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_le_conductorExponentAt_localChar_mul_comp_idelicNorm_of_hasConductorExponentAt_of_forall_le
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_of_finrank_eq_three
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt
import Theorems.Thm_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
import Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SpectralSide.instCompactSpaceMatrix ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange"
p2m_attr_erase "simp" "JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors LanglandsTunnell.CubicInduction.halfModulus2_one"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal UnramifiedWhittaker
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace G0

theorem exists_under_eq (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (v : HeightOneSpectrum (𝓞 ℚ)) : ∃ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 K)) := by
    set e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
    have hf : (algebraMap (𝓞 ℚ) (𝓞 K)).comp e.symm.toRingHom = Int.castRingHom (𝓞 K) :=
      RingHom.ext_int _ _
    have h2 : Function.Injective ((algebraMap (𝓞 ℚ) (𝓞 K)).comp e.symm.toRingHom) := by
      rw [hf]; exact Int.cast_injective
    intro a b hab
    apply e.injective
    apply h2
    show algebraMap (𝓞 ℚ) (𝓞 K) (e.symm (e a)) = algebraMap (𝓞 ℚ) (𝓞 K) (e.symm (e b))
    rw [e.symm_apply_apply, e.symm_apply_apply]; exact hab
  haveI : FaithfulSMul (𝓞 ℚ) (𝓞 K) := (faithfulSMul_iff_algebraMap_injective (𝓞 ℚ) (𝓞 K)).mpr hinj
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) v.asIdeal
  refine ⟨⟨Q, hQm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hQm (RingOfIntegers.not_isField K)⟩, ?_⟩
  exact HeightOneSpectrum.ext (hQo.over).symm

theorem not_isUnramifiedCharAt_of_one_le (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔓 : HeightOneSpectrum (𝓞 K))
    (h : 1 ≤ LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar μ 𝔓)) :
    ¬ IsUnramifiedCharAt μ 𝔓 := fun hu => by
  have := LanglandsTunnell.Converse.conductorExponentAt_localChar_eq_zero_of_isUnramifiedCharAt K μ 𝔓 hu
  omega

theorem isArchCompAt_mul_of_zero_zero (K : Type) [Field K] [NumberField K]
    (ν χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K) (u : ℂ) (a : ℤ)
    (hν : IsArchCompAt K ν w u a) (hχ : IsArchCompAt K χ w 0 0) :
    IsArchCompAt K (ν * χ) w u a := by
  intro x
  have h1 := hν x
  have h2 := hχ x
  simp only [mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h2
  have : archLocalChar (ν * χ) w x = archLocalChar ν w x * archLocalChar χ w x := rfl
  rw [this, Units.val_mul, h1, h2, mul_one]

theorem isArchCompAt_comp_idelicNorm_zero_zero (K : Type) [Field K] [NumberField K]
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (w : InfinitePlace K) :
    IsArchCompAt K (χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w 0 0 := by
  obtain ⟨h1, h2, -⟩ :=
    LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange ℚ K χA w 0
  have hv : (w.comap (algebraMap ℚ K)).IsReal := by
    rw [Subsingleton.elim (w.comap (algebraMap ℚ K)) Rat.infinitePlace]; exact Rat.isReal_infinitePlace
  by_cases hw : w.IsReal
  · exact h1 hw 0 (hχinf _ hv)
  · exact h2 (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw) hv 0 (hχinf _ hv)

theorem subsingleton_algebra_ringOfIntegers_rat (A : Type) [Ring A] :
    Subsingleton (Algebra (𝓞 ℚ) A) := by
  refine ⟨fun P Q => Algebra.algebra_ext P Q fun r => ?_⟩
  have key : ∀ f g : 𝓞 ℚ →+* A, f = g := by
    intro f g
    refine RingHom.ext fun x => ?_
    have hx : x = ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) :=
      Rat.ringOfIntegersEquiv.injective (by rw [map_intCast, Int.cast_id])
    rw [hx, map_intCast, map_intCast]
  exact RingHom.congr_fun (key (@algebraMap (𝓞 ℚ) A _ _ P) (@algebraMap (𝓞 ℚ) A _ _ Q)) r

theorem isAdmissibleTwist_mul (F : Type) [Field F] [NumberField F]
    (a b : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ha : IsAdmissibleTwist F a) (hb : IsAdmissibleTwist F b) :
    IsAdmissibleTwist F (a * b) := by
  obtain ⟨h1, h2, h3⟩ := ha
  obtain ⟨h1', h2', h3'⟩ := hb
  refine ⟨fun u => ?_, h2.mul h2', fun x => ?_⟩
  · rw [MonoidHom.mul_apply, h1 u, h1' u, one_mul]
  · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h3 x, h3' x, one_mul]

theorem isAdmissibleTwist_inv (F : Type) [Field F] [NumberField F]
    (a : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ha : IsAdmissibleTwist F a) :
    IsAdmissibleTwist F a⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := ha
  refine ⟨fun u => ?_, h2.inv, fun x => ?_⟩
  · rw [MonoidHom.inv_apply, h1 u, inv_one]
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h3 x, inv_one]

theorem monoidHom_eq_one_of_units_of_uniformizer (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (φ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hu : ∀ t : (v.adicCompletion F)ˣ, (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F → φ t = 1)
    (hϖ : φ (NumberField.AdelicLevel.uniformizerUnit F v) = 1) : φ = 1 := by
  ext x
  rw [MonoidHom.one_apply]
  set ϖ := NumberField.AdelicLevel.uniformizerUnit F v with hϖdef
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  set m : ℤ := WithZero.log (Valued.v (x : v.adicCompletion F)) with hmdef
  have hxm : Valued.v (x : v.adicCompletion F) = WithZero.exp m := (WithZero.exp_log hx0).symm
  have hu1 : Valued.v ((x * ϖ ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hxm, hϖdef,
      NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      smul_eq_mul, mul_neg, mul_one, add_neg_cancel, WithZero.exp_zero]
  have hmem : ((x * ϖ ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu1]
  have hmem' : (((x * ϖ ^ m)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one]
  have hx : x = (x * ϖ ^ m) * ϖ ^ (-m) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, map_mul, map_zpow, hu _ hmem hmem', hϖ, one_zpow, one_mul]

theorem comp_idelicNorm_uniformizerIdele_eq_pow
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (𝔓 : HeightOneSpectrum (𝓞 K))
    (hτ : IsUnramifiedCharAt τ (𝔓.under (𝓞 ℚ))) :
    (τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) (uniformizerIdele K 𝔓) =
      τ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI := subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  obtain ⟨t, ht1, hN⟩ :=
    M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit ℚ K 𝔓
  have hunit : τ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ)
      (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ)) t)) = 1 := by
    have h1 : (t : (𝔓.under (𝓞 ℚ)).adicCompletion ℚ) ∈ (𝔓.under (𝓞 ℚ)).adicCompletionIntegers ℚ := by
      simp only [HeightOneSpectrum.mem_adicCompletionIntegers, ht1, le_refl]
    have h2 : ((t⁻¹ : ((𝔓.under (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (𝔓.under (𝓞 ℚ)).adicCompletion ℚ) ∈
        (𝔓.under (𝓞 ℚ)).adicCompletionIntegers ℚ := by
      simp only [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, ht1, inv_one,
        le_refl]
    exact hτ t h1 h2
  rw [MonoidHom.comp_apply, hN, map_mul, map_pow, hunit, mul_one]

theorem eq_comp_idelicNorm_of_forall_apply_uniformizerIdele_eq
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsAdmissibleTwist ℚ η)
    (hwit : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) :
    μ = η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm := by
  haveI := subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  classical
  set N := (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm with hNdef
  obtain ⟨Sμ, hSμ⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous K μ hμ.2.1
  obtain ⟨Sη, hSη⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous ℚ η hη.2.1
  have hfib : ∀ p : HeightOneSpectrum (𝓞 ℚ), (primeFibre ℚ K p).Finite := fun p => by
    have hfin : (Ideal.primesOver p.asIdeal (𝓞 K)).Finite := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)
    refine (hfin.preimage (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    intro 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    refine ⟨𝔓.isPrime, ⟨?_⟩⟩
    rw [← h𝔓]
    rfl
  have hfin : {𝔓 : HeightOneSpectrum (𝓞 K) | 𝔓.under (𝓞 ℚ) ∈ (↑(SQ ∪ Sη) : Set (HeightOneSpectrum (𝓞 ℚ)))}.Finite := by
    have : {𝔓 : HeightOneSpectrum (𝓞 K) | 𝔓.under (𝓞 ℚ) ∈ (↑(SQ ∪ Sη) : Set (HeightOneSpectrum (𝓞 ℚ)))} =
        ⋃ p ∈ (↑(SQ ∪ Sη) : Set (HeightOneSpectrum (𝓞 ℚ))), primeFibre ℚ K p := by
      ext 𝔓; simp [mem_primeFibre]
    rw [this]
    exact Set.Finite.biUnion (Finset.finite_toSet _) fun p _ => hfib p
  set T : Finset (HeightOneSpectrum (𝓞 K)) := Sμ ∪ hfin.toFinset with hTdef
  have hηN : IsAdmissibleTwist K (η.comp N) :=
    LanglandsTunnell.Converse.isAdmissibleTwist_comp_idelicNorm_genuineBaseChange ℚ K η hη
  have hθ : IsAdmissibleTwist K (μ * (η.comp N)⁻¹) :=
    isAdmissibleTwist_mul K _ _ hμ (isAdmissibleTwist_inv K _ hηN)
  have hθ1 : μ * (η.comp N)⁻¹ = 1 := by
    refine NumberField.TateGlobal.eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one K _
      hθ.1 hθ.2.1 T fun 𝔓 h𝔓 => ?_
    have hμu : IsUnramifiedCharAt μ 𝔓 := hSμ 𝔓 fun h => h𝔓 (Finset.mem_union_left _ h)
    have hp : 𝔓.under (𝓞 ℚ) ∉ SQ ∪ Sη := fun h => h𝔓 (Finset.mem_union_right _ (hfin.mem_toFinset.mpr h))
    rw [Finset.mem_union, not_or] at hp
    have hηu : IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) := hSη _ hp.2
    have hNu : IsUnramifiedCharAt (η.comp N) 𝔓 :=
      (NumberField.TateGlobal.isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
        ℚ K η 𝔓 (hSQ 𝔓 hp.1)).mpr hηu
    refine monoidHom_eq_one_of_units_of_uniformizer K 𝔓 _ (fun t ht ht' => ?_) ?_
    · have : localChar (μ * (η.comp N)⁻¹) 𝔓 t = localChar μ 𝔓 t * (localChar (η.comp N) 𝔓 t)⁻¹ := rfl
      rw [this, hμu t ht ht', hNu t ht ht', inv_one, mul_one]
    · have h1 : μ (uniformizerIdele K 𝔓) = (η.comp N) (uniformizerIdele K 𝔓) := by
        rw [comp_idelicNorm_uniformizerIdele_eq_pow K η 𝔓 hηu]
        exact Units.val_injective (by rw [Units.val_pow_eq_pow_val]; exact hwit 𝔓 hμu hηu)
      show (μ * (η.comp N)⁻¹) (uniformizerIdele K 𝔓) = 1
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, mul_inv_cancel]
  exact mul_inv_eq_one.mp hθ1

theorem exists_finset_badPlaces (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hν : Continuous ν) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v, IsBadPlace K ν v → v ∈ T := by
  classical
  obtain ⟨Sν, hSν⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous K ν hν
  refine ⟨SQ ∪ Sν.image (fun 𝔓 => 𝔓.under (𝓞 ℚ)), fun v hv => ?_⟩
  rcases hv with ⟨𝔓, h𝔓, hne⟩ | ⟨𝔓, h𝔓, hram⟩
  · rw [mem_primeFibre] at h𝔓
    by_contra hv
    apply hne
    have := hSQ 𝔓 (fun h => hv (Finset.mem_union_left _ (h𝔓 ▸ h)))
    rwa [h𝔓] at this
  · rw [mem_primeFibre] at h𝔓
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨𝔓, by_contra fun h => hram (hSν 𝔓 h), h𝔓⟩)

theorem not_isRamifiedIn_of_not_mem (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ SQ) : ¬ IsRamifiedIn K v := by
  rintro ⟨𝔓, h𝔓, hne⟩
  rw [mem_primeFibre] at h𝔓
  apply hne
  have := hSQ 𝔓 (h𝔓 ▸ hv)
  rwa [h𝔓] at this

theorem continuous_centralChar (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ) (F : CubicInductionForm K pins ψ μ)
    (hcont : Continuous F.form) (hF : F.form ≠ 0) :
    Continuous ⇑F.centralChar := by
  obtain ⟨g₀, hg₀⟩ : ∃ g, F.form g ≠ 0 := Function.ne_iff.mp hF
  have hsc : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀ := by
    have hdiag : Continuous fun a : AdeleRing (𝓞 ℚ) ℚ => Matrix.diagonal fun _ : Fin 3 => a :=
      (continuous_pi fun _ : Fin 3 => continuous_id).matrix_diagonal
    have hs : Continuous ((Matrix.scalar (Fin 3)).toMonoidHom :
        AdeleRing (𝓞 ℚ) ℚ → Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
      hdiag.congr fun a => (Matrix.scalar_apply a).symm
    have h1 : Continuous (centralScalarGL 3 (𝓞 ℚ) ℚ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → AdelicGL 3 (𝓞 ℚ) ℚ) :=
      Continuous.units_map _ hs
    exact h1.mul continuous_const
  have hval : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((F.centralChar z : ℂˣ) : ℂ) := by
    have heq : (fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((F.centralChar z : ℂˣ) : ℂ)) =
        fun z => F.form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀) / F.form g₀ := by
      funext z
      rw [F.central z g₀, mul_div_cancel_right₀ _ hg₀]
    rw [heq]
    exact (hcont.comp hsc).div_const _
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have hinv : (fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (((F.centralChar z)⁻¹ : ℂˣ) : ℂ)) =
      fun z => ((F.centralChar z⁻¹ : ℂˣ) : ℂ) := by
    funext z
    rw [map_inv]
  rw [hinv]
  exact hval.comp continuous_inv

theorem isUnitaryChar_centralChar (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (pins : CarrierPins ℚ) (F : CubicInductionForm K pins ψ μ)
    (hcont : Continuous F.form) (hF : F.form ≠ 0)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSQ : ∀ v ∉ SQ, ¬ IsRamifiedIn K v) :
    IsUnitaryChar (𝓞 ℚ) ℚ F.centralChar := by
  haveI := subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  set ω := F.centralChar with hωdef
  have hωc : Continuous ⇑ω := continuous_centralChar K ψ μ pins F hcont hF

  set A : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ :=
    (Units.map (Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom).comp
      ((Units.map ((normHom : ℂ →*₀ ℝ) : ℂ →* ℝ)).comp ω) with hAdef
  have hAval : ∀ z, ((A z : ℂˣ) : ℂ) = ((‖((ω z : ℂˣ) : ℂ)‖ : ℝ) : ℂ) := fun z => rfl
  have hAic : IsIdeleClassChar (𝓞 ℚ) ℚ A := fun u => by
    apply Units.ext
    rw [hAval, F.centralChar_ideleClass u, Units.val_one, norm_one, Complex.ofReal_one]
  have hAc : Continuous ⇑A :=
    ((Continuous.units_map _ Complex.continuous_ofReal).comp
      (Continuous.units_map _ continuous_norm)).comp hωc
  have hX := F.isCubicInductionDataOn {v | IsBadPlace K μ v} fun v hv => hv
  have hloc : ∀ v ∉ SQ, localChar A v = 1 := by
    intro v hv
    obtain ⟨η, -, hη2, hωv⟩ :=
      LanglandsTunnell.CubicInduction.exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
        K hdeg ψ μ hμ pins F.toData hX hcont hF v (hSQ v hv)
    refine MonoidHom.ext fun t => Units.ext ?_
    rw [MonoidHom.one_apply, Units.val_one]
    show ((A _ : ℂˣ) : ℂ) = 1
    rw [hAval]
    have h1 : ((‖((localChar F.centralChar v t : ℂˣ) : ℂ)‖ : ℝ) : ℂ) = 1 := by
      have hωv' := hωv t
      simp only [CubicInductionForm.toData] at hωv'
      rw [hωv', norm_mul]
      have hη : ‖((η t : ℂˣ) : ℂ)‖ = 1 := by
        have h2 : ‖((η t : ℂˣ) : ℂ)‖ * ‖((η t : ℂˣ) : ℂ)‖ = 1 := by
          rw [← norm_mul, ← Units.val_mul, hη2 t, Units.val_one, norm_one]
        nlinarith [norm_nonneg ((η t : ℂˣ) : ℂ)]
      have hπ : ‖∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
            (Units.map (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K)).toMonoidHom t) : ℂˣ) : ℂ)‖ = 1 := by
        refine finprod_induction (fun x : ℂ => ‖x‖ = 1) norm_one (fun x y hx hy => by show ‖x * y‖ = 1; rw [norm_mul]; rw [show ‖x‖ = 1 from hx, show ‖y‖ = 1 from hy, mul_one]) ?_
        intro w
        exact hμ.2.2 _
      rw [hη, hπ, mul_one, Complex.ofReal_one]
    exact h1
  have hA1 := NumberField.TateGlobal.eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one ℚ A hAic hAc
    SQ hloc
  intro z
  have := congrArg (fun f : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ => ((f z : ℂˣ) : ℂ)) hA1
  simp only [MonoidHom.one_apply, Units.val_one] at this
  rw [hAval] at this
  exact_mod_cast this

theorem exists_open_subgroup_localChar_eq_one (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχA : IsAdmissibleTwist ℚ χA) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ U₀ : Subgroup (v.adicCompletion ℚ)ˣ, IsOpen (U₀ : Set (v.adicCompletion ℚ)ˣ) ∧
      ∀ u ∈ U₀, NumberField.TateGlobal.localChar χA v u = 1 := by
  obtain ⟨n, hn⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ v
    (NumberField.TateGlobal.localChar χA v) (NumberField.TateGlobal.continuous_localChar χA hχA.2.1 v)
  refine ⟨(NumberField.TateGlobal.localChar χA v).ker, ?_, fun u hu => (MonoidHom.mem_ker).mp hu⟩
  apply Subgroup.isOpen_of_mem_nhds (g := 1)

  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective ℚ (WithZero.exp (-((n : ℤ) + 1)))
  have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v a := by
    rw [ha]; exact zero_lt_iff.mpr WithZero.exp_ne_zero
  have hball : IsOpen {x : v.adicCompletion ℚ | Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))} := by
    have hset : {x : v.adicCompletion ℚ | Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))} =
        (fun x => a⁻¹ * (x - 1)) ⁻¹' {y : v.adicCompletion ℚ | Valued.v y ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.map_mul, map_inv₀, ← ha]
      rw [inv_mul_le_iff₀ hpos, mul_one]
    rw [hset]
    exact (Valued.isClopen_integer (v.adicCompletion ℚ)).isOpen.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  have hU : IsOpen {u : (v.adicCompletion ℚ)ˣ |
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((n : ℤ) + 1))} :=
    hball.preimage Units.continuous_val
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · show Valued.v (((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((n : ℤ) + 1))
    rw [Units.val_one, sub_self, map_zero]; exact zero_le'
  intro u hu
  have hu' : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((n : ℤ) + 1)) := hu
  have hlt : Valued.v ((u : v.adicCompletion ℚ) - 1) < 1 :=
    lt_of_le_of_lt hu' (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hv1 : Valued.v (u : v.adicCompletion ℚ) = 1 := by
    have e : (u : v.adicCompletion ℚ) = 1 + ((u : v.adicCompletion ℚ) - 1) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  have hmem : u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v n :=
    ⟨hv1, Or.inr (hu'.trans (WithZero.exp_le_exp.mpr (by omega)))⟩
  exact (MonoidHom.mem_ker).mpr (hn.1 u hmem)

theorem isUnramifiedCharAt_mul (F : Type) [Field F] [NumberField F] (τ σ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) (hτ : IsUnramifiedCharAt τ v) (hσ : IsUnramifiedCharAt σ v) :
    IsUnramifiedCharAt (τ * σ) v := by
  intro t ht ht'
  have : localChar (τ * σ) v t = localChar τ v t * localChar σ v t := rfl
  rw [this, hτ t ht ht', hσ t ht ht', one_mul]

theorem det_centralGen (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det (centralGen v) = NumberField.AdelicLevel.uniformizerUnit ℚ v ^ 3 := by
  apply Units.ext
  simp [centralGen, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal, Fin.prod_univ_three, varpi, pow_three,
    mul_assoc]

theorem inducedE3_twist (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (hdeg : Module.finrank ℚ K = 3)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : IsAdmissibleTwist ℚ χA)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hχp : IsUnramifiedCharAt χA p)
    (W : LocalGL3 p → ℂ) (hW : IsInducedSphericalAt (inducedCoeff K ν) p (localMaximalCompact3 (𝓞 ℚ) ℚ p) W)
    (hW1 : W 1 = 1) :
    inducedE3 ℚ (inducedCoeff K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) p =
      ((localChar χA p (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂˣ) : ℂ) ^ 3 * inducedE3 ℚ (inducedCoeff K ν) p := by
  have hS := (LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt K hdeg ν χA hχA
    p hχp).2.2 W hW
  have h1 := hS.2.2.2 1
  have h2 := hW.2.2.2 1
  simp only [mul_one] at h1 h2
  rw [map_one, map_one, Units.val_one, one_mul, hW1, mul_one, h2, hW1, mul_one, det_centralGen, map_pow,
    Units.val_pow_eq_pow_val] at h1
  exact h1.symm

theorem isArchCompAt_of_mul_of_zero_zero (K : Type) [Field K] [NumberField K]
    (ν χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K) (u : ℂ) (a : ℤ)
    (hνχ : IsArchCompAt K (ν * χ) w u a) (hχ : IsArchCompAt K χ w 0 0) :
    IsArchCompAt K ν w u a := by
  intro x
  have h1 := hνχ x
  have h2 := hχ x
  simp only [mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h2
  have e : archLocalChar (ν * χ) w x = archLocalChar ν w x * archLocalChar χ w x := rfl
  rw [e, Units.val_mul, h2, mul_one] at h1
  exact h1

theorem isArchCompAt_inv_zero_zero (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K) (hχ : IsArchCompAt K χ w 0 0) :
    IsArchCompAt K χ⁻¹ w 0 0 := by
  intro x
  have h := hχ x
  simp only [mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h ⊢
  have : archLocalChar χ⁻¹ w x = (archLocalChar χ w x)⁻¹ := rfl
  rw [this, Units.val_inv_eq_inv_val, h, inv_one]

theorem heckeDatum_archFactor_eq (F : Type) [Field F] [NumberField F] (χ χ' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace F, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace F, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ) :
    (LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).archFactor =
      (LanglandsTunnell.HeckeTate.heckeDatum F χ' uR aR uC kC).archFactor := by
  funext s
  simp only [LanglandsTunnell.LDatum.archFactor, LanglandsTunnell.HeckeTate.heckeDatum]

theorem heckeDatum_archFactorDual_eq (F : Type) [Field F] [NumberField F] (χ χ' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace F, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace F, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ) :
    (LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).archFactorDual =
      (LanglandsTunnell.HeckeTate.heckeDatum F χ' uR aR uC kC).archFactorDual := by
  funext s
  simp only [LanglandsTunnell.LDatum.archFactorDual, LanglandsTunnell.HeckeTate.heckeDatum]

theorem self_mem_gl3CyclicSubspace {F : Type*} [CommRing F] (W : GL (Fin 3) F → ℂ) : W ∈ gl3CyclicSubspace W := by
  refine Submodule.subset_span ⟨1, ?_⟩
  funext x
  simp [gl3AmbientRightTranslate_apply]

theorem gl3CyclicSubspace_le_of_mem {F : Type*} [CommRing F] {W X Y : GL (Fin 3) F → ℂ}
    (hX : X ∈ gl3CyclicSubspace W) (hY : Y ∈ gl3CyclicSubspace X) : Y ∈ gl3CyclicSubspace W := by
  have hle : gl3CyclicSubspace X ≤ gl3CyclicSubspace W := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h hX
  exact hle hY

end G0

section IDXHelpers

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel

namespace IDX

theorem primeFibre_finite (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 ℚ)) :
    (primeFibre ℚ K p).Finite := by
  have hfin : (Ideal.primesOver p.asIdeal (𝓞 K)).Finite :=
    IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)
  refine (hfin.preimage (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal)
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  intro 𝔓 h𝔓
  rw [mem_primeFibre] at h𝔓
  refine ⟨𝔓.isPrime, ⟨?_⟩⟩
  rw [← h𝔓]
  rfl

theorem primeFibre_nonempty (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ primeFibre ℚ K p := by
  have hfund := Ideal.sum_ramification_inertia (𝓞 K) ℚ K p.ne_bot
  have hne : (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hfund
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  obtain ⟨P, hP⟩ := hne
  have hP' := (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 K)).mp hP
  refine ⟨⟨P, hP'.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot ⟨hP'.1, hP'.2⟩⟩, ?_⟩
  rw [mem_primeFibre]
  exact HeightOneSpectrum.ext hP'.2.over.symm

theorem exists_nat_cast_eq_finsum_pinnedExp (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ ℓ : ℕ, (ℓ : ℤ) = ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      LanglandsTunnell.Converse.pinnedExp K χ 𝔓 := by
  have hnn : 0 ≤ ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      LanglandsTunnell.Converse.pinnedExp K χ 𝔓 := by
    refine finsum_mem_induction (fun x : ℤ => 0 ≤ x) le_rfl (fun _ _ hx hy => add_nonneg hx hy) ?_
    intro 𝔓 _
    refine mul_nonneg (Int.natCast_nonneg _) ?_
    unfold LanglandsTunnell.Converse.pinnedExp
    refine add_nonneg (Int.natCast_nonneg _) ?_
    have h := LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal K 𝔓
    have h2 := FractionalIdeal.count_coe_nonneg K 𝔓 (differentIdeal ℤ (𝓞 K))
    rw [← h] at h2
    exact h2
  exact ⟨_, (Int.toNat_of_nonneg hnn)⟩

open scoped Classical in

theorem finprod_primeFibre_cpow_zpow_eq_cpow (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (pe : HeightOneSpectrum (𝓞 K) → ℤ) (ℓ : ℕ)
    (hℓ : (ℓ : ℤ) = ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * pe 𝔓) (s : ℂ) :
    ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (pe 𝔓)) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) := by
  have hfin := primeFibre_finite K v
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ideal.absNorm_eq_zero_iff.ne]
    exact v.ne_bot

  have hfac : ∀ 𝔓 ∈ primeFibre ℚ K v,
      ((((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (pe 𝔓)) =
        (Ideal.absNorm v.asIdeal : ℂ) ^ (((v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * pe 𝔓 : ℤ) * ((1 : ℂ) / 2 - s)) := by
    intro 𝔓 h𝔓
    have h : 𝔓.under (𝓞 ℚ) = v := (mem_primeFibre ℚ v 𝔓).mp h𝔓
    haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h]; rfl⟩
    rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal v.asIdeal v.isPrime v.ne_bot, Nat.cast_pow]
    symm
    rw [show ((((v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * pe 𝔓 : ℤ) : ℂ) * ((1 : ℂ) / 2 - s)) =
        (pe 𝔓 : ℂ) * ((v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℕ) * ((1 : ℂ) / 2 - s)) by push_cast; ring,
      Complex.cpow_int_mul,
      Complex.cpow_nat_mul' (by rw [Complex.natCast_arg, mul_zero]; exact neg_lt_zero.mpr Real.pi_pos)
        (by rw [Complex.natCast_arg, mul_zero]; exact Real.pi_pos.le)]
  rw [finprod_mem_congr rfl hfac, finprod_mem_eq_finite_toFinset_prod _ hfin]
  rw [show ((ℓ : ℂ)) = ((ℓ : ℤ) : ℂ) by push_cast; rfl, hℓ, finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  rw [Finset.sum_mul]

  induction hfin.toFinset using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [Finset.prod_insert haT, Finset.sum_insert haT, Complex.cpow_add _ _ hN0, ih]

theorem asIdeal_mem_primesOver_of_mem_primeFibre (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 ℚ))
    {𝔓 : HeightOneSpectrum (𝓞 F)} (h : 𝔓 ∈ primeFibre ℚ F p) :
    𝔓.asIdeal ∈ p.asIdeal.primesOver (𝓞 F) := by
  rw [mem_primeFibre] at h
  refine ⟨𝔓.isPrime, ⟨?_⟩⟩
  rw [← h]
  rfl

theorem image_asIdeal_primeFibre (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 ℚ)) :
    HeightOneSpectrum.asIdeal '' primeFibre ℚ F p = p.asIdeal.primesOver (𝓞 F) := by
  ext Q
  constructor
  · rintro ⟨𝔓, h𝔓, rfl⟩
    exact asIdeal_mem_primesOver_of_mem_primeFibre F p h𝔓
  · intro hQ
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver p.asIdeal := hQ.2
    refine ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ⟩, ?_, rfl⟩
    rw [mem_primeFibre]
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def Q p.asIdeal).symm

theorem finsum_fibre_ramificationIdx_mul_inertiaDeg (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal =
      Module.finrank ℚ F := by
  calc ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal
      = ∑ᶠ Q ∈ HeightOneSpectrum.asIdeal '' primeFibre ℚ F p,
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q :=
        (finsum_mem_image (f := fun Q : Ideal (𝓞 F) => p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q)
          HeightOneSpectrum.asIdeal_injective.injOn).symm
    _ = ∑ᶠ Q ∈ p.asIdeal.primesOver (𝓞 F), p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [image_asIdeal_primeFibre]
    _ = ∑ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 F),
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [← IsDedekindDomain.coe_primesOverFinset p.ne_bot (𝓞 F), finsum_mem_coe_finset]
    _ = Module.finrank ℚ F := Ideal.sum_ramification_inertia (𝓞 F) ℚ F p.ne_bot

theorem cpow_bookkeeping (q : ℂ) (hq : q ≠ 0) (ℓ : ℕ) (m n : ℤ) (hm : m = -(ℓ : ℤ)) (s : ℂ) :
    q ^ ((n : ℂ) * s) * q ^ ((ℓ : ℂ) * (1 / 2 - s)) = q ^ ((ℓ : ℂ) / 2) * q ^ (((m : ℂ) + (n : ℂ)) * s) := by
  subst hm
  rw [← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
  congr 1
  push_cast
  ring

theorem cpow_bookkeeping' (q : ℂ) (hq : q ≠ 0) (ℓ : ℕ) (m : ℤ) (hm : m = -(ℓ : ℤ)) (s : ℂ) :
    q ^ ((ℓ : ℂ) / 2) * q ^ ((m : ℂ) * s) = q ^ ((ℓ : ℂ) * (1 / 2 - s)) := by
  subst hm
  rw [← Complex.cpow_add _ _ hq]
  congr 1
  push_cast
  ring

end IDX

end IDXHelpers

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt ν 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((ν (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))

    (p : HeightOneSpectrum (𝓞 ℚ))
    (ξA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hξA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ξA)
    (hξoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → IsUnramifiedCharAt ξA v)
    (hξinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ ξA v 0 0)
    (B c₀ : ℕ)
    (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ξA p) B)
    (hνc : ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar ν w) c)
    (hB : c₀ + 12 ≤ B)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K ν w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K ν w (uC w hw) (kC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (ω₃ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω₃ : IsAdmissibleTwist ℚ ω₃ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K ν p →
        IsUnramifiedCharAt ω₃ p ∧ eulerCoeff ℚ ω₃ p = inducedE3 ℚ (inducedCoeff K ν) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K ν w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K ν w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω₃ v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (hWarch :
      Warch ≠ 0 ∧ IsKFinite Warch ∧
      (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf Warch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        Warch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω₃ (E z) : ℂˣ) : ℂ) * Warch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => Warch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => Warch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K ν (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K ν (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => Warch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => Warch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((ω₃ (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K ν (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0)

    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hArchEq : F.whittakerArch = Warch)
    (hEss :
      (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K ν v → ¬ IsRamifiedIn K v →
        psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ →
        ∃ W ∈ gl3CyclicSubspace (F.whittakerLoc v), IsGL3PsiWhittakerFn (psiLoc ψ v) W ∧ W ≠ 0 ∧
          (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K ν v), ∀ g, W (g * k) = W g) ∧
          W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v W))
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K ν v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K ν v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))

    (hadm : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K ν v →
      ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace (F.whittakerLoc v),
          (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) :
    ∃ (ε : ℂ) (ℓ : ℕ), ε ≠ 0 ∧

      (ℓ : ℤ) = ∑ᶠ 𝔓 ∈ primeFibre ℚ K p, (p.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
        LanglandsTunnell.Converse.pinnedExp K (ν * ξA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 ∧
      B ≤ ℓ ∧
      (ℓ : ℤ) ≤ 3 * (B : ℤ) + ∑ᶠ 𝔓 ∈ primeFibre ℚ K p, (p.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
        LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓) ∧
      ∀ W ∈ gl3CyclicSubspace
          (fun g : LocalGL3 p => ((NumberField.TateGlobal.localChar ξA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            F.whittakerLoc p g),
      ∀ g : LocalGL3 p,
        (letI := localBorel ℚ p
         ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
          (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
            P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W 1 g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W 1 s g =
              ((1 : Polynomial ℂ).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            (selfDualHaarAt ℚ p) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
          ∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
                W 1 (1 - s) g =
              ((1 : Polynomial ℂ).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
                ((ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)) := by
  classical

  haveI := G0.subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _

  set μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ν * ξA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm with hμν
  have hμ : IsAdmissibleTwist K μ := by
    rw [hμν]
    exact G0.isAdmissibleTwist_mul K _ _ hνadm
      (LanglandsTunnell.Converse.isAdmissibleTwist_comp_idelicNorm_genuineBaseChange ℚ K ξA hξA)
  set SQ : Finset (HeightOneSpectrum (𝓞 ℚ)) := {p} with hSQdef
  have hpSQ : p ∈ SQ := by rw [hSQdef]; exact Finset.mem_singleton_self p
  have hSQp : ∀ v, v ∈ SQ → v = p := fun v hv => by rw [hSQdef] at hv; exact Finset.mem_singleton.mp hv
  have hξoff' : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt ξA v := fun v hv =>
    hξoff v (fun h => hv (h ▸ hpSQ))

  have hbadfin : {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K ν v}.Finite :=
    LanglandsTunnell.CubicInduction.finite_setOf_isBadPlace_of_continuous K ν hνadm.2.1
  obtain ⟨Tν, hTν⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v, IsBadPlace K ν v → v ∈ T :=
    ⟨hbadfin.toFinset, fun v hv => hbadfin.mem_toFinset.mpr hv⟩
  have hSQ' : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tν →
      Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1 := fun 𝔓 h𝔓 => by
    by_contra hne
    exact h𝔓 (hTν _ (Or.inl ⟨𝔓, (mem_primeFibre ℚ _ 𝔓).mpr rfl, hne⟩))

  have hDTR : ∀ w ∈ primeFibre ℚ K p, B ≤ LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) := by
    rw [hμν]
    exact LanglandsTunnell.CubicInduction.le_conductorExponentAt_localChar_mul_comp_idelicNorm_of_hasConductorExponentAt_of_forall_le
      K _hdeg ν ξA p B c₀ hξB hνc hB

  have hωu : IsUnitaryChar (𝓞 ℚ) ℚ F.centralChar :=
    G0.isUnitaryChar_centralChar K _hdeg ψ ν hνadm _ F hFc hF0.1 Tν
      (fun v hv hram => hv (hTν v (Or.inl hram)))

  have hADMν : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K ν v →
      ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace (F.whittakerLoc v),
          (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) :=
    hadm

  set X : CubicInductionData :=
    { form := fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((ξA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x
      whittaker := fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((ξA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x
      whittakerLoc := fun (v : HeightOneSpectrum (𝓞 ℚ)) (y : LocalGL3 v) =>
        ((NumberField.TateGlobal.localChar ξA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * F.whittakerLoc v y
      whittakerArch := F.whittakerArch
      centralChar := F.centralChar * ξA ^ 3
      dualWhittaker := fun x : AdelicGL 3 (𝓞 ℚ) ℚ =>
        ((ξA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x } with hXdef

  have hdeep : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ SQ →
      1 ≤ LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar μ 𝔓) := by
    intro 𝔓 h𝔓
    have h := hDTR 𝔓 ((mem_primeFibre ℚ p 𝔓).mpr (hSQp _ h𝔓))
    omega
  have hSQbad : ∀ v ∈ SQ, IsBadPlace K μ v := by
    intro v hv
    obtain ⟨𝔓, h𝔓⟩ := G0.exists_under_eq K v
    exact Or.inr ⟨𝔓, (mem_primeFibre ℚ v 𝔓).mpr h𝔓,
      G0.not_isUnramifiedCharAt_of_one_le K μ 𝔓 (hdeep 𝔓 (h𝔓 ▸ hv))⟩

  have hSν : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K ν v → v ∈ {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v} := by
    intro v hbad
    show IsBadPlace K μ v
    by_cases hv : v ∈ SQ
    · exact hSQbad v hv
    · rw [hμν]
      exact (LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt K _hdeg ν ξA hξA
        v (hξoff' v hv)).1.mpr hbad
  have hSχ : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsUnramifiedCharAt ξA v → v ∈ {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v} := by
    intro v hram
    show IsBadPlace K μ v
    by_contra hne
    exact hram (hξoff' v fun hv => hne (hSQbad v hv))

  have hX : IsCubicInductionDataOn K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ μ
      {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v} X := by
    have h := LanglandsTunnell.CubicInduction.isCubicInductionDataOn_twist_det K _hdeg _ ψ ν hνadm F ξA hξA hξinf
      {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v} hSν hSχ
    rw [← hμν] at h
    exact h

  have hX0 : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v) := by
    refine ⟨fun h0 => hF0.1 (funext fun x => ?_), fun v hv hlv => ?_⟩
    · have := congr_fun h0 x
      simp only [hXdef, Pi.zero_apply, mul_eq_zero, Units.ne_zero, false_or] at this
      exact this
    · have hvSQ : v ∉ SQ := fun h => hv (hSQbad v h)
      have hχv := hξoff' v hvSQ
      have hTS := LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt K _hdeg ν ξA hξA v hχv
      have hνv : ¬ IsBadPlace K ν v := fun h => hv (hμν ▸ hTS.1.mpr h)
      have hKv : ¬ IsRamifiedIn K v := fun h => hνv (Or.inl h)
      obtain ⟨h1, h2⟩ := hF0.2 v hKv hlv
      refine ⟨?_, ?_⟩
      · show ((NumberField.TateGlobal.localChar ξA v (Matrix.GeneralLinearGroup.det (1 : LocalGL3 v)) : ℂˣ) : ℂ) *
            F.whittakerLoc v 1 = 1
        rw [map_one, map_one, Units.val_one, one_mul, h1]
      · have h3 := hTS.2.1 (F.whittakerLoc v) h2
        rw [← hμν] at h3
        exact h3

  obtain ⟨-, -, -, -, -, hC1, hC2, hC3, hG1, hG2, -, -⟩ :=
    LanglandsTunnell.CubicInduction.CubicInductionForm.twist_det_package K _ ψ ν F ξA hξA hξinf

  have hstabF : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g := by
    intro v
    by_cases hv : IsBadPlace K ν v
    · exact (hBad {v}).1 v (Finset.mem_singleton_self v) hv
    · exact ⟨localMaximalCompact3 (𝓞 ℚ) ℚ v, LanglandsTunnell.CubicInduction.isOpen_localMaximalCompact3 (𝓞 ℚ) ℚ v,
        fun k hk g => (F.spherical v hv).1 g k hk⟩
  have hirrF : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
      F.whittakerLoc v ∈ gl3CyclicSubspace W := by
    intro v
    by_cases hv : IsBadPlace K ν v
    · exact (hBad {v}).2 v (Finset.mem_singleton_self v) hv
    · exact LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
        K _hdeg ν hνadm.2.2 v (F.whittakerLoc v) (F.spherical v hv) (psiLoc ψ v) (F.whittakerLoc_law v) (hlev v)
        (LanglandsTunnell.CubicInduction.psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar ψ hψ v).1

  have hBadμ : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
        X.whittakerLoc v ∈ gl3CyclicSubspace W) := by
    intro T
    refine ⟨fun v _ _ => ?_, fun v _ _ W hW hW0 => ?_⟩
    · obtain ⟨U₀, hU₀, hχU₀⟩ := G0.exists_open_subgroup_localChar_eq_one ξA hξA v
      exact (LanglandsTunnell.CubicInduction.twist_det_localPackage v (psiLoc ψ v) (localChar ξA v) U₀ hU₀ hχU₀
        (fun z => hξA.2.2 _) (F.whittakerLoc v)).2.2.1 (hstabF v)
    · obtain ⟨-, h2, -, -⟩ :=
        LanglandsTunnell.CubicInduction.mem_gl3CyclicSubspace_twist_det v (localChar ξA v) (F.whittakerLoc v)
      obtain ⟨W', hW', rfl⟩ := h2 W hW
      obtain ⟨h1', -, h3', -⟩ :=
        LanglandsTunnell.CubicInduction.mem_gl3CyclicSubspace_twist_det v (localChar ξA v) W'
      have hW'0 : W' ≠ 0 := fun h => hW0 (h3'.mpr h)
      exact h1' _ (hirrF v W' hW' hW'0)
  have hadmμ : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w →
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)) := by
    intro w _ Uw hUw
    obtain ⟨U₀, hU₀, hχU₀⟩ := G0.exists_open_subgroup_localChar_eq_one ξA hξA w
    refine (LanglandsTunnell.CubicInduction.twist_det_localPackage w (psiLoc ψ w) (localChar ξA w) U₀ hU₀ hχU₀
      (fun z => hξA.2.2 _) (F.whittakerLoc w)).1 ?_ Uw hUw
    by_cases hνw : IsBadPlace K ν w
    · exact hADMν w hνw
    · exact LanglandsTunnell.CubicInduction.exists_finset_mem_span_of_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
        K _hdeg ν hνadm.2.2 w (F.whittakerLoc w) (F.spherical w hνw) (psiLoc ψ w) (F.whittakerLoc_law w) (hlev w)
        (LanglandsTunnell.CubicInduction.psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar ψ hψ w).1
  have hcent : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w →
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((NumberField.TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((NumberField.TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h := by
    intro w _
    obtain ⟨U₀, hU₀, hχU₀⟩ := G0.exists_open_subgroup_localChar_eq_one ξA hξA w
    have hsc := LanglandsTunnell.CubicInduction.CubicInductionForm.whittakerLoc_scalar_mul_eq_localChar_centralChar_mul
      K _ ψ ν hbadfin F hF0.1 w
    have hωw : ∀ z : (w.adicCompletion ℚ)ˣ, ‖((localChar F.centralChar w z : ℂˣ) : ℂ)‖ = 1 := fun z => hωu _
    have hd := (LanglandsTunnell.CubicInduction.twist_det_localPackage w (psiLoc ψ w) (localChar ξA w) U₀ hU₀ hχU₀
      (fun z => hξA.2.2 _) (F.whittakerLoc w)).2.2.2 (localChar F.centralChar w) hωw hsc
    have hloc : localChar X.centralChar w = localChar F.centralChar w * localChar ξA w ^ 3 :=
      MonoidHom.ext fun _ => rfl
    rw [hloc]
    exact hd

  have hoffμ : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
    rintro ⟨η, hη, hwit⟩
    apply hoff
    have hμeq := G0.eq_comp_idelicNorm_of_forall_apply_uniformizerIdele_eq K Tν hSQ' μ hμ η hη hwit
    refine ⟨η * ξA⁻¹, G0.isAdmissibleTwist_mul ℚ _ _ hη (G0.isAdmissibleTwist_inv ℚ _ hξA), fun 𝔓 _ hη' => ?_⟩
    have hν : ν = (η * ξA⁻¹).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm := by
      rw [MonoidHom.mul_comp, MonoidHom.inv_comp, ← hμeq, hμν, mul_inv_cancel_right]
    have h2 := G0.comp_idelicNorm_uniformizerIdele_eq_pow K (η * ξA⁻¹) 𝔓 hη'
    rw [← hν] at h2
    rw [h2, Units.val_pow_eq_pow_val]
  have hcRμ : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ) := fun w hw => by
    rw [hμν]
    exact G0.isArchCompAt_mul_of_zero_zero K ν _ w _ _ (hcR w hw) (G0.isArchCompAt_comp_idelicNorm_zero_zero K ξA hξinf w)
  have hcCμ : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw) := fun w hw => by
    rw [hμν]
    exact G0.isArchCompAt_mul_of_zero_zero K ν _ w _ _ (hcC w hw) (G0.isArchCompAt_comp_idelicNorm_zero_zero K ξA hξinf w)

  have hωμ : IsAdmissibleTwist ℚ (ω₃ * ξA ^ 3) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt (ω₃ * ξA ^ 3) p ∧ eulerCoeff ℚ (ω₃ * ξA ^ 3) p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ (ω₃ * ξA ^ 3) v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))) := by

    refine ⟨?_, fun p hp => ?_, fun uR' aR' uC' kC' hR hC v hv => ?_⟩
    · rw [pow_three]
      exact G0.isAdmissibleTwist_mul ℚ _ _ hω₃.1
        (G0.isAdmissibleTwist_mul ℚ _ _ hξA (G0.isAdmissibleTwist_mul ℚ _ _ hξA hξA))
    · have hpSQ : p ∉ SQ := fun h => hp (hSQbad p h)
      have hχp := hξoff' p hpSQ
      have hTS := LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt K _hdeg ν ξA hξA p hχp
      have hνp : ¬ IsBadPlace K ν p := fun h => hp (hμν ▸ hTS.1.mpr h)
      obtain ⟨hωp, he⟩ := hω₃.2.1 p hνp
      have hχ3 : IsUnramifiedCharAt (ξA ^ 3) p := by
        rw [pow_three]
        exact G0.isUnramifiedCharAt_mul ℚ _ _ p hχp (G0.isUnramifiedCharAt_mul ℚ _ _ p hχp hχp)
      have hu : IsUnramifiedCharAt (ω₃ * ξA ^ 3) p := G0.isUnramifiedCharAt_mul ℚ _ _ p hωp hχ3
      refine ⟨hu, ?_⟩
      have hKp : ¬ IsRamifiedIn K p := fun h => hνp (Or.inl h)
      obtain ⟨h1, -⟩ := hF0.2 p hKp (hlev p)
      have he3 := G0.inducedE3_twist K _hdeg ν ξA hξA p hχp (F.whittakerLoc p) (F.spherical p hνp) h1
      rw [eulerCoeff, if_pos hωp] at he
      rw [hμν, he3, eulerCoeff, if_pos hu, ← he, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul,
        Units.val_pow_eq_pow_val, mul_comm]
      rfl
    · have hN0 := G0.isArchCompAt_comp_idelicNorm_zero_zero K ξA hξinf
      have hR' : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K ν w (uR' w hw) ((aR' w hw).val : ℤ) := fun w hw =>
        G0.isArchCompAt_of_mul_of_zero_zero K ν _ w _ _ (hμν ▸ hR w hw) (hN0 w)
      have hC' : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K ν w (uC' w hw) (kC' w hw) := fun w hw =>
        G0.isArchCompAt_of_mul_of_zero_zero K ν _ w _ _ (hμν ▸ hC w hw) (hN0 w)
      have h := hω₃.2.2 uR' aR' uC' kC' hR' hC' v hv
      rw [pow_three]
      exact G0.isArchCompAt_mul_of_zero_zero ℚ ω₃ _ v _ _ h
        (G0.isArchCompAt_mul_of_zero_zero ℚ ξA _ v _ _ (hξinf v hv)
          (G0.isArchCompAt_mul_of_zero_zero ℚ ξA _ v _ _ (hξinf v hv) (hξinf v hv)))
  have hWμ : Warch ≠ 0 ∧ IsKFinite Warch ∧
      (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf Warch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        Warch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = (((ω₃ * ξA ^ 3) (E z) : ℂˣ) : ℂ) * Warch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => Warch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => Warch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => Warch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => Warch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                ((((ω₃ * ξA ^ 3) (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0 := by

    have hχE : ∀ z : (InfiniteAdeleRing ℚ)ˣ, ξA (E z) = 1 := fun z => Units.ext (by
      rw [LanglandsTunnell.CubicInduction.apply_of_infPart_eq_of_isArchCompAt ξA E hE 0 0 hξinf z Rat.infinitePlace
        Rat.isReal_infinitePlace]
      simp only [mul_zero, Complex.cpow_zero, zpow_zero, mul_one, Units.val_one])
    have hE1 : ∀ z : (InfiniteAdeleRing ℚ)ˣ, (ω₃ * ξA ^ 3) (E z) = ω₃ (E z) := fun z => by
      rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hχE z, one_pow, mul_one]
    simp only [hE1, G0.heckeDatum_archFactor_eq K μ ν, G0.heckeDatum_archFactorDual_eq K μ ν]
    exact hWarch

  obtain ⟨Tμ, hTμ⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v, IsBadPlace K μ v → v ∈ T := by
    refine ⟨SQ ∪ Tν, fun v hv => ?_⟩
    by_cases h : v ∈ SQ
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hTν v
        ((LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt K _hdeg ν ξA hξA v
          (hξoff' v h)).1.mp (hμν ▸ hv)))
  have hstabX : ∀ v, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g :=
    fun v hv => (hBadμ {v}).1 v (Finset.mem_singleton_self v) hv
  have hXarch0 : X.whittakerArch ≠ 0 := fun h0 => hWarch.1 (hArchEq ▸ h0)
  obtain ⟨Y, hY, hY0, hY1, hYgood, hYcyc, hYarch, hYcc, hYc, hYw, hYdw, hYg, hYdg, hYstab, hYscal⟩ :=
    LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace K ψ hψ.continuous μ
      _ _ _ X hX (hC1 hFc) (hC2 hFw) (hC3 hFdw) (hG1 hFg) (hG2 hFdg) hX0.1 hXarch0 Tμ hTμ hstabX
      (fun v hv => (hcent v hv).2)
  have hY0' : Y.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        Y.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (Y.whittakerLoc v) :=
    ⟨hY0, fun v hv hl => by rw [hYgood v hv]; exact hX0.2 v hv hl⟩
  have hBadY : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (Y.whittakerLoc v), W ≠ 0 →
            Y.whittakerLoc v ∈ gl3CyclicSubspace W) := fun T =>
    ⟨fun v _ hv => hYstab v hv, fun v _ hv W hW hW0 => by
      have hWX : W ∈ gl3CyclicSubspace (X.whittakerLoc v) := by rw [← hYcyc v]; exact hW
      have h1 := (hBadμ {v}).2 v (Finset.mem_singleton_self v) hv W hWX hW0
      have h2 : Y.whittakerLoc v ∈ gl3CyclicSubspace (X.whittakerLoc v) := by
        rw [← hYcyc v]; exact G0.self_mem_gl3CyclicSubspace _
      exact G0.gl3CyclicSubspace_le_of_mem h1 h2⟩
  have hadmY : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w →
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (Y.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)) := fun w hw Uw hUw => by
    obtain ⟨B, hB⟩ := hadmμ w hw Uw hUw
    exact ⟨B, fun G hG => hB G (by rw [← hYcyc w]; exact hG)⟩
  have hcentY : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w →
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((NumberField.TateGlobal.localChar Y.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        Y.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((NumberField.TateGlobal.localChar Y.centralChar w t : ℂˣ) : ℂ) * Y.whittakerLoc w h := fun w hw =>
    ⟨by rw [hYcc]; exact (hcent w hw).1, hYscal w hw⟩

  have hpbad : IsBadPlace K μ p := hSQbad p hpSQ
  obtain ⟨lam, hlam0, hl3⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deepAt
      K _hdeg μ hμ hoffμ p hpbad uR aR uC kC hcRμ hcCμ ψ hψ hlev hψQ (ω₃ * ξA ^ 3) hωμ E hE a ha aInf haInf psiInf
      hpsiInf hψinf ν_add hν_add ν_mul Warch hWμ _ _ _ Y hY hY0' hY1 hYc hYw hYdw hYg hYdg (hYarch.trans hArchEq)
      hBadY hadmY hcentY
  have hgen : X.whittakerLoc p ∈ gl3CyclicSubspace (Y.whittakerLoc p) := by
    rw [hYcyc p]; exact G0.self_mem_gl3CyclicSubspace _

  have hN0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ideal.absNorm_eq_zero_iff.ne]
    exact p.ne_bot
  have hfin := IDX.primeFibre_finite K p
  obtain ⟨ℓ, hℓ⟩ := IDX.exists_nat_cast_eq_finsum_pinnedExp K μ p
  set A : ℂ := ∏ᶠ w ∈ primeFibre ℚ K p, ((localChar μ w (-1) : ℂˣ) : ℂ) with hAdef
  set Eps : ℂ := ∏ᶠ w ∈ primeFibre ℚ K p, LanglandsTunnell.TateLocal.stdRootNumberAt K w (localChar μ w) with hEpsdef
  have hA0 : A ≠ 0 := by
    rw [hAdef]
    exact finprod_mem_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ hx hy => mul_ne_zero hx hy)
      (fun w _ => Units.ne_zero _)
  have hEps0 : Eps ≠ 0 := by
    rw [hEpsdef]
    refine finprod_mem_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ hx hy => mul_ne_zero hx hy) ?_
    intro w _
    obtain ⟨aw, haw⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K w (localChar μ w)
      (NumberField.TateGlobal.continuous_localChar μ hμ.2.1 w)
    have h1 := LanglandsTunnell.TateLocal.norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt K w (localChar μ w) aw haw
      (fun x => by rw [NumberField.TateGlobal.localChar_apply]; exact hμ.2.2 _)
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hε0 : lam * (A * Eps) ≠ 0 := mul_ne_zero hlam0 (mul_ne_zero hA0 hEps0)

  have h1A : IsAdmissibleTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) := by
    have h := G0.isAdmissibleTwist_mul ℚ _ _ hξA (G0.isAdmissibleTwist_inv ℚ _ hξA)
    have e : ξA * ξA⁻¹ = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel, MonoidHom.one_apply]
    rwa [e] at h
  have h1AN : IsAdmissibleTwist K
      ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) := by
    rw [MonoidHom.one_comp]
    have h := G0.isAdmissibleTwist_mul K _ _ hμ (G0.isAdmissibleTwist_inv K _ hμ)
    have e : μ * μ⁻¹ = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel, MonoidHom.one_apply]
    rwa [e] at h
  have e1μ : (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ = μ :=
    MonoidHom.ext fun x => by rw [MonoidHom.mul_apply, MonoidHom.one_comp, MonoidHom.one_apply, one_mul]
  have hloc1 : localChar (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) p = (1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) :=
    MonoidHom.ext fun x => by rw [NumberField.TateGlobal.localChar_apply]; rfl
  have h10 : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) 0 :=
    LanglandsTunnell.TateLocal.hasConductorExponentAt_one_zero ℚ p
  have hdepth0 : ∀ w ∈ primeFibre ℚ K p,
      2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * 0) + 1 ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) := fun w hw => by
    have h := hDTR w hw
    rw [mul_zero, mul_zero, zero_add]
    omega

  have h31gen := LanglandsTunnell.CubicInduction.localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq p
    (X.whittakerLoc p) 1 1 (lam * (A * Eps)) ℓ one_ne_zero one_ne_zero
    (Polynomial.C (lam * (A * Eps) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) / 2))) 1 (-(ℓ : ℤ))
    ⟨Polynomial.C_ne_zero.mpr (mul_ne_zero hε0 (by
        intro h0; rw [Complex.cpow_eq_zero_iff] at h0; exact hN0 h0.1)),
      one_ne_zero, fun g => by
        obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ₂, hc30, hZ, hc31, hZd⟩ :=
          hl3 (X.whittakerLoc p) hgen 0 hdepth0 1 0 h10 le_rfl 1 h1A hloc1 h1AN g
        refine ⟨Q₁, Q₂, n, σ₀, σ₁, hQ₂, hc30, hZ, hc31, fun s hs => ?_⟩
        have hZd' := hZd s hs
        rw [e1μ] at hZd'
        rw [Polynomial.eval_one, mul_one, hZd', Polynomial.eval_C,
          finprod_mem_mul_distrib hfin, IDX.finprod_primeFibre_cpow_zpow_eq_cpow K p _ ℓ hℓ s, ← hAdef, ← hEpsdef]
        have hb := IDX.cpow_bookkeeping (Ideal.absNorm p.asIdeal : ℂ) hN0 ℓ (-(ℓ : ℤ)) n rfl s
        linear_combination (Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * lam * A * Eps) * hb⟩
    (fun s => by
      rw [Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_one, mul_one, mul_one]
      have hb := IDX.cpow_bookkeeping' (Ideal.absNorm p.asIdeal : ℂ) hN0 ℓ (-(ℓ : ℤ)) rfl s
      linear_combination (lam * (A * Eps)) * hb)

  have hexp : ∀ w ∈ primeFibre ℚ K p,
      (B : ℤ) ≤ (LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) : ℤ) ∧
      (LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) : ℤ) ≤
        (p.asIdeal.ramificationIdx' w.asIdeal : ℤ) * (B : ℤ) := by
    intro w hw
    have hw' : w.under (𝓞 ℚ) = p := (mem_primeFibre ℚ p w).mp hw
    refine ⟨by exact_mod_cast hDTR w hw, ?_⟩
    obtain ⟨a₁, hBa, ha, -⟩ :=
      LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_of_finrank_eq_three K _hdeg p
        (⟨w, hw'⟩ : p.Extension (𝓞 K)) (NumberField.TateGlobal.localChar ξA p) B (by omega) hξB
    obtain ⟨b', hb', hb'le⟩ :=
      LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul ℚ K p
        (⟨w, hw'⟩ : p.Extension (𝓞 K)) (NumberField.TateGlobal.localChar ξA p) B hξB
    have hab : a₁ = b' := LanglandsTunnell.TateLocal.hasConductorExponentAt_unique K _ ha hb'
    obtain ⟨c, hc, hνw⟩ := hνc w hw
    have hprod := LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt K _ _ _ a₁ c
      ha hνw (by omega)
    have hloc := NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K ν ξA p
      (⟨w, hw'⟩ : p.Extension (𝓞 K))
    have hloc' := hloc.trans
      (mul_comm (NumberField.TateGlobal.localChar ν ((⟨w, hw'⟩ : p.Extension (𝓞 K)).1)) _)
    have hkey : LanglandsTunnell.TateLocal.HasConductorExponentAt K w (localChar μ w) a₁ := by
      rw [hμν, show NumberField.TateGlobal.localChar
          (ν * ξA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w = _ from hloc']
      exact hprod
    rw [LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K w hkey, hab]
    exact_mod_cast hb'le
  obtain ⟨w₀, hw₀⟩ := IDX.primeFibre_nonempty K p
  have hterm_nn : ∀ w ∈ hfin.toFinset, (0 : ℤ) ≤ (p.asIdeal.inertiaDeg' w.asIdeal : ℤ) *
      LanglandsTunnell.Converse.pinnedExp K μ w := fun w hw => by
    refine mul_nonneg (Int.natCast_nonneg _) ?_
    unfold LanglandsTunnell.Converse.pinnedExp
    refine add_nonneg (Int.natCast_nonneg _) ?_
    rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal]
    exact FractionalIdeal.count_coe_nonneg K w _
  have hd_nn : ∀ w : HeightOneSpectrum (𝓞 K), (0 : ℤ) ≤
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) := fun w => by
    rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal]
    exact FractionalIdeal.count_coe_nonneg K w _
  have hf_pos : ∀ w ∈ primeFibre ℚ K p, (1 : ℤ) ≤ (p.asIdeal.inertiaDeg' w.asIdeal : ℤ) := fun w hw => by
    have hw' : w.under (𝓞 ℚ) = p := (mem_primeFibre ℚ p w).mp hw
    haveI : w.asIdeal.LiesOver p.asIdeal := ⟨by rw [← hw']; rfl⟩
    exact_mod_cast Ideal.inertiaDeg'_pos p.asIdeal w.asIdeal
  have hℓsum : (ℓ : ℤ) = ∑ w ∈ hfin.toFinset, (p.asIdeal.inertiaDeg' w.asIdeal : ℤ) *
      LanglandsTunnell.Converse.pinnedExp K μ w := by
    rw [hℓ, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hBℓ : B ≤ ℓ := by
    have h1 := Finset.single_le_sum hterm_nn (hfin.mem_toFinset.mpr hw₀)
    rw [← hℓsum] at h1
    have h2 : (B : ℤ) ≤ (p.asIdeal.inertiaDeg' w₀.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w₀ := by
      unfold LanglandsTunnell.Converse.pinnedExp
      have hf := hf_pos w₀ hw₀
      have ha := (hexp w₀ hw₀).1
      have hd := hd_nn w₀
      nlinarith
    exact_mod_cast h2.trans h1
  have hef : ∑ w ∈ hfin.toFinset, (p.asIdeal.ramificationIdx' w.asIdeal : ℤ) * (p.asIdeal.inertiaDeg' w.asIdeal : ℤ) = 3 := by
    have h := IDX.finsum_fibre_ramificationIdx_mul_inertiaDeg K p
    rw [_hdeg, finsum_mem_eq_finite_toFinset_sum _ hfin] at h
    exact_mod_cast h
  have hℓhi : (ℓ : ℤ) ≤ 3 * (B : ℤ) + ∑ᶠ 𝔓 ∈ primeFibre ℚ K p, (p.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, hℓsum, ← hef, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have hw' := hfin.mem_toFinset.mp hw
    unfold LanglandsTunnell.Converse.pinnedExp
    have hf : (0 : ℤ) ≤ (p.asIdeal.inertiaDeg' w.asIdeal : ℤ) := Int.natCast_nonneg _
    have ha := (hexp w hw').2
    nlinarith

  refine ⟨lam * (A * Eps), ℓ, hε0, hℓ, hBℓ, hℓhi, fun W hW g => ?_⟩
  exact LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall p
    (X.whittakerLoc p) _ _ _ _ h31gen W hW g

end S_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt (solution)
