-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f1348cfd-c549-5978-a756-5766666dc334

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta_conj_diagonal_signFlip
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar
import Theorems.Thm_AutomorphicForm_psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_exists_forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittakerLoc_ne_zero_of_isCubicInductionDataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_LanglandsTunnell_CubicInduction_globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_HeckeTate_finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp
import Theorems.Thm_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg
import Theorems.Thm_HeckeCharacter_exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_exists_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isReal
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_LanglandsTunnell_Converse_hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3
import Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_localZetaDual31_eq_mul_localZeta30_of_isGL3PsiWhittakerFn_of_norm_eq_one
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_of_ramificationIdx_eq_one
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_two_mul_conductorExponent_le
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_three
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_ne_zero_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_of_finrank_eq_three
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt
import Theorems.Thm_NumberField_TateGlobal_localChar_apply_neg_one_eq_one_of_isIdeleClassChar_of_isArchCompAt_zero_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_localChar_centralChar_neg_one_and_pin_eq_finprod_of_eq_finprod_mul_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_factors_or_eq_zero_of_integrable_sPart
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_eq_modulus_cpow
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_HeckeTate_finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archDetermined_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le
import Theorems.Thm_NumberField_TateGlobal_prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt
import Theorems.Thm_LanglandsTunnell_Converse_pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
import Theorems.Thm_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply"
p2m_attr_erase "simp" "NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

theorem archComp_eq_of_isArchCompAt_zero_zero
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hτ : IsAdmissibleTwist ℚ τ)
    (hτinf : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 0) :
    τ.comp E = 1 := by
  refine MonoidHom.ext fun z => ?_
  apply Units.ext
  rw [MonoidHom.comp_apply, MonoidHom.one_apply, Units.val_one,
    LanglandsTunnell.CubicInduction.apply_of_infPart_eq_of_isArchCompAt τ E hE 0 0 hτinf z Rat.infinitePlace
      Rat.isReal_infinitePlace]
  simp only [mul_zero, Complex.cpow_zero, zpow_zero, mul_one]

theorem archZeta30_comp_eq_archZeta30_one_of_isArchCompAt
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ)
    (hσ : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) (he : (-1 : ℂ) ^ e = 1) (s : ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archZeta30 ν_mul Warch (σ.comp E) s g = archZeta30 ν_mul Warch 1 (s + t) g := by
  unfold archZeta30
  congr 1
  funext a
  have hw := Rat.isReal_infinitePlace
  have hx0 : (a : InfiniteAdeleRing ℚ) Rat.infinitePlace ≠ 0 :=
    (Units.map (Pi.evalMonoidHom (fun v : InfinitePlace ℚ => v.Completion) Rat.infinitePlace) a).ne_zero
  have hnorm : ‖(a : InfiniteAdeleRing ℚ)‖ = ‖(a : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ := by
    rw [NumberField.InfiniteAdeleRing.norm_def, Fintype.prod_subsingleton _ Rat.infinitePlace,
      NumberField.InfinitePlace.mult, if_pos hw, pow_one]
  have hsign : (NumberField.InfinitePlace.Completion.extensionEmbedding Rat.infinitePlace
      ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace) /
        (‖(a : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ : ℂ)) ^ e = 1 := by
    have hr : (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace) : ℂ) =
        NumberField.InfinitePlace.Completion.extensionEmbedding Rat.infinitePlace
          ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace) :=
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw _
    have hn : ‖(a : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ =
        |NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
          ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace)| := by
      have := (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace)
      rw [Real.norm_eq_abs] at this
      exact this.symm
    have hr0 : NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace) ≠ 0 := (map_ne_zero _).mpr hx0
    rw [← hr, hn]
    rcases hr0.lt_or_gt with hlt | hgt
    · rw [abs_of_neg hlt, Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.mpr hr0), he]
    · rw [abs_of_pos hgt, div_self (Complex.ofReal_ne_zero.mpr hr0), one_zpow]
  have hσa : (((σ.comp E) a : ℂˣ) : ℂ) = ((‖(a : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ : ℂ)) ^ t := by
    rw [MonoidHom.comp_apply, apply_of_infPart_eq_of_isArchCompAt σ E hE t e hσ a Rat.infinitePlace hw, hsign, mul_one,
      NumberField.InfinitePlace.mult, if_pos hw, Nat.cast_one, one_mul]
  rw [hσa, MonoidHom.one_apply, Units.val_one, mul_one, hnorm, mul_assoc,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx0))]
  congr 2
  ring

theorem localZeta31_dualWhittakerFn3_eq_localZetaDual31_inv
    (v : HeightOneSpectrum (𝓞 ℚ)) [MeasurableSpace (v.adicCompletion ℚ)ˣ] [MeasurableSpace (v.adicCompletion ℚ)]
    (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ))
    (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZeta31 v μ ν (dualWhittakerFn3 W) χ s (weylPrime3 * transposeInv3 g) = localZetaDual31 v μ ν W χ⁻¹ s g := by
  unfold localZetaDual31
  exact congrArg (fun ψ => localZeta31 v μ ν (dualWhittakerFn3 W) ψ s (weylPrime3 * transposeInv3 g)) (inv_inv χ).symm

theorem inducedL_fe
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hτ : IsAdmissibleTwist ℚ τ) (t : ℂ) (e : ℤ)
    (hτinf : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ τ v t e) :
    IsNicePinned
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
        (fun w hw => uR w hw + t) (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC)
      (fun _ => 1) (fun _ => 1)
      (LanglandsTunnell.HeckeTate.heckeRootNumber K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
        (fun w hw => aR w hw + (e : ZMod 2)) kC)
      (LanglandsTunnell.HeckeTate.heckeConductor K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) ∧
    ∀ p : HeightOneSpectrum (𝓞 ℚ), IsUnramifiedCharAt τ p →
    (∏ᶠ 𝔓 ∈ primeFibre ℚ K p,
        ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
            (fun w hw => uR w hw + t) (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t)
            kC).euler 𝔓).comp (Polynomial.X ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)))
      = (inducedEulerPoly ℚ (inducedCoeff K μ) p).comp
          (Polynomial.C (LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ p) * Polynomial.X) := by
  refine ⟨LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg K μ
    _hμ _hns uR aR uC kC huR huC τ hτ t e hτinf, fun p hp => ?_⟩
  exact LanglandsTunnell.HeckeTate.finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp K μ τ
    (fun w hw => uR w hw + t) (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC p hp

theorem exists_comparisonTwist
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) (_hv : v ∈ S)
    (depth : HeightOneSpectrum (𝓞 ℚ) → ℕ) :
    ∃ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ ∧ IsUnramifiedCharAt τ v ∧
      (∀ w ∈ S, w ≠ v → ∃ n : ℕ, depth w ≤ n ∧ Even n ∧
        LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ w (localChar τ w) n) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt τ w) ∧
      ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 0 := by
  classical
  obtain ⟨τ, hadm, hexp, hunr, harch⟩ :=
    LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le (S.erase v)
      (fun w => 2 * max (depth w) 2) (fun w _ => by show 3 ≤ 2 * max (depth w) 2; omega)
  refine ⟨τ, hadm, hunr v (by simp), fun w hw hwv => ?_,
    fun w hw => hunr w fun h => hw (Finset.mem_of_mem_erase h), harch⟩
  exact ⟨2 * max (depth w) 2, by omega, even_two_mul _, hexp w (Finset.mem_erase.mpr ⟨hwv, hw⟩)⟩

theorem localZeta30_unramifiedTwist_eq_shift
    (v : HeightOneSpectrum (𝓞 ℚ)) (ω χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s₀ : ℂ)
    (hs₀ : ∀ a : (v.adicCompletion ℚ)ˣ,
      ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 ∧
      ((χ a : ℂˣ) : ℂ) = ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s₀) :
    letI := localBorel ℚ v
    ∀ (W : LocalGL3 v → ℂ) (g : LocalGL3 v) (s : ℂ),
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W (ω * χ) s g =
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W ω (s + s₀) g ∧
      localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W (ω * χ)
          (1 - s) g =
        localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W ω
          (1 - (s + s₀)) g := by
  letI := localBorel ℚ v
  refine fun W g s => ⟨?_, ?_⟩
  · unfold localZeta30
    congr 1
    funext a
    obtain ⟨hne, hval⟩ := hs₀ a
    have hexp : s + s₀ - 1 = s₀ + (s - 1) := by ring
    rw [MonoidHom.mul_apply, Units.val_mul, hval, hexp, Complex.cpow_add _ _ hne]
    ring
  · unfold localZetaDual31 localZeta31
    congr 1
    funext a
    obtain ⟨hne, hval⟩ := hs₀ a
    have hexp : 1 - (s + s₀) - 1 = -s₀ + (1 - s - 1) := by ring
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, MonoidHom.mul_apply, mul_inv, Units.val_mul,
      Units.val_inv_eq_inv_val (χ a), hval, hexp, Complex.cpow_add _ _ hne, ← Complex.cpow_neg]
    ring

open scoped Classical in

theorem exists_testVector_localZeta30_ne_zero
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (hbad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
        X.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hconv : ∀ g : LocalGL3 v, ∃ σ : ℝ,
      letI := localBorel ℚ v
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v)
        η g σ) :
    letI := localBorel ℚ v
    (∃ (g : LocalGL3 v) (σ : ℝ),
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) η g
        σ ∧
      ∀ s : ℂ, σ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) η s g ≠ 0) := by
  have hW0 : X.whittakerLoc v ≠ 0 :=
    whittakerLoc_ne_zero_of_isCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ X hX S
      (fun w hw => (hSbad w).1 hw) hexp.1 v
  have hψ1 : psiLoc ψ v ≠ 1 := (psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar ψ _hψ v).1
  exact
    exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
      v (psiLoc ψ v) hψ1 (X.whittakerLoc v) (hX.whittakerLoc_law v) hW0
      ((hbad S).1 v hv ((hSbad v).mpr hv)) η hconv

theorem psiLoc_eq_one_of_valued_le_one_and_exists_ne_one
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S) :
    (∀ v, v ∉ S → ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1) ∧
    (∀ v, v ∉ S → ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1) := by
  obtain ⟨ψv, nψ, -, -, h1, h2, -, h4, -⟩ :=
    AutomorphicForm.exists_localComponents_of_isGlobalAddChar ℚ ψ _hψ
  have hloc : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ), psiLoc ψ v x = ψv v x := by
    intro v x
    have hfp : (∏ᶠ w, ψv w (NumberField.StandardAddChar.finAdeleSingleAt ℚ v x w)) = ψv v x := by
      refine (finprod_eq_single _ v fun w hw => ?_).trans ?_
      · simp only [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v x hw, AddChar.map_zero_eq_one]
      · simp only [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
    show ψ (AddMonoidHom.inr (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)
      (NumberField.StandardAddChar.finAdeleSingleAt ℚ v x)) = ψv v x
    exact (h4 _).trans hfp
  have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1) ∧
        ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1 := by
    intro v hvS
    have hl : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 :=
      _hlev v fun hb => hvS ((hSbad v).mp hb)
    have hne : psiLoc ψ v ≠ 1 := by
      obtain ⟨x, -, hx⟩ := h2 v
      intro h
      exact hx (by rw [← hloc v x, h, AddChar.one_apply])
    have hk := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v (psiLoc ψ v)
      ⟨nψ v, fun x hx => by rw [hloc v x]; exact h1 v x hx⟩ hne
    rw [hl, WithZero.exp_zero] at hk
    obtain ⟨hk1, x₀, hx₀, hne₀⟩ := hk
    refine ⟨hk1, varpi v * x₀, ?_, ?_⟩
    · rw [Valuation.map_mul, NumberField.AdelicLevel.valued_uniformizerUnit ℚ v]
      calc WithZero.exp (-1 : ℤ) * Valued.v x₀
          ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (0 + 1) := by gcongr
        _ = 1 := by rw [← WithZero.exp_add]; norm_num
    · rwa [inv_mul_cancel_left₀ (varpi_ne_zero v)]
  exact ⟨fun v hvS => (hv v hvS).1, fun v hvS => (hv v hvS).2⟩

theorem heckeDatum_euler_ne_zero
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (LanglandsTunnell.HeckeTate.heckeDatum K χ uR aR uC kC).euler 𝔓 ≠ 0 := by
  intro h
  have h0 := congrArg (fun q : Polynomial ℂ => q.coeff 0) h
  simp only [LanglandsTunnell.HeckeTate.heckeDatum] at h0
  split_ifs at h0 <;> simp at h0

theorem one_lt_heckeDatum_norm
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    1 < (LanglandsTunnell.HeckeTate.heckeDatum K χ uR aR uC kC).norm 𝔓 := by
  have h0 : Ideal.absNorm 𝔓.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact 𝔓.ne_bot
  have h1 : Ideal.absNorm 𝔓.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact 𝔓.isPrime.ne_top
  show 1 < Ideal.absNorm 𝔓.asIdeal
  omega

theorem hasProd_subtype_of_multipliable_of_fibre_prod_eq {ι κ : Type} (f : ι → ℂ) (u : ι → κ)
    (S : Finset κ) (G : {k : κ // k ∉ S} → ℂ) (hf : Multipliable f)
    (hfin : ∀ k : κ, {i : ι | u i = k}.Finite)
    (hS : ∀ k ∈ S, ∀ i : ι, u i = k → f i = 1)
    (hG : ∀ k : {k : κ // k ∉ S}, ∏ i ∈ (hfin k.1).toFinset, f i = G k) :
    HasProd G (∏' i : ι, f i) := by
  have h₁ : HasProd (f ∘ Equiv.sigmaFiberEquiv u) (∏' i : ι, f i) :=
    (Equiv.sigmaFiberEquiv u).hasProd_iff.mpr hf.hasProd
  have hfib : ∀ k : κ, HasProd (fun c : {i : ι // u i = k} => f c.1) (∏ i ∈ (hfin k).toFinset, f i) := by
    intro k
    have he : ∀ i : ι, u i = k ↔ i ∈ ((hfin k).toFinset : Set ι) := by
      intro i
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact (Equiv.subtypeEquivRight he).hasProd_iff.mpr ((hfin k).toFinset.hasProd f)
  have h₂ : HasProd (fun k : κ => ∏ i ∈ (hfin k).toFinset, f i) (∏' i : ι, f i) := HasProd.sigma h₁ hfib
  have hone : ∀ k ∈ S, ∏ i ∈ (hfin k).toFinset, f i = 1 := by
    intro k hk
    refine Finset.prod_eq_one fun i hi => hS k hk i ?_
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hi
  have hGeq : G = fun k : {k : κ // k ∉ S} => ∏ i ∈ (hfin k.1).toFinset, f i := by
    funext k
    exact (hG k).symm
  have hind : ({k : κ | k ∉ S} : Set κ).mulIndicator (fun k : κ => ∏ i ∈ (hfin k).toFinset, f i) =
      fun k : κ => ∏ i ∈ (hfin k).toFinset, f i := by
    funext k
    by_cases hk : k ∈ S
    · rw [Set.mulIndicator_of_notMem (fun h => (h : k ∉ S) hk), hone k hk]
    · exact Set.mulIndicator_of_mem hk _
  rw [hGeq]
  refine (hasProd_subtype_iff_mulIndicator (s := {k : κ | k ∉ S})
    (f := fun k : κ => ∏ i ∈ (hfin k).toFinset, f i)).mpr ?_
  rw [hind]
  exact h₂

theorem prod_inv_eval_pow_cpow_eq_inv_eval_of_prod_comp_eq {ι : Type} (T : Finset ι)
    (P : ι → Polynomial ℂ) (f : ι → ℕ) (R : Polynomial ℂ) (c : ℂ) (q : ℕ) (s : ℂ)
    (h : ∏ i ∈ T, (P i).comp (Polynomial.X ^ f i) = R.comp (Polynomial.C c * Polynomial.X)) :
    ∏ i ∈ T, ((P i).eval (((q ^ f i : ℕ) : ℂ) ^ (-s)))⁻¹ = (R.eval (c * (q : ℂ) ^ (-s)))⁻¹ := by
  have hpow : ∀ i : ι, (((q ^ f i : ℕ) : ℂ) ^ (-s)) = ((q : ℂ) ^ (-s)) ^ f i := fun i => by
    rw [Nat.cast_pow, ← Complex.cpow_nat_mul' (by simp [Complex.natCast_arg, Real.pi_pos])
      (by simp [Complex.natCast_arg, Real.pi_pos.le]), Complex.cpow_nat_mul]
  have h' := congrArg (Polynomial.eval ((q : ℂ) ^ (-s))) h
  rw [Polynomial.eval_prod, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at h'
  rw [Finset.prod_inv_distrib, ← h']
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hpow, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]

theorem absNorm_asIdeal_eq_pow_inertiaDeg_under
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔓.asIdeal =
      Ideal.absNorm (𝔓.under (𝓞 ℚ)).asIdeal ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
  haveI : IsScalarTower ℤ (𝓞 ℚ) (𝓞 K) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 ℚ)).asIdeal :=
    inferInstanceAs (𝔓.asIdeal.LiesOver (𝔓.asIdeal.under (𝓞 ℚ)))
  exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal (𝔓.under (𝓞 ℚ)).asIdeal
    (𝔓.under (𝓞 ℚ)).isPrime (𝔓.under (𝓞 ℚ)).ne_bot

theorem finprod_inv_eval_euler_heckeDatum_eq_inv_eval_inducedEulerPoly
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hτ : IsUnramifiedCharAt τ p) (hfin : (primeFibre ℚ K p).Finite)
    (s : ℂ) :
    (∏ᶠ 𝔓 ∈ primeFibre ℚ K p,
        (((LanglandsTunnell.HeckeTate.heckeDatum K
              (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).euler 𝔓).eval
          (((LanglandsTunnell.HeckeTate.heckeDatum K
              (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℂ) ^
            (-s)))⁻¹)
      = ((inducedEulerPoly ℚ (inducedCoeff K μ) p).eval
          (LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ p * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ := by
  have h₁ := LanglandsTunnell.HeckeTate.finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp K μ τ uR aR uC kC
    p hτ
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin] at h₁
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin,
    ← prod_inv_eval_pow_cpow_eq_inv_eval_of_prod_comp_eq _ _ _ _ _ _ s h₁]
  refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
  have hp : 𝔓.under (𝓞 ℚ) = p := (mem_primeFibre ℚ p 𝔓).mp (hfin.mem_toFinset.mp h𝔓)
  have hN : (LanglandsTunnell.HeckeTate.heckeDatum K
      (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓
        = Ideal.absNorm p.asIdeal ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
    show Ideal.absNorm 𝔓.asIdeal = _
    rw [absNorm_asIdeal_eq_pow_inertiaDeg_under K 𝔓, hp]
  rw [hN]

theorem hasProd_subtype_notMem_erase_of_hasProd_subtype_notMem {κ : Type} [DecidableEq κ] (g : κ → ℂ)
    (S : Finset κ) (v : κ) (hv : v ∈ S) (L : ℂ) (hL : HasProd (fun p : {p : κ // p ∉ S} => g p.1) L) :
    HasProd (fun p : {p : κ // p ∉ S.erase v} => g p.1) (g v * L) := by
  have h1 : HasProd (({p : κ | p ∉ S} : Set κ).mulIndicator g) L :=
    (hasProd_subtype_iff_mulIndicator (s := {p : κ | p ∉ S})).mp hL
  have h2 : HasProd (({v} : Set κ).mulIndicator g) ((({v} : Set κ).mulIndicator g) v) :=
    hasProd_single v fun b hb => Set.mulIndicator_of_notMem (by simpa using hb) g
  rw [Set.mulIndicator_of_mem (Set.mem_singleton v)] at h2
  have hdisj : Disjoint ({v} : Set κ) {p : κ | p ∉ S} := by
    rw [Set.disjoint_singleton_left]
    exact fun h => h hv
  have hset : ({p : κ | p ∉ S.erase v} : Set κ) = {v} ∪ {p : κ | p ∉ S} := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.mem_erase, not_and, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases hpv : p = v
      · exact Or.inl hpv
      · exact Or.inr (h hpv)
    · rintro (rfl | h)
      · intro h'
        exact absurd rfl h'
      · intro _
        exact h
  refine (hasProd_subtype_iff_mulIndicator (s := {p : κ | p ∉ S.erase v})).mpr ?_
  rw [hset, Set.mulIndicator_union_of_disjoint hdisj]
  exact h2.mul h1

theorem LFun_heckeDatum_eq_finprod_fibre_mul_inducedL
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v₀ : HeightOneSpectrum (𝓞 ℚ)) (hv₀ : v₀ ∈ S) (s : ℂ) (L : ℂ)
    (hfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), (primeFibre ℚ K p).Finite)
    (hτ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt τ p)
    (hram : ∀ w ∈ S, w ≠ v₀ → ∀ 𝔓 ∈ primeFibre ℚ K w,
      ¬ IsUnramifiedCharAt (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
    (hmult : Multipliable fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
              uR aR uC kC).euler 𝔓).eval (((LanglandsTunnell.HeckeTate.heckeDatum K
                  (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                      uR aR uC kC).norm 𝔓 : ℂ) ^ (-s)))⁻¹)
    (hL : HasProd (fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
        ((inducedEulerPoly ℚ (inducedCoeff K μ) p.1).eval
          (LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ p.1 * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)))⁻¹) L) :
    (LanglandsTunnell.HeckeTate.heckeDatum K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
        uR aR uC kC).LFun s =
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v₀, (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
              uR aR uC kC).euler 𝔓).eval (((LanglandsTunnell.HeckeTate.heckeDatum K
                  (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                      uR aR uC kC).norm 𝔓 : ℂ) ^ (-s)))⁻¹) * L := by
  classical
  let r : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun q => ∏ 𝔓 ∈ (hfin q).toFinset,
      (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
              uR aR uC kC).euler 𝔓).eval (((LanglandsTunnell.HeckeTate.heckeDatum K
                  (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                      uR aR uC kC).norm 𝔓 : ℂ) ^ (-s)))⁻¹
  have hL' : HasProd (fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} => r p.1) L := by
    convert hL using 1
    funext p
    show ∏ 𝔓 ∈ (hfin p.1).toFinset, _ = _
    rw [← finprod_mem_eq_finite_toFinset_prod _ (hfin p.1)]
    exact finprod_inv_eval_euler_heckeDatum_eq_inv_eval_inducedEulerPoly K μ τ uR aR uC kC p.1 (hτ p.1 p.2)
      (hfin p.1) s
  have hsplit : HasProd (fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S.erase v₀} => r p.1) (r v₀ * L) :=
    hasProd_subtype_notMem_erase_of_hasProd_subtype_notMem r S v₀ hv₀ L hL'
  have hregroup :=
    hasProd_subtype_of_multipliable_of_fibre_prod_eq _ (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ))
    (S.erase v₀) (fun p => r p.1) hmult hfin
    (by
      intro k hk 𝔓 h𝔓
      have hr := hram k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk) 𝔓 h𝔓
      simp only [LanglandsTunnell.HeckeTate.heckeDatum, if_neg hr, Polynomial.eval_C, inv_one])
    (fun _ => rfl)
  rw [finprod_mem_eq_finite_toFinset_prod _ (hfin v₀)]
  exact hregroup.unique hsplit

theorem isUnramifiedCharAt_inv_iff {F : Type} [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    NumberField.TateGlobal.IsUnramifiedCharAt χ⁻¹ v ↔ NumberField.TateGlobal.IsUnramifiedCharAt χ v := by
  have key : ∀ t : (v.adicCompletion F)ˣ,
      NumberField.TateGlobal.localChar χ⁻¹ v t = (NumberField.TateGlobal.localChar χ v t)⁻¹ := fun t =>
    MonoidHom.inv_apply χ _
  constructor
  · intro h t ht ht'
    exact inv_eq_one.mp ((key t).symm.trans (h t ht ht'))
  · intro h t ht ht'
    rw [key t, h t ht ht', inv_one]

theorem dual_heckeDatum_eq_euler_heckeDatum_inv {F : Type} [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace F, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace F, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ)
    (𝔓 : HeightOneSpectrum (𝓞 F)) :
    (LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).dual 𝔓
      = (LanglandsTunnell.HeckeTate.heckeDatum F χ⁻¹ uR aR uC kC).euler 𝔓 := by
  simp only [LanglandsTunnell.HeckeTate.heckeDatum]
  by_cases h : NumberField.TateGlobal.IsUnramifiedCharAt χ 𝔓
  · rw [if_pos h, if_pos ((isUnramifiedCharAt_inv_iff χ 𝔓).mpr h), MonoidHom.inv_apply]
  · rw [if_neg h, if_neg fun h' => h ((isUnramifiedCharAt_inv_iff χ 𝔓).mp h')]

theorem dual_heckeDatum_eq_one_of_not_isUnramifiedCharAt {F : Type} [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace F, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace F, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ)
    (𝔓 : HeightOneSpectrum (𝓞 F)) (h : ¬ NumberField.TateGlobal.IsUnramifiedCharAt χ 𝔓) :
    (LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).dual 𝔓 = Polynomial.C 1 := by
  simp only [LanglandsTunnell.HeckeTate.heckeDatum]
  rw [if_neg h]

theorem tprod_eq_fibre_prod_mul_tprod_fibre_prod {ι κ : Type} (f : ι → ℂ) (u : ι → κ) (S : Finset κ)
    (v₀ : κ) (hv₀ : v₀ ∈ S) (hf : Multipliable f) (hfin : ∀ k : κ, {i : ι | u i = k}.Finite)
    (hS : ∀ k ∈ S, k ≠ v₀ → ∀ i : ι, u i = k → f i = 1) :
    ∏' i : ι, f i
      = (∏ i ∈ (hfin v₀).toFinset, f i) * ∏' k : {k : κ // k ∉ S}, ∏ i ∈ (hfin k.1).toFinset, f i := by
  classical
  by_cases hc : ∏ i ∈ (hfin v₀).toFinset, f i = 0
  · obtain ⟨i₀, -, hi₀⟩ := Finset.prod_eq_zero_iff.mp hc
    have h0 : HasProd f 0 :=
      tendsto_atTop_of_eventually_const (i₀ := {i₀}) fun T hT =>
        Finset.prod_eq_zero (hT (Finset.mem_singleton_self i₀)) hi₀
    rw [h0.tprod_eq, hc, zero_mul]
  · have hmem : ∀ i : ι, i ∈ (hfin v₀).toFinset ↔ u i = v₀ := fun i => by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have hprod : ∀ T : Finset ι, (hfin v₀).toFinset ⊆ T →
        ∏ i ∈ T, (if u i = v₀ then 1 else f i) = (∏ i ∈ T, f i) / ∏ i ∈ (hfin v₀).toFinset, f i := by
      intro T hT
      rw [← Finset.prod_sdiff hT (f := f), ← Finset.prod_sdiff hT (f := fun i => if u i = v₀ then 1 else f i),
        mul_div_cancel_right₀ _ hc]
      rw [Finset.prod_eq_one fun i hi => if_pos ((hmem i).mp hi), mul_one]
      exact Finset.prod_congr rfl fun i hi => if_neg fun h => (Finset.mem_sdiff.mp hi).2 ((hmem i).mpr h)
    have hf' : HasProd (fun i : ι => if u i = v₀ then 1 else f i)
        ((∏' i : ι, f i) / ∏ i ∈ (hfin v₀).toFinset, f i) :=
      (hf.hasProd.div_const _).congr'
        ((Filter.eventually_ge_atTop (hfin v₀).toFinset).mono fun T hT => (hprod T hT).symm)
    have h₂₄ := hasProd_subtype_of_multipliable_of_fibre_prod_eq (fun i : ι => if u i = v₀ then 1 else f i) u S
      (fun k : {k : κ // k ∉ S} => ∏ i ∈ (hfin k.1).toFinset, f i) hf'.multipliable hfin
      (fun k hk i hi => by
        by_cases hkv : k = v₀
        · exact if_pos (hi.trans hkv)
        · exact (if_neg fun h => hkv (hi.symm.trans h)).trans (hS k hk hkv i hi))
      (fun k => Finset.prod_congr rfl fun i hi => if_neg fun h => k.2 (by
        have hik : u i = k.1 := by simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hi
        rw [← hik, h]
        exact hv₀))
    have key : ∏' k : {k : κ // k ∉ S}, ∏ i ∈ (hfin k.1).toFinset, f i
        = (∏' i : ι, f i) / ∏ i ∈ (hfin v₀).toFinset, f i := by
      rw [← hf'.tprod_eq]
      exact h₂₄.tprod_eq
    rw [key, mul_div_cancel₀ _ hc]

theorem LFunDual_heckeDatum_eq_finprod_fibre_mul_tprod_inducedLDual
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v₀ : HeightOneSpectrum (𝓞 ℚ)) (hv₀ : v₀ ∈ S) (s : ℂ)
    (hfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), (primeFibre ℚ K p).Finite)
    (hτ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt τ p)
    (hram : ∀ w ∈ S, w ≠ v₀ → ∀ 𝔓 ∈ primeFibre ℚ K w,
      ¬ IsUnramifiedCharAt (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
    (hmult : Multipliable fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
              uR aR uC kC).dual 𝔓).eval (((LanglandsTunnell.HeckeTate.heckeDatum K
                  (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                      uR aR uC kC).norm 𝔓 : ℂ) ^ (-s)))⁻¹) :
    (LanglandsTunnell.HeckeTate.heckeDatum K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
        uR aR uC kC).LFunDual s =
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v₀, (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
              uR aR uC kC).dual 𝔓).eval (((LanglandsTunnell.HeckeTate.heckeDatum K
                  (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                      uR aR uC kC).norm 𝔓 : ℂ) ^ (-s)))⁻¹) *
        ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
          ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v.1).eval
              (((TateGlobal.localChar τ⁻¹ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) *
                (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)))⁻¹ := by
  have hinv : (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)⁻¹
      = μ⁻¹ * τ⁻¹.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.inv_apply, MonoidHom.mul_apply, MonoidHom.comp_apply, mul_inv]
  have hone : ∀ k ∈ S, k ≠ v₀ → ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) = k →
      (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
              uR aR uC kC).dual 𝔓).eval (((LanglandsTunnell.HeckeTate.heckeDatum K
                  (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                      uR aR uC kC).norm 𝔓 : ℂ) ^ (-s)))⁻¹ = 1 := by
    intro k hk hkv 𝔓 h𝔓
    rw [dual_heckeDatum_eq_one_of_not_isUnramifiedCharAt _ _ _ _ _ _
      (hram k hk hkv 𝔓 ((mem_primeFibre ℚ k 𝔓).mpr h𝔓)), Polynomial.eval_C, inv_one]
  have hfib : ∀ v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
      (∏ 𝔓 ∈ (hfin v.1).toFinset, (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
              uR aR uC kC).dual 𝔓).eval (((LanglandsTunnell.HeckeTate.heckeDatum K
                  (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                      uR aR uC kC).norm 𝔓 : ℂ) ^ (-s)))⁻¹)
        = ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v.1).eval
            (((TateGlobal.localChar τ⁻¹ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) *
              (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)))⁻¹ := by
    intro v
    have hτ' : IsUnramifiedCharAt τ⁻¹ v.1 := (isUnramifiedCharAt_inv_iff τ v.1).mpr (hτ v.1 v.2)
    have hbridge : LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ⁻¹ v.1
        = ((TateGlobal.localChar τ⁻¹ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) := by
      unfold LanglandsTunnell.CubicLambda.eulerCoeff
      exact (if_pos hτ').trans rfl
    have h₂₅ := finprod_inv_eval_euler_heckeDatum_eq_inv_eval_inducedEulerPoly K μ⁻¹ τ⁻¹ uR aR uC kC v.1 hτ'
      (hfin v.1) s
    rw [finprod_mem_eq_finite_toFinset_prod _ (hfin v.1), hbridge] at h₂₅
    rw [← h₂₅]
    refine Finset.prod_congr rfl fun 𝔓 _ => ?_
    have hnorm : (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓
          = (LanglandsTunnell.HeckeTate.heckeDatum K
            (μ⁻¹ * τ⁻¹.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 :=
      rfl
    rw [dual_heckeDatum_eq_euler_heckeDatum_inv, hinv, hnorm]
  rw [LanglandsTunnell.LDatum.LFunDual,
    tprod_eq_fibre_prod_mul_tprod_fibre_prod _ (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) S v₀ hv₀ hmult
      hfin hone,
    finprod_mem_eq_finite_toFinset_prod _ (hfin v₀)]
  exact congrArg (HMul.hMul _) (tprod_congr hfib)

theorem generalLinearGroup_map_transposeInv3 {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (g : GL (Fin 3) A) :
    Matrix.GeneralLinearGroup.map φ (transposeInv3 g) = transposeInv3 (Matrix.GeneralLinearGroup.map φ g) := by
  apply Units.ext
  show (Matrix.transpose ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)).map φ
      = Matrix.transpose (((Matrix.GeneralLinearGroup.map φ g)⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)
  rw [← map_inv (Matrix.GeneralLinearGroup.map φ) g]
  ext i j
  rfl

theorem generalLinearGroup_map_weylPrime3 {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) :
    Matrix.GeneralLinearGroup.map φ (weylPrime3 : GL (Fin 3) A) = weylPrime3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylPrime3, Matrix.GeneralLinearGroup.map_apply]

theorem archComponent3_transposeInv3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archComponent3 (𝓞 ℚ) ℚ (transposeInv3 g) = transposeInv3 (archComponent3 (𝓞 ℚ) ℚ g) := by
  exact generalLinearGroup_map_transposeInv3 _ g

theorem archComponent3_weylPrime3 :
    archComponent3 (𝓞 ℚ) ℚ weylPrime3 = weylPrime3 := by
  exact generalLinearGroup_map_weylPrime3 _

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

theorem localChar_comp_idelicNorm_uniformizerUnit_eq_pow_inertiaDeg
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (𝔓 : HeightOneSpectrum (𝓞 K))
    (hτ : IsUnramifiedCharAt τ (𝔓.under (𝓞 ℚ))) :
    localChar (τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓
        (NumberField.AdelicLevel.uniformizerUnit K 𝔓) =
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
  calc localChar (τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓
          (NumberField.AdelicLevel.uniformizerUnit K 𝔓)
        = τ ((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm (uniformizerIdele K 𝔓)) := rfl
    _ = τ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ)) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal *
          Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ)
            (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ)) t)) := by rw [hN]
    _ = τ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
          rw [map_mul, map_pow, hunit, mul_one]

theorem hasConductorExponentAt_and_stdRootNumberAt_localChar_mul_comp_idelicNorm
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hτu : IsUnitaryChar (𝓞 ℚ) ℚ τ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) (hτ : IsUnramifiedCharAt τ (𝔓.under (𝓞 ℚ)))
    (a : ℕ) (ha : HasConductorExponentAt K 𝔓 (localChar μ 𝔓) a)
    (hu : ‖((localChar μ 𝔓 (NumberField.AdelicLevel.uniformizerUnit K 𝔓) : ℂˣ) : ℂ)‖ = 1)
    (hψ : NumberField.StandardAddChar.psiLocal K 𝔓 ≠ 1) :
    HasConductorExponentAt K 𝔓
        (localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) a ∧
      stdRootNumberAt K 𝔓
          (localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
        (((τ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) ^
              ((a : ℤ) + addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓)) *
          stdRootNumberAt K 𝔓 (localChar μ 𝔓) := by
  haveI := subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  suffices aux : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K)), IsUnramifiedCharAt τ v →
      HasConductorExponentAt K w.1 (localChar μ w.1) a →
      ‖((localChar μ w.1 (NumberField.AdelicLevel.uniformizerUnit K w.1) : ℂˣ) : ℂ)‖ = 1 →
      NumberField.StandardAddChar.psiLocal K w.1 ≠ 1 →
      HasConductorExponentAt K w.1
          (localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w.1) a ∧
        stdRootNumberAt K w.1
            (localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w.1) =
          (((τ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) ^ v.asIdeal.inertiaDeg' w.1.asIdeal) ^
              ((a : ℤ) + addCharLevel (NumberField.StandardAddChar.psiLocal K w.1)) *
            stdRootNumberAt K w.1 (localChar μ w.1) from
    aux (𝔓.under (𝓞 ℚ)) ⟨𝔓, rfl⟩ hτ ha hu hψ
  intro v w hτ ha hu hψ
  have e := NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ τ v w
  have hC0 : HasConductorExponentAt K w.1
      ((localChar τ v).comp (Units.map (Algebra.norm (v.adicCompletion ℚ)))) 0 :=
    LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_zero ℚ K v w (localChar τ v)
      (LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt ℚ τ v hτ)
  have hC : localChar (τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w.1 =
      (localChar τ v).comp (Units.map (Algebra.norm (v.adicCompletion ℚ))) := by
    refine MonoidHom.ext fun x => ?_
    have ex := DFunLike.congr_fun e x
    have lhs : localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w.1 x =
        localChar μ w.1 x *
          localChar (τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w.1 x := rfl
    rw [MonoidHom.mul_apply, lhs] at ex
    exact mul_left_cancel ex
  have hτ' : IsUnramifiedCharAt τ (w.1.under (𝓞 ℚ)) := by
    rw [w.2]
    exact hτ
  have hCval : (localChar τ v).comp (Units.map (Algebra.norm (v.adicCompletion ℚ)))
        (NumberField.AdelicLevel.uniformizerUnit K w.1) =
      τ (uniformizerIdele ℚ v) ^ v.asIdeal.inertiaDeg' w.1.asIdeal := by
    have hunif := localChar_comp_idelicNorm_uniformizerUnit_eq_pow_inertiaDeg K τ w.1 hτ'
    rw [w.2] at hunif
    rw [← hC]
    exact hunif
  have huC : ‖(((localChar τ v).comp (Units.map (Algebra.norm (v.adicCompletion ℚ)))
        (NumberField.AdelicLevel.uniformizerUnit K w.1) : ℂˣ) : ℂ)‖ = 1 := by
    rw [hCval, ← map_pow]
    exact hτu _
  refine ⟨?_, ?_⟩
  · rw [e]
    exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero K w.1
      (localChar μ w.1) _ a ha hC0
  · rw [e, LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero K w.1
      (localChar μ w.1) _ a ha hC0 hu huC hψ, hCval, Units.val_pow_eq_pow_val]

theorem continuous_centralChar_of_form_ne_zero
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hF : X.form ≠ 0) :
    Continuous ⇑X.centralChar := by
  obtain ⟨g₀, hg₀⟩ : ∃ g, X.form g ≠ 0 := Function.ne_iff.mp hF
  have hsc : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀ := by
    have hdiag : Continuous fun a : AdeleRing (𝓞 ℚ) ℚ => Matrix.diagonal fun _ : Fin 3 => a :=
      (continuous_pi fun _ : Fin 3 => continuous_id).matrix_diagonal
    have hs : Continuous ((Matrix.scalar (Fin 3)).toMonoidHom :
        AdeleRing (𝓞 ℚ) ℚ → Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
      hdiag.congr fun a => (Matrix.scalar_apply a).symm
    have h1 : Continuous (centralScalarGL 3 (𝓞 ℚ) ℚ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → AdelicGL 3 (𝓞 ℚ) ℚ) :=
      Continuous.units_map _ hs
    exact h1.mul continuous_const
  have hval : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((X.centralChar z : ℂˣ) : ℂ) := by
    have heq : (fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((X.centralChar z : ℂˣ) : ℂ)) =
        fun z => X.form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀) / X.form g₀ := by
      funext z
      rw [hX.central z g₀, mul_div_cancel_right₀ _ hg₀]
    rw [heq]
    exact (hcont.comp hsc).div_const _
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have hinv : (fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (((X.centralChar z)⁻¹ : ℂˣ) : ℂ)) =
      fun z => ((X.centralChar z⁻¹ : ℂˣ) : ℂ) := by
    funext z
    rw [map_inv]
  rw [hinv]
  exact hval.comp continuous_inv

theorem exists_hasConductorExponentAt_localChar_centralChar
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hF : X.form ≠ 0) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ b : ℕ, HasConductorExponentAt ℚ w (localChar X.centralChar w) b := by
  obtain ⟨b, hb⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ w
    (localChar X.centralChar w)
    (NumberField.TateGlobal.continuous_localChar X.centralChar
      (continuous_centralChar_of_form_ne_zero K ψ μ pins X hX hcont hF) w)
  exact ⟨b, hb⟩

theorem finprod_eq_prod_finprod_fibre_mul_finprod_compl {ι κ M : Type*} [CommMonoid M]
    (f : ι → M) (u : ι → κ) (T : Finset κ) (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ i, f i = (∏ k ∈ T, ∏ᶠ i ∈ u ⁻¹' {k}, f i) * ∏ᶠ i ∈ (u ⁻¹' (↑T : Set κ))ᶜ, f i := by
  classical
  have hT : ∏ᶠ i ∈ u ⁻¹' (↑T : Set κ), f i = ∏ k ∈ T, ∏ᶠ i ∈ u ⁻¹' {k}, f i := by
    have hU : u ⁻¹' (↑T : Set κ) ∩ Function.mulSupport f =
        ⋃ k ∈ (↑T : Set κ), (u ⁻¹' {k} ∩ Function.mulSupport f) := by
      ext i
      simp only [Set.mem_inter_iff, Set.mem_preimage, Finset.mem_coe, Set.mem_iUnion, Set.mem_singleton_iff,
        exists_prop]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨u i, h1, rfl, h2⟩
      · rintro ⟨k, hk, rfl, h2⟩
        exact ⟨hk, h2⟩
    have hd : (↑T : Set κ).PairwiseDisjoint fun k => u ⁻¹' {k} ∩ Function.mulSupport f :=
      fun k _ l _ hkl => Set.disjoint_left.mpr fun i hik hil =>
        hkl ((Set.mem_singleton_iff.mp hik.1).symm.trans (Set.mem_singleton_iff.mp hil.1))
    rw [← finprod_mem_inter_mulSupport f (u ⁻¹' ↑T), hU,
      finprod_mem_biUnion hd T.finite_toSet (fun k _ => hf.subset Set.inter_subset_right), finprod_mem_coe_finset]
    exact Finset.prod_congr rfl fun k _ => finprod_mem_inter_mulSupport f _
  rw [← hT, ← finprod_mem_union' disjoint_compl_right (hf.subset Set.inter_subset_right)
    (hf.subset Set.inter_subset_right), Set.union_compl_self, finprod_mem_univ]

theorem prod_zpow_eq_zpow_sum_of_ne_zero {ι : Type*} (s : Finset ι) (x : ℂ) (hx : x ≠ 0) (e : ι → ℤ) :
    ∏ i ∈ s, x ^ e i = x ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hx, ih]

theorem finprod_primeFibre_stdRootNumberAt_localChar_mul_comp_idelicNorm_eq_zpow_finsum_mul
    (K : Type) [Field K] [NumberField K] (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hσu : IsUnitaryChar (𝓞 ℚ) ℚ σ) (w : HeightOneSpectrum (𝓞 ℚ)) (hfin : (primeFibre ℚ K w).Finite)
    (hσ : IsUnramifiedCharAt σ w) (a : HeightOneSpectrum (𝓞 K) → ℕ)
    (hνa : ∀ 𝔓 ∈ primeFibre ℚ K w, HasConductorExponentAt K 𝔓 (localChar ν 𝔓) (a 𝔓))
    (hνu : ∀ 𝔓 ∈ primeFibre ℚ K w,
      ‖((localChar ν 𝔓 (NumberField.AdelicLevel.uniformizerUnit K 𝔓) : ℂˣ) : ℂ)‖ = 1)
    (hψ : ∀ 𝔓 ∈ primeFibre ℚ K w, NumberField.StandardAddChar.psiLocal K 𝔓 ≠ 1) :
    ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
        (localChar (ν * σ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
      ((σ (uniformizerIdele ℚ w) : ℂˣ) : ℂ) ^
          (∑ᶠ 𝔓 ∈ primeFibre ℚ K w, (w.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
            ((a 𝔓 : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓))) *
        ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar ν 𝔓) := by
  have hw : ∀ 𝔓 ∈ primeFibre ℚ K w, 𝔓.under (𝓞 ℚ) = w := fun 𝔓 h => (mem_primeFibre ℚ w 𝔓).mp h
  have hfac : ∀ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
      (localChar (ν * σ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
      ((σ (uniformizerIdele ℚ w) : ℂˣ) : ℂ) ^ ((w.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
          ((a 𝔓 : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓))) *
        LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar ν 𝔓) := by
    intro 𝔓 h
    have hσ' : IsUnramifiedCharAt σ (𝔓.under (𝓞 ℚ)) := by
      rw [hw 𝔓 h]
      exact hσ
    rw [(hasConductorExponentAt_and_stdRootNumberAt_localChar_mul_comp_idelicNorm K ν σ hσu 𝔓 hσ' (a 𝔓)
      (hνa 𝔓 h) (hνu 𝔓 h) (hψ 𝔓 h)).2, hw 𝔓 h, ← zpow_natCast, ← zpow_mul]
  rw [finprod_mem_congr rfl hfac, finprod_mem_mul_distrib hfin]
  congr 1
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact prod_zpow_eq_zpow_sum_of_ne_zero _ _ (Units.ne_zero _) _

theorem isUnramifiedCharAt_mul (F : Type) [Field F] [NumberField F] (τ σ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (w : HeightOneSpectrum (𝓞 F)) (hτ : IsUnramifiedCharAt τ w) (hσ : IsUnramifiedCharAt σ w) :
    IsUnramifiedCharAt (τ * σ) w := by
  intro t h1 h2
  have e : localChar (τ * σ) w t = localChar τ w t * localChar σ w t := rfl
  rw [e, hτ t h1 h2, hσ t h1 h2, one_mul]

open scoped Classical in

theorem mul_finprod_stdRootNumberAt_eq_mul_finprod_primeFibre_mul_prod_erase_mul_finprod_compl
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (A : ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (hfin : {𝔓 : HeightOneSpectrum (𝓞 K) |
      LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓) ≠ 1}.Finite) :
    A * ∏ᶠ 𝔓 : HeightOneSpectrum (𝓞 K), LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓) =
      A * (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓)) *
        (∏ q ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K q, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓)) *
        ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹' (↑S : Set _))ᶜ,
          LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓) := by
  have hfibre := finprod_eq_prod_finprod_fibre_mul_finprod_compl
    (fun 𝔓 : HeightOneSpectrum (𝓞 K) => LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓))
    (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) S hfin
  have hfib : ∀ q : HeightOneSpectrum (𝓞 ℚ),
      (∏ᶠ 𝔓 ∈ (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹' {q},
          LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓)) =
        ∏ᶠ 𝔓 ∈ primeFibre ℚ K q, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓) :=
    fun _ => rfl
  simp only [hfib] at hfibre
  rw [hfibre, ← Finset.mul_prod_erase S _ hv]
  simp only [mul_assoc]

open scoped Classical in

theorem finprod_absNorm_zpow_pinnedExp_eq_finprod_primeFibre_mul_prod_erase_mul_finprod_compl
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (hfin : {𝔓 : HeightOneSpectrum (𝓞 K) |
      LanglandsTunnell.Converse.pinnedExp K χ 𝔓 ≠ 0}.Finite) :
    ∏ᶠ 𝔓 : HeightOneSpectrum (𝓞 K),
        (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (LanglandsTunnell.Converse.pinnedExp K χ 𝔓) =
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v,
          (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (LanglandsTunnell.Converse.pinnedExp K χ 𝔓)) *
        (∏ q ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K q,
          (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (LanglandsTunnell.Converse.pinnedExp K χ 𝔓)) *
        ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹' (↑S : Set _))ᶜ,
          (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (LanglandsTunnell.Converse.pinnedExp K χ 𝔓) := by
  have hfibre := finprod_eq_prod_finprod_fibre_mul_finprod_compl
    (fun 𝔓 : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (LanglandsTunnell.Converse.pinnedExp K χ 𝔓))
    (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) S
    (hfin.subset fun 𝔓 h he => h (by simp only [he, zpow_zero]))
  have hfib : ∀ q : HeightOneSpectrum (𝓞 ℚ),
      (∏ᶠ 𝔓 ∈ (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹' {q},
          (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (LanglandsTunnell.Converse.pinnedExp K χ 𝔓)) =
        ∏ᶠ 𝔓 ∈ primeFibre ℚ K q, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (LanglandsTunnell.Converse.pinnedExp K χ 𝔓) :=
    fun _ => rfl
  simp only [hfib] at hfibre
  rw [hfibre, ← Finset.mul_prod_erase S _ hv]

theorem stdRootNumberAt_and_pinnedExp_localChar_mul_comp_idelicNorm_eq_of_zero
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hθu : IsUnitaryChar (𝓞 ℚ) ℚ θ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) (hθ : IsUnramifiedCharAt θ (𝔓.under (𝓞 ℚ)))
    (hμ : HasConductorExponentAt K 𝔓 (localChar μ 𝔓) 0)
    (hu : ‖((localChar μ 𝔓 (NumberField.AdelicLevel.uniformizerUnit K 𝔓) : ℂˣ) : ℂ)‖ = 1)
    (hψ : NumberField.StandardAddChar.psiLocal K 𝔓 ≠ 1)
    (hlev : LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓) = 0) :
    LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
          (localChar (μ * θ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
        LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar μ 𝔓) ∧
      LanglandsTunnell.Converse.pinnedExp K
          (μ * θ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 =
        LanglandsTunnell.Converse.pinnedExp K μ 𝔓 := by
  have htwist := hasConductorExponentAt_and_stdRootNumberAt_localChar_mul_comp_idelicNorm K μ θ hθu 𝔓 hθ 0 hμ hu hψ
  refine ⟨?_, ?_⟩
  · rw [htwist.2, hlev, add_zero, Nat.cast_zero, zpow_zero, one_mul]
  · unfold LanglandsTunnell.Converse.pinnedExp
    rw [LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K 𝔓 htwist.1,
      LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K 𝔓 hμ]

theorem exists_forall_lt_hasConductorExponentAt_comp_norm_of_le
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3) (w : HeightOneSpectrum (𝓞 ℚ)) (b : ℕ) :
    ∃ c₀ : ℕ, ∀ (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (c : ℕ), HasConductorExponentAt ℚ w (localChar χ w) c →
      c₀ ≤ c → ∀ P : w.Extension (𝓞 K), ∃ a : ℕ, b < a ∧
        HasConductorExponentAt K P.1 ((localChar χ w).comp (Units.map (Algebra.norm (w.adicCompletion ℚ)))) a := by
  refine ⟨max 12 (b + 1), fun χ c hχ hc P => ?_⟩
  have h12 := le_max_left 12 (b + 1)
  have hb := le_max_right 12 (b + 1)
  obtain ⟨a, hca, ha, -⟩ :=
    LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_of_finrank_eq_three K hdeg w P (localChar χ w) c
      (by omega) hχ
  exact ⟨a, by omega, ha⟩

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

theorem exists_forall_finprod_primeFibre_stdRootNumberAt_localChar_mul_comp_idelicNorm_mul_eq_pow_mul
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμu : IsUnitaryChar (𝓞 K) K μ)
    (b : HeightOneSpectrum (𝓞 K) → ℕ) (hb : ∀ 𝔓, HasConductorExponentAt K 𝔓 (localChar μ 𝔓) (b 𝔓))
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ c₀ : ℕ, ∀ (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (n : ℕ), c₀ ≤ n → HasConductorExponentAt ℚ w (localChar τ w) n →
      (∀ 𝔓 ∈ primeFibre ℚ K w,
        ¬ IsUnramifiedCharAt (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) ∧
      ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsUnitaryChar (𝓞 ℚ) ℚ τ → IsUnitaryChar (𝓞 ℚ) ℚ σ →
        IsUnramifiedCharAt σ w →
          (∀ 𝔓 ∈ primeFibre ℚ K w,
            LanglandsTunnell.Converse.pinnedExp K
                (μ * (τ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 =
              LanglandsTunnell.Converse.pinnedExp K
                (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) ∧
          ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
              (localChar (μ * (τ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
            ((σ (uniformizerIdele ℚ w) : ℂˣ) : ℂ) ^ (3 * n) *
              ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
                (localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) := by
  have hfin : (primeFibre ℚ K w).Finite := primeFibre_finite K w
  obtain ⟨c₅, hc₅⟩ := exists_forall_lt_hasConductorExponentAt_comp_norm_of_le K hdeg w (hfin.toFinset.sup b)
  obtain ⟨c₂, hc₂⟩ := exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq K hdeg w
  refine ⟨max c₅ c₂, fun τ n hn hτn => ?_⟩
  have hb₀ : ∀ 𝔓 ∈ primeFibre ℚ K w, b 𝔓 ≤ hfin.toFinset.sup b := fun 𝔓 h =>
    Finset.le_sup (hfin.mem_toFinset.mpr h)
  have hmem : ∀ P : w.Extension (𝓞 K), P.1 ∈ primeFibre ℚ K w := fun P => (mem_primeFibre ℚ w P.1).mpr P.2
  have hA := hc₅ τ n hτn ((le_max_left c₅ c₂).trans hn)
  choose aE hbaE haE using hA
  have hν₁ : ∀ P : w.Extension (𝓞 K),
      HasConductorExponentAt K P.1
        (localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) P.1) (aE P) := by
    intro P
    rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ τ w P]
    have hcomm : localChar μ P.1 * (localChar τ w).comp (Units.map (Algebra.norm (w.adicCompletion ℚ))) =
        (localChar τ w).comp (Units.map (Algebra.norm (w.adicCompletion ℚ))) * localChar μ P.1 :=
      MonoidHom.ext fun x => by rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_comm]
    rw [hcomm]
    exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt K P.1 _ _ (aE P)
      (b P.1) (haE P) (hb P.1) (lt_of_le_of_lt (hb₀ P.1 (hmem P)) (hbaE P))
  refine ⟨fun 𝔓 h𝔓 hunr => ?_, fun σ hτu hσu hσw => ?_⟩
  ·
    obtain ⟨P, rfl⟩ : ∃ P : w.Extension (𝓞 K), P.1 = 𝔓 := ⟨⟨𝔓, h𝔓⟩, rfl⟩
    have h0 := LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt K
      (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) P.1 hunr
    have h0a := LanglandsTunnell.TateLocal.hasConductorExponentAt_unique K P.1 h0 (hν₁ P)
    have hlt := hbaE P
    omega
  ·
    have hσ0 : ∀ P : w.Extension (𝓞 K), HasConductorExponentAt K P.1
        ((localChar σ w).comp (Units.map (Algebra.norm (w.adicCompletion ℚ)))) 0 := fun P =>
      LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_zero ℚ K w P (localChar σ w)
        (LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt ℚ σ w hσw)
    have hN : μ * (τ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm =
        μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm *
          σ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm :=
      MonoidHom.ext fun x => by simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, mul_assoc]
    have hν₂ : ∀ P : w.Extension (𝓞 K), HasConductorExponentAt K P.1
        (localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm *
          σ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) P.1) (aE P) := by
      intro P
      rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) σ w P]
      exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero K P.1 _ _ (aE P)
        (hν₁ P) (hσ0 P)
    rw [hN]
    refine ⟨fun 𝔓 h𝔓 => ?_, ?_⟩
    · obtain ⟨P, rfl⟩ : ∃ P : w.Extension (𝓞 K), P.1 = 𝔓 := ⟨⟨𝔓, h𝔓⟩, rfl⟩
      unfold LanglandsTunnell.Converse.pinnedExp
      rw [LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K P.1 (hν₂ P),
        LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K P.1 (hν₁ P)]
    ·
      have hν₁u : ∀ 𝔓 ∈ primeFibre ℚ K w,
          ‖((localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓
            (NumberField.AdelicLevel.uniformizerUnit K 𝔓) : ℂˣ) : ℂ)‖ = 1 := by
        intro 𝔓 h𝔓
        obtain ⟨P, rfl⟩ : ∃ P : w.Extension (𝓞 K), P.1 = 𝔓 := ⟨⟨𝔓, h𝔓⟩, rfl⟩
        have hμP : ‖((localChar μ P.1 (NumberField.AdelicLevel.uniformizerUnit K P.1) : ℂˣ) : ℂ)‖ = 1 := hμu _
        rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ τ w P, MonoidHom.mul_apply,
          Units.val_mul, norm_mul, hμP, one_mul]
        exact hτu _
      have hψ : ∀ 𝔓 ∈ primeFibre ℚ K w, NumberField.StandardAddChar.psiLocal K 𝔓 ≠ 1 := fun 𝔓 _ =>
        LanglandsTunnell.TateLocal.psiLocal_ne_one K 𝔓
      have hν₁' : ∀ 𝔓 ∈ primeFibre ℚ K w, HasConductorExponentAt K 𝔓
          (localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
          (Function.extend Subtype.val aE (fun _ => 0) 𝔓) := by
        intro 𝔓 h𝔓
        obtain ⟨P, rfl⟩ : ∃ P : w.Extension (𝓞 K), P.1 = 𝔓 := ⟨⟨𝔓, h𝔓⟩, rfl⟩
        rw [Subtype.val_injective.extend_apply]
        exact hν₁ P
      have hP := finprod_primeFibre_stdRootNumberAt_localChar_mul_comp_idelicNorm_eq_zpow_finsum_mul K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) σ hσu w hfin hσw
        (Function.extend Subtype.val aE (fun _ => 0)) hν₁' hν₁u hψ
      have h2 := hc₂ (localChar τ w) n ((le_max_right c₅ c₂).trans hn) hτn aE haE
      have h2' : ∑ᶠ P : w.Extension (𝓞 K), (w.asIdeal.inertiaDeg' P.1.asIdeal : ℤ) *
          (((Function.extend Subtype.val aE (fun _ => 0) P.1 : ℕ) : ℤ) +
            LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1)) = 3 * (n : ℤ) := by
        rw [← h2]
        exact finsum_congr fun P => by rw [Subtype.val_injective.extend_apply]
      have hexp : ∑ᶠ 𝔓 ∈ primeFibre ℚ K w, (w.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
          (((Function.extend Subtype.val aE (fun _ => 0) 𝔓 : ℕ) : ℤ) +
            LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓)) =
          ((3 * n : ℕ) : ℤ) := by
        rw [← finsum_set_coe_eq_finsum_mem, Nat.cast_mul, Nat.cast_ofNat]
        exact h2'
      rw [hexp, zpow_natCast] at hP
      exact hP

theorem isAdmissibleTwist_mul_comp_idelicNorm_of_isAdmissibleTwist
    (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hτ : IsAdmissibleTwist ℚ τ) :
    IsAdmissibleTwist K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) := by
  obtain ⟨h1, h2, h3⟩ := hμ
  obtain ⟨h1', h2', h3'⟩ := hτ
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  ·
    have hN : (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) =
        Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (Units.map (Algebra.norm ℚ) u) := by
      ext
      show (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).adelicNorm
          (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) =
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (Algebra.norm ℚ (u : K))
      exact M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap ℚ K (u : K)
    rw [MonoidHom.mul_apply, h1 u, one_mul, MonoidHom.comp_apply, hN]
    exact h1' _
  ·
    have hc : Continuous (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm :=
      Continuous.units_map _ (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange ℚ K)
    exact h2.mul (h2'.comp hc)
  · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h3 x, one_mul]
    exact h3' _

open Complex in

theorem eq_of_differentiable_of_eqOn_halfPlane (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (σ : ℝ) (h : ∀ s : ℂ, σ < s.re → f s = g s) : ∀ s : ℂ, f s = g s := by
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz : ((σ + 1 : ℝ) : ℂ) ∈ {s : ℂ | σ < s.re} := by simp
  have hev : f =ᶠ[nhds ((σ + 1 : ℝ) : ℂ)] g :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun s hs => h s hs
  intro s
  exact (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ _) hev (Set.mem_univ s)

theorem eliminate_right (E₁ E₂ Λ₁ Λ₂ e₁ e₂ Zv₁ Pv Pw₁ Pw₂ q₁' q₂ A₁ A : ℂ → ℂ) (κ : ℂ) (σ : ℝ)
    (hE₁ : Differentiable ℂ E₁) (hE₂ : Differentiable ℂ E₂) (hΛ₁ : Differentiable ℂ Λ₁) (hΛ₂ : Differentiable ℂ Λ₂)
    (he₁ : Differentiable ℂ e₁) (he₂ : Differentiable ℂ e₂) (hPv : Differentiable ℂ Pv) (hPw₁ : Differentiable ℂ Pw₁)
    (hPw₂ : Differentiable ℂ Pw₂) (hq₁ : Differentiable ℂ q₁') (hq₂ : Differentiable ℂ q₂)
    (hA₁ : ∀ s : ℂ, σ < s.re → A₁ s ≠ 0)
    (hR₁ : ∀ s : ℂ, σ < s.re → A₁ s * E₁ s = κ * A s * Zv₁ s * Pw₁ s * Λ₁ s * e₁ s)
    (hR₂ : ∀ s : ℂ, σ < s.re → A₁ s * E₂ s = κ * A s * Pv s * Pw₂ s * Λ₂ s * e₂ s)
    (hZv : ∀ s : ℂ, σ < s.re → Zv₁ s * q₂ s = q₁' s) :
    ∀ s : ℂ, E₁ s * Pv s * Pw₂ s * Λ₂ s * e₂ s * q₂ s = E₂ s * q₁' s * Pw₁ s * Λ₁ s * e₁ s := by
  refine eq_of_differentiable_of_eqOn_halfPlane _ _ (by fun_prop) (by fun_prop) σ fun s hs => ?_
  have h1 := hR₁ s hs
  have h2 := hR₂ s hs
  have h3 := hZv s hs
  apply mul_left_cancel₀ (hA₁ s hs)
  linear_combination (Pv s * Pw₂ s * Λ₂ s * e₂ s * q₂ s) * h1 +
    (κ * A s * Pw₁ s * Λ₁ s * e₁ s * Pv s * Pw₂ s * Λ₂ s * e₂ s) * h3 - (q₁' s * Pw₁ s * Λ₁ s * e₁ s) * h2

theorem eliminate_left
    (E₁ E₂ Λ₁ Λ₂ Λd₁ Λd₂ C₁ C₂ e₁ e₂ ed₁ ed₂ Zd₁ γv Pv γw₁ γw₂ Pw₁ Pw₂ r₁' q₁' q₂ r₂ A₂ Ad : ℂ → ℂ) (c : ℂ) (σ : ℝ)
    (hE₁ : Differentiable ℂ E₁) (hE₂ : Differentiable ℂ E₂) (hΛ₁ : Differentiable ℂ Λ₁) (hΛ₂ : Differentiable ℂ Λ₂)
    (hC₁ : Differentiable ℂ C₁) (hC₂ : Differentiable ℂ C₂) (he₁ : Differentiable ℂ e₁) (he₂ : Differentiable ℂ e₂)
    (hed₁ : Differentiable ℂ ed₁) (hed₂ : Differentiable ℂ ed₂) (hγv : Differentiable ℂ γv) (hPv : Differentiable ℂ Pv)
    (hγw₁ : Differentiable ℂ γw₁) (hγw₂ : Differentiable ℂ γw₂) (hPw₁ : Differentiable ℂ Pw₁)
    (hPw₂ : Differentiable ℂ Pw₂) (hr₁ : Differentiable ℂ r₁') (hq₁ : Differentiable ℂ q₁') (hq₂ : Differentiable ℂ q₂)
    (hr₂ : Differentiable ℂ r₂)
    (hA₂ : ∀ s : ℂ, s.re < σ → A₂ (1 - s) ≠ 0)
    (hL₁ : ∀ s : ℂ, s.re < σ →
      A₂ (1 - s) * E₁ s = c * Ad (1 - s) * Zd₁ (1 - s) * (γw₁ s * Pw₁ s) * Λd₁ (1 - s) * ed₁ s)
    (hL₂ : ∀ s : ℂ, s.re < σ →
      A₂ (1 - s) * E₂ s = c * Ad (1 - s) * (γv s * Pv s) * (γw₂ s * Pw₂ s) * Λd₂ (1 - s) * ed₂ s)
    (hfe₁ : ∀ s : ℂ, Λ₁ s = C₁ s * Λd₁ (1 - s)) (hfe₂ : ∀ s : ℂ, Λ₂ s = C₂ s * Λd₂ (1 - s))
    (hZd : ∀ s : ℂ, s.re < σ → Zd₁ (1 - s) * (q₂ s * r₂ s) = r₁' s * q₁' s) :
    ∀ s : ℂ,
      E₁ s * Pv s * Pw₂ s * Λ₂ s * e₂ s * q₂ s * (γv s * γw₂ s * ed₂ s * r₂ s * C₁ s * e₁ s) =
        E₂ s * q₁' s * Pw₁ s * Λ₁ s * e₁ s * (r₁' s * γw₁ s * ed₁ s * C₂ s * e₂ s) := by
  have main : ∀ s : ℂ, s.re < σ →
      E₁ s * Pv s * Pw₂ s * Λ₂ s * e₂ s * q₂ s * (γv s * γw₂ s * ed₂ s * r₂ s * C₁ s * e₁ s) =
        E₂ s * q₁' s * Pw₁ s * Λ₁ s * e₁ s * (r₁' s * γw₁ s * ed₁ s * C₂ s * e₂ s) := by
    intro s hs
    have h1 := hL₁ s hs
    have h2 := hL₂ s hs
    have h3 := hZd s hs
    rw [hfe₁ s, hfe₂ s]
    apply mul_left_cancel₀ (hA₂ s hs)
    linear_combination
      (Pv s * Pw₂ s * C₂ s * Λd₂ (1 - s) * e₂ s * q₂ s * γv s * γw₂ s * ed₂ s * r₂ s * C₁ s * e₁ s) * h1 +
        (c * Ad (1 - s) * γw₁ s * Pw₁ s * Λd₁ (1 - s) * ed₁ s * Pv s * Pw₂ s * C₂ s * Λd₂ (1 - s) * e₂ s * γv s *
            γw₂ s * ed₂ s * C₁ s * e₁ s) * h3 -
          (q₁' s * Pw₁ s * C₁ s * Λd₁ (1 - s) * e₁ s * r₁' s * γw₁ s * ed₁ s * C₂ s * e₂ s) * h2
  have key := eq_of_differentiable_of_eqOn_halfPlane
    (fun t : ℂ => E₁ (1 - t) * Pv (1 - t) * Pw₂ (1 - t) * Λ₂ (1 - t) * e₂ (1 - t) * q₂ (1 - t) *
      (γv (1 - t) * γw₂ (1 - t) * ed₂ (1 - t) * r₂ (1 - t) * C₁ (1 - t) * e₁ (1 - t)))
    (fun t : ℂ => E₂ (1 - t) * q₁' (1 - t) * Pw₁ (1 - t) * Λ₁ (1 - t) * e₁ (1 - t) *
      (r₁' (1 - t) * γw₁ (1 - t) * ed₁ (1 - t) * C₂ (1 - t) * e₂ (1 - t)))
    (by fun_prop) (by fun_prop) (1 - σ) fun t ht =>
      main (1 - t) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  intro s
  simpa only [sub_sub_cancel] using key (1 - s)

theorem eq_of_mul_eq_mul_of_exists_ne_zero (X α β : ℂ → ℂ) (hX : Differentiable ℂ X) (hα : Differentiable ℂ α)
    (hβ : Differentiable ℂ β) (h : ∀ s : ℂ, X s * α s = X s * β s) (h₀ : ∃ s₀ : ℂ, X s₀ ≠ 0) : ∀ s : ℂ, α s = β s := by
  obtain ⟨s₀, hs₀⟩ := h₀
  have hev : α =ᶠ[nhds s₀] β :=
    (hX.continuous.continuousAt.eventually_ne hs₀).mono fun s hs => mul_left_cancel₀ hs (h s)
  intro s
  exact (hα.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hβ.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ _) hev (Set.mem_univ s)

theorem eval_cpow_ne_zero_of_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) (N : ℝ) (hN : 1 < N) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Q.eval ((N : ℂ) ^ (-s)) ≠ 0 := by
  obtain ⟨Q₀, hQ₀, hX⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ 0
  rw [map_zero, sub_zero] at hQ₀ hX
  have h0 : Q₀.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact fun h => hX (Polynomial.X_dvd_iff.mpr h)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_ne_fun (Polynomial.continuous Q₀) continuous_const).mem_nhds h0)
  refine ⟨-Real.logb N δ, fun s hs => ?_⟩
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN
  have hz : ((N : ℂ) ^ (-s)) ≠ 0 := fun h =>
    (Complex.ofReal_ne_zero.mpr hNpos.ne') ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hmem : ((N : ℂ) ^ (-s)) ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_cpow_eq_rpow_re_of_pos hNpos, Complex.neg_re]
    exact (Real.lt_logb_iff_rpow_lt hN hδ).mp (by linarith)
  rw [hQ₀, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact mul_ne_zero (pow_ne_zero _ hz) (hball hmem)

theorem exists_forall_mem_neg_re_lt (m : Multiset ℂ) : ∃ σ : ℝ, ∀ μ ∈ m, -μ.re < σ := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, fun μ hμ => absurd hμ (Multiset.notMem_zero μ)⟩
  | cons a m ih =>
    obtain ⟨σ, hσ⟩ := ih
    refine ⟨max σ (-a.re + 1), fun μ hμ => ?_⟩
    rcases Multiset.mem_cons.mp hμ with rfl | hμ
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact lt_of_lt_of_le (hσ μ hμ) (le_max_left _ _)

theorem gammaC_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.Gammaℂ z ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero fun h => ?_) (Complex.Gamma_ne_zero_of_re_pos hz)
  have h2 := ((Complex.cpow_eq_zero_iff _ _).mp h).1
  exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h2

theorem prod_map_gammaR_ne_zero (m : Multiset ℂ) (s : ℂ) (h : ∀ μ ∈ m, 0 < (s + μ).re) :
    (m.map fun μ => Complex.Gammaℝ (s + μ)).prod ≠ 0 := by
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨μ, hμ, hμ0⟩ := Multiset.mem_map.mp h0
  exact Complex.Gammaℝ_ne_zero_of_re_pos (h μ hμ) hμ0

theorem prod_map_gammaC_ne_zero (m : Multiset ℂ) (s : ℂ) (h : ∀ μ ∈ m, 0 < (s + μ).re) :
    (m.map fun μ => Complex.Gammaℂ (s + μ)).prod ≠ 0 := by
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨μ, hμ, hμ0⟩ := Multiset.mem_map.mp h0
  exact gammaC_ne_zero_of_re_pos (h μ hμ) hμ0

theorem archFactor_ne_zero_and_archFactorDual_ne_zero {ι : Type} (D : LanglandsTunnell.LDatum ι) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → D.archFactor s ≠ 0 ∧ D.archFactorDual s ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_forall_mem_neg_re_lt (D.gammaR + D.gammaC + D.gammaRDual + D.gammaCDual)
  refine ⟨σ, fun s hs => ?_⟩
  have key : ∀ μ ∈ D.gammaR + D.gammaC + D.gammaRDual + D.gammaCDual, 0 < (s + μ).re := fun μ hμ => by
    rw [Complex.add_re]; linarith [hσ μ hμ]
  refine ⟨mul_ne_zero (prod_map_gammaR_ne_zero _ _ fun μ hμ => key μ ?_)
      (prod_map_gammaC_ne_zero _ _ fun μ hμ => key μ ?_),
    mul_ne_zero (prod_map_gammaR_ne_zero _ _ fun μ hμ => key μ ?_)
      (prod_map_gammaC_ne_zero _ _ fun μ hμ => key μ ?_)⟩ <;>
    simp only [Multiset.mem_add, hμ, true_or, or_true]

theorem componentAt3_localToAdelic3_self (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v g) = g := by
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (LanglandsTunnell.CubicInduction.finMatN (Fin 3) (𝓞 ℚ) ℚ
        (LanglandsTunnell.CubicInduction.localMatN (Fin 3) (𝓞 ℚ) ℚ v (g : Matrix (Fin 3) (Fin 3) _))) =
    (g : Matrix (Fin 3) (Fin 3) _)
  rw [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, LanglandsTunnell.CubicInduction.mapMatrix_fin_finMatN,
    LanglandsTunnell.CubicInduction.mapMatrix_localMatN_self]

theorem componentAt3_localToAdelic3_of_ne
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 ℚ)) (hwv : w ≠ v) (g : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v g) = 1 := by
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (LanglandsTunnell.CubicInduction.finMatN (Fin 3) (𝓞 ℚ) ℚ
        (LanglandsTunnell.CubicInduction.localMatN (Fin 3) (𝓞 ℚ) ℚ v (g : Matrix (Fin 3) (Fin 3) _))) = _
  rw [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, LanglandsTunnell.CubicInduction.mapMatrix_fin_finMatN,
    LanglandsTunnell.CubicInduction.mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hwv, Units.val_one]

noncomputable def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [archMat3, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, NumberField.AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [archMat3, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, NumberField.AdelicLevel.adeleFin_apply]

theorem archMat3_one : archMat3 1 = 1 :=
  LanglandsTunnell.CubicInduction.matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  LanglandsTunnell.CubicInduction.matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

noncomputable def archEmbed3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun g :=
    { val := archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      inv := archMat3 ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

theorem archComponent3_archEmbed3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archEmbed3 g) = g := by
  apply Units.ext
  change RingHom.mapMatrix (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
      (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) = (g : Matrix (Fin 3) (Fin 3) _)
  exact mapMatrix_arch_archMat3 _

theorem componentAt3_archEmbed3 (w : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ w (archEmbed3 g) = 1 := by
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) = _
  rw [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, mapMatrix_fin_archMat3, map_one, Units.val_one]

theorem componentAt3_weylPrime3 (w : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ w (weylPrime3 : AdelicGL 3 (𝓞 ℚ) ℚ) = (weylPrime3 : LocalGL3 w) := by
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      ((weylPrime3 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) _) =
    ((weylPrime3 : LocalGL3 w) : Matrix (Fin 3) (Fin 3) _)
  rw [LanglandsTunnell.CubicInduction.weylPrime3_coe, LanglandsTunnell.CubicInduction.weylPrime3_coe,
    RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem weylPrime3_mem_localMaximalCompact3 (w : HeightOneSpectrum (𝓞 ℚ)) :
    (weylPrime3 : LocalGL3 w) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
  have hinv : ((weylPrime3⁻¹ : LocalGL3 w) : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) =
      !![1, 0, 0; 0, 0, 1; 0, 1, 0] := rfl
  rw [LanglandsTunnell.CubicInduction.mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [LanglandsTunnell.CubicInduction.weylPrime3_coe]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hinv]
    fin_cases i <;> fin_cases j <;> simp

theorem componentAt3_transposeInv3 (w : HeightOneSpectrum (𝓞 ℚ)) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ w (transposeInv3 x) = transposeInv3 (componentAt3 (𝓞 ℚ) ℚ w x) := by
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (Matrix.transpose ((x⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) _)) =
    Matrix.transpose (((componentAt3 (𝓞 ℚ) ℚ w x)⁻¹ : LocalGL3 w) : Matrix (Fin 3) (Fin 3) _)
  rw [← map_inv, RingHom.mapMatrix_apply, Matrix.transpose_map]
  rfl

open scoped Matrix in

theorem transposeInv3_mul
    (w : HeightOneSpectrum (𝓞 ℚ)) (a b : LocalGL3 w) :
    transposeInv3 (a * b) = transposeInv3 a * transposeInv3 b := by
  apply Units.ext
  show ((((a * b)⁻¹ : LocalGL3 w) : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)))ᵀ =
    (((a⁻¹ : LocalGL3 w) : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)))ᵀ *
      (((b⁻¹ : LocalGL3 w) : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)))ᵀ
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

open scoped Matrix in

theorem transposeInv3_one
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    transposeInv3 (1 : LocalGL3 w) = 1 := by
  apply Units.ext
  show (((1 : LocalGL3 w)⁻¹ : LocalGL3 w) : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ))ᵀ = _
  simp

theorem transposeInv3_mem_localMaximalCompact3
    (w : HeightOneSpectrum (𝓞 ℚ)) (k : LocalGL3 w) (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) :
    transposeInv3 k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
  rw [mem_localMaximalCompact3_iff (R := 𝓞 ℚ) (K := ℚ) (v := w)] at hk ⊢
  exact ⟨fun i j => hk.2 j i, fun i j => hk.1 j i⟩

theorem longWeyl3_mem_localMaximalCompact3
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    (longWeyl3 : LocalGL3 w) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
  have hinv : ((longWeyl3⁻¹ : LocalGL3 w) : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [longWeyl3_coe]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hinv]
    fin_cases i <;> fin_cases j <;> simp

theorem dualWhittakerFn3_rightInvariant_off
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S) :
    ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v,
      dualWhittakerFn3 (X.whittakerLoc v) (y * k) = dualWhittakerFn3 (X.whittakerLoc v) y := by
  intro v hv k hk y
  have hsph := hX.spherical v fun hb => hv ((hSbad v).1 hb)
  simp only [dualWhittakerFn3_apply]
  rw [transposeInv3_mul v y k, ← mul_assoc]
  exact hsph.1 (longWeyl3 * transposeInv3 y) (transposeInv3 k) (transposeInv3_mem_localMaximalCompact3 v k hk)

theorem dualWhittakerFn3_one_off
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S) :
    ∀ v, v ∉ S → dualWhittakerFn3 (X.whittakerLoc v) 1 = 1 := by
  intro v hv
  have hnb : ¬ IsBadPlace K μ v := fun hb => hv ((hSbad v).1 hb)
  have hsph := hX.spherical v hnb
  have hw : X.whittakerLoc v longWeyl3 = X.whittakerLoc v 1 := by
    simpa using hsph.1 1 longWeyl3 (longWeyl3_mem_localMaximalCompact3 v)
  simp only [dualWhittakerFn3_apply, transposeInv3_one, mul_one]
  rw [hw]
  exact (hexp.2 v hnb (_hlev v hnb)).1

theorem dualWhittaker_factorises_off
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S) :
    ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      X.dualWhittaker x =
        dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ x) *
          ∏ v ∈ T, dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v x) := by
  intro x T hST hxT
  have hD1 := dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn K ψ μ D U gen X hX hcont
  exact dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod_of_isCubicInductionDataOn K X hX hD1 x T
    (fun w hw => hST ((hSbad w).1 hw)) hxT

theorem apply_eq_one_of_isAdmissibleTwist_of_isUnramifiedCharAt_off
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hχU : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → TateGlobal.IsUnramifiedCharAt χ w) :
    ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1 := by
  exact NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous ℚ χ hχ.2.1 S hχU

theorem isAdmissibleTwist_inv
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ) :
    IsAdmissibleTwist ℚ χ⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := hχ
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.inv_apply, h1 u, inv_one]
  · exact h2.inv
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h3 x, inv_one]

theorem isUnramifiedCharAt_inv
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 ℚ)) (hχ : TateGlobal.IsUnramifiedCharAt χ w) :
    TateGlobal.IsUnramifiedCharAt χ⁻¹ w := by
  intro t ht ht'
  have h := hχ t ht ht'
  change (TateGlobal.localChar χ w t)⁻¹ = 1
  rw [h, inv_one]

theorem isAdmissibleTwist_mul (χ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hη : IsAdmissibleTwist ℚ η) : IsAdmissibleTwist ℚ (χ * η) := by
  obtain ⟨h1, h2, h3⟩ := hχ
  obtain ⟨h1', h2', h3'⟩ := hη
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.mul_apply, h1 u, h1' u, one_mul]
  · exact h2.mul h2'
  · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h3 x, h3' x, one_mul]

theorem isArchCompAt_mul_of_zero_zero (χ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (w : InfinitePlace ℚ)
    (hχ : IsArchCompAt ℚ χ w 0 0) (hη : IsArchCompAt ℚ η w 0 0) : IsArchCompAt ℚ (χ * η) w 0 0 := by
  intro x
  have hx := hχ x
  have hx' := hη x
  simp only [mul_zero, Complex.cpow_zero, zpow_zero, one_mul] at hx hx' ⊢
  change ((((χ * η) (archUnitHom w x) : ℂˣ)) : ℂ) = 1
  change (((χ (archUnitHom w x) : ℂˣ)) : ℂ) = 1 at hx
  change (((η (archUnitHom w x) : ℂˣ)) : ℂ) = 1 at hx'
  rw [MonoidHom.mul_apply, Units.val_mul, hx, hx', one_mul]

theorem localChar_inv (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    localChar χ⁻¹ w = (localChar χ w)⁻¹ := by
  exact MonoidHom.ext fun _ => rfl

theorem transposeInv3_mul' {A : Type*} [CommRing A] (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  apply Units.ext
  simp only [transposeInv3, mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem transposeInv3_transposeInv3' {A : Type*} [CommRing A] (g : GL (Fin 3) A) :
    transposeInv3 (transposeInv3 g) = g := by
  apply Units.ext
  simp only [transposeInv3, Units.inv_mk, Matrix.transpose_transpose]

theorem isOpen_map_conj' (v : HeightOneSpectrum (𝓞 ℚ)) (U : Subgroup (LocalGL3 v))
    (hU : IsOpen (U : Set (LocalGL3 v))) (g : LocalGL3 v) :
    IsOpen ((U.map (MulAut.conj g).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have : ((U.map (MulAut.conj g).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)) '' (U : Set (LocalGL3 v)) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Homeomorph.trans_apply,
      Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight, SetLike.mem_coe]
  rw [this]
  exact (Homeomorph.isOpenMap _) _ hU

theorem deepTwist_localFE_of_ne_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW0 : W ≠ 0)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h) :
    ∃ c₀ : ℕ, 1 ≤ c₀ ∧
      ∀ (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v τ c →
        ‖(τ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1 →
        c₀ ≤ c →
        (letI := localBorel ℚ v
        ∃ σ₀ σ₁ : ℝ,
          (∀ g : LocalGL3 v,
            ∃ P : ℂ → ℂ,
              (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
                P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
              IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g = P s) ∧
              IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                    W τ (1 - s) g =
                  ((ωv (-1) : ℂˣ) : ℂ) * ((τ (-1) : ℂˣ) : ℂ) *
                    (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ωv * τ) *
                      LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v τ ^ 2 *
                        (Ideal.absNorm v.asIdeal : ℂ) ^ ((3 * (c : ℂ)) * (1 / 2 - s))) * P s)) ∧
        (∃ (g : LocalGL3 v) (s : ℂ), σ₀ < s.re ∧
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g ≠ 0)) := by
  classical
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, W g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hW0 (funext h)
  set c : ℂ := (W g₀)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hg₀
  set W' : LocalGL3 v → ℂ := fun g => c * W (g * g₀) with hW'
  have hW'def : ∀ g, W' g = c * W (g * g₀) := fun g => rfl
  have hW'1 : W' 1 = 1 := by rw [hW'def, one_mul, hc]; exact inv_mul_cancel₀ hg₀
  have hW'law : IsGL3PsiWhittakerFn ψv W' := by
    intro x y z g
    rw [hW'def, hW'def, mul_assoc, hW x y z (g * g₀)]
    ring
  have hW'eq : W' = c • gl3AmbientRightTranslate (R := ℂ) g₀ W := by
    funext g; simp only [hW'def, Pi.smul_apply, gl3AmbientRightTranslate_apply, smul_eq_mul]
  have hW'mem : W' ∈ gl3CyclicSubspace W := by
    rw [hW'eq]; exact Submodule.smul_mem _ c (Submodule.subset_span ⟨g₀, rfl⟩)
  have hle : gl3CyclicSubspace W' ≤ gl3CyclicSubspace W :=
    Submodule.span_le.mpr (by rintro _ ⟨h, rfl⟩; exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h hW'mem)
  have hirr' : ∀ F ∈ gl3CyclicSubspace W', F ≠ 0 → W' ∈ gl3CyclicSubspace F := fun F hF hF0 => by
    have hWF := hirr F (hle hF) hF0
    rw [hW'eq]; exact Submodule.smul_mem _ c (gl3AmbientRightTranslate_mem_gl3CyclicSubspace F g₀ hWF)
  have hsm' : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W' (g * k) = W' g := by
    obtain ⟨Uv, hUo, hUv⟩ := hsm
    refine ⟨Uv.map (MulAut.conj g₀).toMonoidHom, isOpen_map_conj' v Uv hUo g₀, ?_⟩
    rintro k ⟨k', hk', rfl⟩ g
    rw [hW'def, hW'def]
    congr 1
    have : g * ((MulAut.conj g₀).toMonoidHom k') * g₀ = g * g₀ * k' := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this]
    exact hUv k' hk' (g * g₀)
  have hadm' : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W',
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) :=
    fun Uv hUo => by
      obtain ⟨B, hB⟩ := hadm Uv hUo
      exact ⟨B, fun F hF hFk => hB F (hle hF) hFk⟩
  have hω' : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W' (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W' h := fun t h => by
    rw [hW'def, hW'def, mul_assoc, hω t (h * g₀)]
    ring
  have hψ1 : ψv ≠ 1 := by rw [hψinv]; exact inv_ne_one.mpr (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v)
  have hW'0 : W' ≠ 0 := fun h0 => by
    have h1 := congrFun h0 1
    rw [hW'1] at h1
    exact one_ne_zero h1
  have hmult' : HasWhittakerMultOne ψv W' :=
    hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace v ψv hψ1 W' hW'0 hirr' hsm' hadm'
  obtain ⟨c₀, hc₀, hmain⟩ :=
    exists_exists_forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero
      v ψv hψinv W' hW'law hW'1 hmult' hirr' hsm' hadm' ωv hωu hω'

  letI := localBorel ℚ v
  have hdualW' : ∀ h : LocalGL3 v, dualWhittakerFn3 W' h = c * dualWhittakerFn3 W (h * transposeInv3 g₀) := by
    intro h
    simp only [dualWhittakerFn3_apply, hW'def, transposeInv3_mul', transposeInv3_transposeInv3', mul_assoc]
  have hZ30 : ∀ (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v),
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W' χ s g =
        c * localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s (g * g₀) := by
    intro χ s g
    simp only [localZeta30, hW'def, mul_assoc]
    rw [← integral_const_mul]
  have hZd : ∀ (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v),
      localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W' χ s g =
        c * localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ s
          (g * g₀) := by
    intro χ s g
    simp only [localZetaDual31, localZeta31, hdualW', transposeInv3_mul', mul_assoc]
    rw [← integral_const_mul]
    congr 1
    funext a
    rw [integral_const_mul]
    ring
  refine ⟨c₀, hc₀, fun τ cc hτ hτu hcle => ?_⟩
  obtain ⟨σ₀, σ₁, hall, ⟨g₁, s₁, hs₁, hne₁⟩⟩ := hmain τ cc hτ hτu hcle
  refine ⟨σ₀, σ₁, fun g => ?_, ⟨g₁ * g₀, s₁, hs₁, ?_⟩⟩
  · obtain ⟨P, ⟨Q, m, hP⟩, hconv, hZ, hconv31, hZdual⟩ := hall (g * g₀⁻¹)
    have hgg : g * g₀⁻¹ * g₀ = g := by group
    have hZWg : ∀ s : ℂ, localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g =
        c⁻¹ * localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W' τ s (g * g₀⁻¹) := by
      intro s; rw [hZ30, hgg, inv_mul_cancel_left₀ hc0]
    have hZdWg : ∀ s : ℂ,
        localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W τ s g =
          c⁻¹ * localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W' τ s
            (g * g₀⁻¹) := by
      intro s; rw [hZd, hgg, inv_mul_cancel_left₀ hc0]
    have hT : weylPrime3 * transposeInv3 (g * g₀⁻¹) * transposeInv3 g₀ = weylPrime3 * transposeInv3 g := by
      rw [mul_assoc, ← transposeInv3_mul', hgg]
    refine ⟨fun s => c⁻¹ * P s, ⟨c⁻¹ • Q, m, fun s => ?_⟩, ?_, ?_, ?_, ?_⟩
    · show c⁻¹ * P s = _
      rw [hP s, Polynomial.eval_smul, smul_eq_mul, mul_assoc]
    · intro s hs
      have hi := (hconv s hs).const_mul c⁻¹
      refine hi.congr (Filter.Eventually.of_forall fun a => ?_)
      show c⁻¹ * (W' (iotaGL (diagUnitGL2 a) * (g * g₀⁻¹)) * _ * _) = _
      rw [hW'def, mul_assoc (iotaGL (diagUnitGL2 a)), hgg, mul_assoc c, mul_assoc c, inv_mul_cancel_left₀ hc0]
    · intro s hs
      show _ = c⁻¹ * P s
      rw [hZWg, hZ s hs]
    · intro s hs
      have hi := (hconv31 s hs).const_mul c⁻¹
      refine hi.congr (Filter.Eventually.of_forall fun p => ?_)
      show c⁻¹ * (dualWhittakerFn3 W' (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
        (weylPrime3 * transposeInv3 (g * g₀⁻¹))) * _ * _) = _
      rw [hdualW', mul_assoc (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2), hT, mul_assoc c, mul_assoc c,
        inv_mul_cancel_left₀ hc0]
    · intro s hs
      show _ = _ * (c⁻¹ * P s)
      rw [hZdWg, hZdual s hs]
      ring
  · have h := hZ30 τ s₁ g₁
    rw [← inv_mul_cancel_left₀ hc0
      (localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s₁ (g₁ * g₀)), ← h]
    exact mul_ne_zero (inv_ne_zero hc0) hne₁

section SignFlipTransport

variable {A : Type*} [Field A]

noncomputable def dflip : GL (Fin 3) A :=
  iotaGL (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Aˣ) * NumberField.AdelicLevel.diagOne (-1 : Aˣ))

theorem dflip_val : ((dflip : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dflip, iotaGL, embedMat2, NumberField.AdelicLevel.diagOne, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Units.val_neg, Matrix.diagonal]

theorem dflip_mul_dflip : (dflip : GL (Fin 3) A) * dflip = 1 := by
  apply Units.ext
  rw [Units.val_mul, dflip_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem dflip_inv : (dflip : GL (Fin 3) A)⁻¹ = dflip :=
  inv_eq_of_mul_eq_one_right dflip_mul_dflip

theorem dflip_conj_upperUnipotent3 (x y z : A) :
    (dflip : GL (Fin 3) A) * upperUnipotent3 x y z * dflip⁻¹ = upperUnipotent3 (-x) (-y) z := by
  rw [dflip_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dflip_val, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem dflip_mul_scalar (t : Aˣ) :
    (dflip : GL (Fin 3) A) * Matrix.GeneralLinearGroup.scalar (Fin 3) t =
      Matrix.GeneralLinearGroup.scalar (Fin 3) t * dflip := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dflip_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_three]

end SignFlipTransport

noncomputable def conjL (v : HeightOneSpectrum (𝓞 ℚ)) (d : LocalGL3 v) : (LocalGL3 v → ℂ) →ₗ[ℂ] (LocalGL3 v → ℂ) where
  toFun F := fun g => F (d * g * d⁻¹)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem conjL_apply (v : HeightOneSpectrum (𝓞 ℚ)) (d : LocalGL3 v) (F : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    conjL v d F g = F (d * g * d⁻¹) := rfl

theorem conjL_mem_gl3CyclicSubspace (v : HeightOneSpectrum (𝓞 ℚ)) (d : LocalGL3 v) (F₂ : LocalGL3 v → ℂ)
    {F₁ : LocalGL3 v → ℂ} (hF₁ : F₁ ∈ gl3CyclicSubspace F₂) :
    conjL v d F₁ ∈ gl3CyclicSubspace (conjL v d F₂) := by
  refine Submodule.span_induction (p := fun f _ => conjL v d f ∈ gl3CyclicSubspace (conjL v d F₂)) ?_ ?_ ?_ ?_ hF₁
  · rintro _ ⟨h, rfl⟩
    refine Submodule.subset_span ⟨d⁻¹ * h * d, ?_⟩
    funext g
    simp only [gl3AmbientRightTranslate_apply, conjL_apply]
    congr 1
    group
  · simp only [map_zero, Submodule.zero_mem]
  · intro f₁ f₂ _ _ h₁ h₂
    simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  · intro c f _ h
    simpa only [map_smul] using Submodule.smul_mem _ c h

theorem conjL_conjL_inv (v : HeightOneSpectrum (𝓞 ℚ)) (d : LocalGL3 v) (F : LocalGL3 v → ℂ) :
    conjL v d (conjL v d⁻¹ F) = F := by
  funext g; simp only [conjL_apply, inv_inv]; congr 1; group

theorem conjL_inv_conjL (v : HeightOneSpectrum (𝓞 ℚ)) (d : LocalGL3 v) (F : LocalGL3 v → ℂ) :
    conjL v d⁻¹ (conjL v d F) = F := by
  funext g; simp only [conjL_apply, inv_inv]; congr 1; group

theorem deepTwist_localFE_of_psiLocal
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψpos : ψv = NumberField.StandardAddChar.psiLocal ℚ v)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW0 : W ≠ 0)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h) :
    ∃ c₀ : ℕ, 1 ≤ c₀ ∧
      ∀ (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v τ c →
        ‖(τ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1 →
        c₀ ≤ c →
        (letI := localBorel ℚ v
        ∃ σ₀ σ₁ : ℝ,
          (∀ g : LocalGL3 v,
            ∃ P : ℂ → ℂ,
              (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
                P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
              IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g = P s) ∧
              IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                    W τ (1 - s) g =
                  ((ωv 1 : ℂˣ) : ℂ) * ((τ 1 : ℂˣ) : ℂ) *
                    (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ωv * τ) *
                      LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v τ ^ 2 *
                        (Ideal.absNorm v.asIdeal : ℂ) ^ ((3 * (c : ℂ)) * (1 / 2 - s))) * P s)) ∧
        (∃ (g : LocalGL3 v) (s : ℂ), σ₀ < s.re ∧
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g ≠ 0)) := by
  classical
  set d : LocalGL3 v := dflip with hd
  set W₀ : LocalGL3 v → ℂ := fun g => W (d * g * d⁻¹) with hW₀
  have hW₀def : ∀ g, W₀ g = W (d * g * d⁻¹) := fun g => rfl
  have hcW : conjL v d W = W₀ := rfl

  have hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W₀ := by
    intro x y z g
    rw [hW₀def, hW₀def, show d * (upperUnipotent3 x y z * g) * d⁻¹ =
      (d * upperUnipotent3 x y z * d⁻¹) * (d * g * d⁻¹) by group, hd, dflip_conj_upperUnipotent3, ← hd,
      hW (-x) (-y) z, hψpos, ← neg_add, AddChar.map_neg_eq_inv, AddChar.inv_apply']
  have hW₀0 : W₀ ≠ 0 := fun h0 => hW0 (by
    have : conjL v d⁻¹ W₀ = W := hcW ▸ conjL_inv_conjL v d W
    rw [← this, h0]; exact map_zero _)
  have hirr₀ : ∀ F ∈ gl3CyclicSubspace W₀, F ≠ 0 → W₀ ∈ gl3CyclicSubspace F := by
    intro F hF hF0
    have hF' : conjL v d⁻¹ F ∈ gl3CyclicSubspace W := by
      have := conjL_mem_gl3CyclicSubspace v d⁻¹ W₀ hF
      rwa [show conjL v d⁻¹ W₀ = W from hcW ▸ conjL_inv_conjL v d W] at this
    have hF'0 : conjL v d⁻¹ F ≠ 0 := fun h0 => hF0 (by rw [← conjL_conjL_inv v d F, h0]; exact map_zero _)
    have hWF := hirr _ hF' hF'0
    have := conjL_mem_gl3CyclicSubspace v d _ hWF
    rw [conjL_conjL_inv, hcW] at this
    exact this
  have hsm₀ : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g := by
    obtain ⟨Uv, hUo, hUv⟩ := hsm
    refine ⟨Uv.map (MulAut.conj d⁻¹).toMonoidHom, isOpen_map_conj' v Uv hUo d⁻¹, ?_⟩
    rintro k ⟨k', hk', rfl⟩ g
    rw [hW₀def, hW₀def]
    have : d * (g * (MulAut.conj d⁻¹).toMonoidHom k') * d⁻¹ = d * g * d⁻¹ * k' := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group
    rw [this]
    exact hUv k' hk' _
  have hadm₀ : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W₀,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
    intro Uv hUo
    obtain ⟨B, hB⟩ := hadm (Uv.map (MulAut.conj d).toMonoidHom) (isOpen_map_conj' v Uv hUo d)
    refine ⟨B.image (conjL v d), fun F hF hFk => ?_⟩
    have hF' : conjL v d⁻¹ F ∈ gl3CyclicSubspace W := by
      have := conjL_mem_gl3CyclicSubspace v d⁻¹ W₀ hF
      rwa [show conjL v d⁻¹ W₀ = W from hcW ▸ conjL_inv_conjL v d W] at this
    have hF'k : ∀ k ∈ Uv.map (MulAut.conj d).toMonoidHom, ∀ g : LocalGL3 v,
        conjL v d⁻¹ F (g * k) = conjL v d⁻¹ F g := by
      rintro k ⟨k', hk', rfl⟩ g
      simp only [conjL_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [show d⁻¹ * (g * (d * k' * d⁻¹)) * d = d⁻¹ * g * d * k' by group]
      exact hFk k' hk' _
    have hmem := hB _ hF' hF'k
    have : F = conjL v d (conjL v d⁻¹ F) := (conjL_conjL_inv v d F).symm
    rw [this, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hmem
  have hω₀ : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W₀ h := by
    intro t h
    rw [hW₀def, hW₀def, show d * (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) * d⁻¹ =
      (d * Matrix.GeneralLinearGroup.scalar (Fin 3) t) * h * d⁻¹ by group, hd, dflip_mul_scalar, ← hd,
      mul_assoc, mul_assoc, hω, ← mul_assoc]

  obtain ⟨c₀, hc₀, hmain⟩ := deepTwist_localFE_of_ne_zero v (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ rfl W₀ hW₀law
    hW₀0 hirr₀ hsm₀ hadm₀ ωv hωu hω₀

  have hZ := LanglandsTunnell.CubicInduction.localZeta_conj_diagonal_signFlip v W ωv hω
  simp only at hZ
  obtain ⟨-, hZ30, hconv30, hZd, hconv31⟩ := hZ
  have hδ : (iotaGL (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : (v.adicCompletion ℚ)ˣ) *
      NumberField.AdelicLevel.diagOne (-1 : (v.adicCompletion ℚ)ˣ)) : LocalGL3 v) = d := by rw [hd]; rfl
  simp only [hδ] at hZ30 hconv30 hZd hconv31
  simp only [← hW₀] at hZ30 hconv30 hZd hconv31
  letI := localBorel ℚ v
  refine ⟨c₀, hc₀, fun τ cc hτ hτu hcle => ?_⟩
  obtain ⟨σ₀, σ₁, hall, ⟨g₁, s₁, hs₁, hne₁⟩⟩ := hmain τ cc hτ hτu hcle
  have hdg : ∀ g : LocalGL3 v, d * (d⁻¹ * g * d) * d⁻¹ = g := fun g => by group
  refine ⟨σ₀, σ₁, fun g => ?_, ⟨d * g₁ * d⁻¹, s₁, hs₁, ?_⟩⟩
  · obtain ⟨P, hP, hconv, hZP, hconvd, hZdual⟩ := hall (d⁻¹ * g * d)
    refine ⟨P, hP, ?_, ?_, ?_, ?_⟩
    · have := (hconv30 τ (d⁻¹ * g * d) σ₀).mp hconv
      rwa [hdg] at this
    · intro s hs
      rw [← hZP s hs, hZ30 τ s (d⁻¹ * g * d), hdg]
    · have := (hconv31 τ⁻¹ (d⁻¹ * g * d) σ₁).mp hconvd
      rwa [hdg] at this
    · intro s hs
      have h := hZdual s hs
      rw [hZd τ (1 - s) (d⁻¹ * g * d), hdg] at h
      have hu : ((ωv (-1) : ℂˣ) : ℂ) * ((τ (-1) : ℂˣ) : ℂ) ≠ 0 := mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
      have h2 := mul_left_cancel₀ hu (h.trans (mul_assoc _ _ _))
      rw [h2]
      simp only [map_one, Units.val_one, one_mul]
  · rw [hZ30 τ s₁ g₁] at hne₁
    exact hne₁

theorem deepTwist_localFE_unit
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψalt : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ ∨ ψv = NumberField.StandardAddChar.psiLocal ℚ v)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW0 : W ≠ 0)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h) :
    ∃ u : (v.adicCompletion ℚ)ˣ, (u = -1 ∨ u = 1) ∧
    ∃ c₀ : ℕ, 1 ≤ c₀ ∧
      ∀ (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v τ c →
        ‖(τ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1 →
        c₀ ≤ c →
        (letI := localBorel ℚ v
        ∃ σ₀ σ₁ : ℝ,
          (∀ g : LocalGL3 v,
            ∃ P : ℂ → ℂ,
              (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
                P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
              IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g = P s) ∧
              IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                    W τ (1 - s) g =
                  ((ωv u : ℂˣ) : ℂ) * ((τ u : ℂˣ) : ℂ) *
                    (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ωv * τ) *
                      LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v τ ^ 2 *
                        (Ideal.absNorm v.asIdeal : ℂ) ^ ((3 * (c : ℂ)) * (1 / 2 - s))) * P s)) ∧
        (∃ (g : LocalGL3 v) (s : ℂ), σ₀ < s.re ∧
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g ≠ 0)) := by
  rcases hψalt with hneg | hpos
  · exact ⟨-1, Or.inl rfl, deepTwist_localFE_of_ne_zero v ψv hneg W hW hW0 hirr hsm hadm ωv hωu hω⟩
  · exact ⟨1, Or.inr rfl, deepTwist_localFE_of_psiLocal v ψv hpos W hW hW0 hirr hsm hadm ωv hωu hω⟩

theorem localFE_at_badPlace_of_deep_twist
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (hbad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
        X.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (h1 : ∀ w ∈ S, w ≠ v → X.whittakerLoc w 1 = 1)
    (hadm : ∀ w ∈ S, ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
      ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
        (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψw : ∀ w ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ∈ S) :
    ∃ (u : (w.adicCompletion ℚ)ˣ) (c₀ : ℕ), (u = -1 ∨ u = 1) ∧ 1 ≤ c₀ ∧
      ∀ (τ : (w.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ w τ c →
        ‖(τ (NumberField.AdelicLevel.uniformizerUnit ℚ w) : ℂ)‖ = 1 →
        c₀ ≤ c →
        (letI := localBorel ℚ w
        ∃ σ₀ σ₁ : ℝ,
        (∀ g : LocalGL3 w,
          ∃ P : ℂ → ℂ,
            (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
              P s = Q.eval ((Ideal.absNorm w.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm w.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
            IsLocalZeta30ConvergentAbove w (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w)))
              (X.whittakerLoc w) τ g σ₀ ∧
            (∀ s : ℂ, σ₀ < s.re →
              localZeta30 w (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w)))
                (X.whittakerLoc w) τ s g = P s) ∧
            IsLocalZeta31ConvergentAbove w (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w)))
              (selfDualHaarAt ℚ w) (dualWhittakerFn3 (X.whittakerLoc w)) τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
            (∀ s : ℂ, σ₁ < (1 - s).re →
              localZetaDual31 w (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w))) (selfDualHaarAt ℚ w)
                  (X.whittakerLoc w) τ (1 - s) g =
                ((TateGlobal.localChar X.centralChar w u : ℂˣ) : ℂ) * ((τ u : ℂˣ) : ℂ) *
                  (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w (TateGlobal.localChar X.centralChar w * τ) *
                    LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w τ ^ 2 *
                      (Ideal.absNorm w.asIdeal : ℂ) ^ ((3 * (c : ℂ)) * (1 / 2 - s))) * P s)) ∧
        (∃ (g : LocalGL3 w) (s : ℂ), σ₀ < s.re ∧
          localZeta30 w (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w)))
              (X.whittakerLoc w) τ s g ≠ 0)) := by
  have hbadw : IsBadPlace K μ w := (hSbad w).2 hw
  have _ := h1
  have _ := hv
  have hlevAll : ∀ p : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ p) = 0 := fun p => by
    by_cases hp : p ∈ S
    · exact hψw p hp
    · exact _hlev p (fun hb => hp ((hSbad p).1 hb))
  have hψalt := AutomorphicForm.psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero ψ _hψ hlevAll w
  have hW0 : X.whittakerLoc w ≠ 0 :=
    whittakerLoc_ne_zero_of_isCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ X hX S
      (fun u hu => (hSbad u).1 hu) hexp.1 w
  obtain ⟨u, hu, c₀, hc₀, h⟩ :=
    deepTwist_localFE_unit
      w (psiLoc ψ w) hψalt (X.whittakerLoc w) (hX.whittakerLoc_law w) hW0 ((hbad S).2 w hw hbadw)
      ((hbad S).1 w hw hbadw) (hadm w hw) (TateGlobal.localChar X.centralChar w) (hcent w hw).1 (hcent w hw).2
  exact ⟨u, c₀, hu, hc₀, h⟩

theorem dual_eulerProduct_at_twist
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hχU : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → TateGlobal.IsUnramifiedCharAt χ w)
    (σ₀ : ℝ) (hσ₀ : 3 ≤ σ₀) :
    (∀ v, v ∉ S →
      letI := localBorel ℚ v
      Integrable (fun y => dualWhittakerFn3 (X.whittakerLoc v) (lowerUnipotent21 y)) (selfDualHaarAt ℚ v)) ∧
    (∀ v, v ∉ S → ∀ s : ℂ, σ₀ < s.re →
      letI := localBorel ℚ v
      ((selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
        ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
          localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (selfDualHaarAt ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) (TateGlobal.localChar χ v) s 1 =
        ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval
            (((TateGlobal.localChar χ v (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
    (Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖dualWhittakerFn3 (X.whittakerLoc v.1) (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1) ∧
    (∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          letI := localBorel ℚ v.1
          ((selfDualHaarAt ℚ v.1).real {u : v.1.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
          ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZeta31 v.1 (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v.1)))
              (selfDualHaarAt ℚ v.1) (dualWhittakerFn3 (X.whittakerLoc v.1)) (TateGlobal.localChar χ v.1) s 1)
        (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
          ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v.1).eval
              (((TateGlobal.localChar χ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) *
                (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)))⁻¹)) := by
  have hnb : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → ¬ IsBadPlace K μ w := fun w hw hb => hw ((hSbad w).1 hb)
  have hgood : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
      X.whittakerLoc w 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) w (X.whittakerLoc w) :=
    fun w hw => hexp.2 w (hnb w hw) (_hlev w (hnb w hw))
  have hψp := psiLoc_eq_one_of_valued_le_one_and_exists_ne_one K ψ _hψ μ _hlev S hSbad
  exact LanglandsTunnell.CubicInduction.hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le
    K _hdeg μ _hμ S (fun w hb => (hSbad w).1 hb) ψ
    X.whittakerLoc (fun w hw => hX.spherical w (hnb w hw)) (fun w hw => (hgood w hw).1) (fun w hw => (hgood w hw).2)
    (fun w _ => hX.whittakerLoc_law w) hψp.1 hψp.2 χ hχ hχU σ₀ hσ₀

theorem continuous_embedMat2 {A : Type*} [CommRing A] [TopologicalSpace A] :
    Continuous (LanglandsTunnell.CubicInduction.embedMat2 (A := A)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [LanglandsTunnell.CubicInduction.embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons] <;>
    first
      | exact continuous_const
      | exact continuous_apply_apply _ _

theorem continuous_iotaGL {A : Type*} [CommRing A] [TopologicalSpace A] :
    Continuous (LanglandsTunnell.CubicInduction.iotaGL (A := A)) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_embedMat2.comp Units.continuous_val, continuous_embedMat2.comp Units.continuous_coe_inv⟩

theorem continuous_diagUnitGL2 {A : Type*} [CommRing A] [TopologicalSpace A] :
    Continuous (LanglandsTunnell.CubicInduction.diagUnitGL2 (A := A)) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : Aˣ => (!![(x : A), 0; 0, 1] : Matrix (Fin 2) (Fin 2) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_val
  · change Continuous fun x : Aˣ => (!![((x⁻¹ : Aˣ) : A), 0; 0, 1] : Matrix (Fin 2) (Fin 2) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_coe_inv

theorem continuous_lowerUnipotent21 {A : Type*} [CommRing A] [TopologicalSpace A] [ContinuousNeg A] :
    Continuous (LanglandsTunnell.CubicInduction.lowerUnipotent21 (A := A)) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : A => (!![1, 0, 0; x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · change Continuous fun x : A => (!![1, 0, 0; -x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact continuous_const | exact continuous_id | exact continuous_neg

theorem continuous_unfoldPoint {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (g : GL (Fin 3) A) :
    Continuous fun p : Aˣ × A =>
      LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 p.1) *
        LanglandsTunnell.CubicInduction.lowerUnipotent21 p.2 * g :=
  (((continuous_iotaGL.comp continuous_diagUnitGL2).comp continuous_fst).mul
    (continuous_lowerUnipotent21.comp continuous_snd)).mul continuous_const

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem aestronglyMeasurable_unfolded_integrand
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hW : Continuous W) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : Continuous χ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ) :
    AEStronglyMeasurable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
        W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ p.1 : ℂˣ) : ℂ) *
          ((TateGlobal.ideleNorm ℚ p.1 : ℝ) : ℂ) ^ (s - 1))
      ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) := by
  haveI := NumberField.Idele.borelSpace_ideleBorel ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdeleRing.secondCountableTopology ℚ
  refine Continuous.aestronglyMeasurable ?_
  refine ((hW.comp (continuous_unfoldPoint g)).mul (Units.continuous_val.comp (hχ.comp continuous_fst))).mul ?_
  refine Continuous.cpow
    (Complex.continuous_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp continuous_fst))
    continuous_const fun p => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (NumberField.TateGlobal.ideleNorm_pos p.1)

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem dual_twoVariable_integrable
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker) (hcontW' : Continuous X.dualWhittaker)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
      Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
        X.dualWhittaker (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ p.1 : ℂˣ) : ℂ) *
          ((TateGlobal.ideleNorm ℚ p.1 : ℝ) : ℂ) ^ (s - 1))
        ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) := by
  obtain ⟨-, -, -, -, -, hint⟩ :=
    summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 X.dualWhittaker hcontW' hW'
  obtain ⟨σ₀, hσ₀⟩ := hint g
  refine ⟨σ₀, fun s hs => ?_⟩
  exact (hσ₀ s.re hs.le).mono' (aestronglyMeasurable_unfolded_integrand X.dualWhittaker hcontW' χ hχ.2.1 g s)
    (Filter.Eventually.of_forall fun p => by
      rw [norm_mul, norm_mul, hχ.2.2 p.1, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos (TateGlobal.ideleNorm_pos p.1), Complex.sub_re, Complex.one_re])

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem dual_unfolding_at_twist
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (hS' : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hχU : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → TateGlobal.IsUnramifiedCharAt χ w)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
      globalZeta31 X.dualWhittaker χ s g =
        ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
          ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
          (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces ℚ / Real.sqrt |(NumberField.discr ℚ : ℝ)| : ℝ) : ℂ) *
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
              (∫ y : mixedEmbedding.mixedSpace ℚ,
                  dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                    lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
                (∏ v ∈ S,
                  (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
                   ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                     (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                     ∫ x : v.adicCompletion ℚ,
                       dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                         lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                         ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
                ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
            ∂(NumberField.Idele.productMeasureData ℚ S).νS) *
          (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
            ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v.1).eval
                (((TateGlobal.localChar χ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) *
                  (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)))⁻¹) := by
  have _ := hW
  have _ := hcontW
  obtain ⟨σa, hσa⟩ := hS' χ hχ g
  obtain ⟨σb, hσb⟩ := dual_twoVariable_integrable K ψ _hψ μ _hμ D U gen X hX hW' hcontW' χ hχ g
  have hD := dual_eulerProduct_at_twist K _hdeg ψ _hψ μ _hμ _hlev D U gen X hX hexp S hSbad χ hχ hχU (max 3 (max σa σb))
    (le_max_left 3 (max σa σb))
  refine ⟨(max 3 (max σa σb)), ?_⟩
  exact globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable S X.dualWhittaker
    (dualWhittakerFn3 X.whittakerArch)
    (fun v => dualWhittakerFn3 (X.whittakerLoc v)) (dualWhittaker_factorises_off K ψ _hψ μ _hμ D U gen X hX hcont S hSbad)
    (dualWhittakerFn3_rightInvariant_off K ψ _hψ μ _hμ D U gen X hX S hSbad)
    (dualWhittakerFn3_one_off K ψ _hψ μ _hμ D U gen X hX _hlev hexp S hSbad) hD.1 hD.2.2.1 χ
    (apply_eq_one_of_isAdmissibleTwist_of_isUnramifiedCharAt_off S χ hχ hχU) g hg (max 3 (max σa σb)) _ hD.2.2.2
    (NumberField.Idele.productMeasureData ℚ S)
    (fun s hs => hσa s (lt_of_le_of_lt ((le_max_left σa σb).trans (le_max_right 3 _)) hs))
    (fun s hs => hσb s (lt_of_le_of_lt ((le_max_right σa σb).trans (le_max_right 3 _)) hs))

theorem exists_forall_componentAt3_eq_and_eq_one (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), LocalGL3 w) :
    ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ w ∈ T, componentAt3 (𝓞 ℚ) ℚ w g = h w) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ T → componentAt3 (𝓞 ℚ) ℚ w g = 1) ∧
      archComponent3 (𝓞 ℚ) ℚ g = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, fun w hw => absurd hw (Finset.notMem_empty w), fun w _ => map_one _, map_one _⟩
  | insert a T haT ih =>
    obtain ⟨g, hg, hg', hga⟩ := ih
    refine ⟨localToAdelic3 a (h a) * g, fun w hw => ?_, fun w hw => ?_, ?_⟩
    · rw [(componentAt3 (𝓞 ℚ) ℚ w).map_mul]
      rcases Finset.mem_insert.mp hw with hwa | hwT
      · rw [hwa, componentAt3_localToAdelic3_self, hg' a haT, mul_one]
      · have hwa : w ≠ a := fun e => haT (e ▸ hwT)
        rw [componentAt3_localToAdelic3_of_ne a w hwa, one_mul, hg w hwT]
    · rw [(componentAt3 (𝓞 ℚ) ℚ w).map_mul]
      have hwa : w ≠ a := fun e => hw (e ▸ Finset.mem_insert_self a T)
      have hwT : w ∉ T := fun m => hw (Finset.mem_insert_of_mem m)
      rw [componentAt3_localToAdelic3_of_ne a w hwa, one_mul, hg' w hwT]
    · rw [(archComponent3 (𝓞 ℚ) ℚ).map_mul, hga, mul_one]
      exact Units.ext (LanglandsTunnell.CubicInduction.mapMatrix_arch_finMatN (Fin 3) (𝓞 ℚ) ℚ _)

theorem exists_forall_componentAt3_eq_and_archComponent3_eq (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), LocalGL3 w) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ w ∈ T, componentAt3 (𝓞 ℚ) ℚ w g = h w) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ T → componentAt3 (𝓞 ℚ) ℚ w g = 1) ∧
      archComponent3 (𝓞 ℚ) ℚ g = gInf := by
  obtain ⟨g, hg, hg', hga⟩ := exists_forall_componentAt3_eq_and_eq_one T h
  refine ⟨g * archEmbed3 gInf, fun w hw => ?_, fun w hw => ?_, ?_⟩
  · rw [map_mul, componentAt3_archEmbed3, mul_one, hg w hw]
  · rw [map_mul, componentAt3_archEmbed3, mul_one, hg' w hw]
  · rw [map_mul, archComponent3_archEmbed3, hga, one_mul]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem lfun_relations_at_twist
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hτ : IsAdmissibleTwist ℚ τ)
    (hτinf : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 0) :
    ∃ (Λ Λd : ℂ → ℂ) (σ : ℝ), Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
      (∀ s : ℂ, σ < s.re → Λ s ≠ 0 ∧
        Λ s = (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactor s *
          (LanglandsTunnell.HeckeTate.heckeDatum K
            (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).LFun s) ∧
      (∀ u : ℂ, σ < u.re →
        Λd u = (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactorDual u *
          (LanglandsTunnell.HeckeTate.heckeDatum K
            (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).LFunDual u) ∧
      (LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).Converges ∧
      (0 : ℝ) <
        LanglandsTunnell.HeckeTate.heckeConductor K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) ∧
      ∀ s : ℂ,
        Λ s =
          LanglandsTunnell.HeckeTate.heckeRootNumber K
            (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR kC *
            ((LanglandsTunnell.HeckeTate.heckeConductor K
                (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - s) *
            Λd (1 - s) := by
  have h0 := inducedL_fe K μ _hμ _hns uR aR uC kC huR huC τ hτ 0 0 hτinf
  obtain ⟨hnice, -⟩ := h0
  simp only [add_zero, Int.cast_zero] at hnice
  obtain ⟨-, hconv, hN, Λ, Λd, hΛ, hΛd, -, -, hL, hLd, hfe⟩ := hnice
  have hgR :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).gammaR =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).gammaR := rfl
  have hgC :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).gammaC =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).gammaC := rfl
  have hgRd :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).gammaRDual =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).gammaRDual := rfl
  have hgCd :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).gammaCDual =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).gammaCDual := rfl
  have habs :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).abscissa = 1 := rfl
  have hcen :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).center = 1 / 2 := rfl
  have harch : ∀ s : ℂ,
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).archFactor s =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactor s := by
    intro s
    unfold LanglandsTunnell.LDatum.archFactor
    rw [hgR, hgC]
  have harchd : ∀ s : ℂ,
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).archFactorDual s =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactorDual s := by
    intro s
    unfold LanglandsTunnell.LDatum.archFactorDual
    rw [hgRd, hgCd]
  have hσ0 := archFactor_ne_zero_and_archFactorDual_ne_zero (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC)
  obtain ⟨σ₃, hσ₃⟩ := hσ0
  refine ⟨Λ, Λd, max 1 σ₃, hΛ, hΛd, fun s hs => ?_, fun u hu => ?_, hconv, hN, fun s => ?_⟩
  · have hs1 :
        (LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).abscissa < s.re := by
      rw [habs]
      exact lt_of_le_of_lt (le_max_left _ _) hs
    have hs3 : σ₃ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have h := hL s hs1
    simp only [one_mul, harch] at h
    refine ⟨?_, h⟩
    rw [h]
    exact mul_ne_zero (hσ₃ s hs3).1 (hconv s hs1).2.2.1
  · have hu1 :
        (LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).abscissa < u.re := by
      rw [habs]
      exact lt_of_le_of_lt (le_max_left _ _) hu
    have h := hLd u hu1
    simp only [one_mul, harchd] at h
    exact h
  · have h := hfe s
    rw [hcen] at h
    rw [h]
    congr 1
    · congr 2
      norm_num
    · congr 1
      norm_num

theorem multipliable_inv_of_summable_norm_sub_one {ι : Type} (f : ι → ℂ)
    (hf : Summable fun i => ‖f i - 1‖) : Multipliable fun i => (f i)⁻¹ := by
  by_cases! h0 : ∃ i, f i = 0
  · obtain ⟨i, hi⟩ := h0
    exact multipliable_of_exists_eq_zero ⟨i, by simp [hi]⟩
  · have hg : Summable fun i => (f i)⁻¹ - 1 := by
      refine (hf.mul_left 2).of_norm_bounded_eventually ?_
      filter_upwards [hf.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi
      have hfi : (1 / 2 : ℝ) ≤ ‖f i‖ := by
        have h := norm_sub_norm_le (1 : ℂ) (f i)
        rw [norm_one, norm_sub_rev] at h
        linarith
      rw [show (f i)⁻¹ - 1 = (1 - f i) / f i by field_simp [h0 i], norm_div, norm_sub_rev,
        div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (f i - 1)]
    simpa using Complex.multipliable_one_add_of_summable hg

theorem unwind_of_bracket_identity
    (γv γw₁ γw₂ C₁ C₂ e₁ e₂ ed₁ ed₂ r₁' r₂ ρ₁ ρ₂ π πd Qt QT : ℂ → ℂ) (S E s₀ : ℂ)
    (hbr : ∀ s : ℂ,
      γv s * γw₂ s * ed₂ s * r₂ s * C₁ s * e₁ s = r₁' s * γw₁ s * ed₁ s * C₂ s * e₂ s)
    (he₂ : ∀ s : ℂ, e₂ s = 1) (hed₂ : ∀ s : ℂ, ed₂ s = 1)
    (hstar : ∀ s : ℂ, γv s * γw₂ s * C₁ s = S * E * Qt s * (γw₁ s * C₂ s))
    (hX : ∀ s : ℂ, γw₁ s * C₂ s ≠ 0)
    (hr₁ : ∀ s : ℂ, r₁' s = ρ₁ (s + s₀)) (hr₂ : ∀ s : ℂ, r₂ s = ρ₂ (s + s₀))
    (he₁ : ∀ s : ℂ, e₁ s = π (s + s₀)) (hed₁ : ∀ s : ℂ, ed₁ s = πd (s + s₀))
    (hQt : ∀ s : ℂ, Qt s = QT (s + s₀)) :
    ∀ s : ℂ, ρ₁ s * πd s = S * E * QT s * π s * ρ₂ s := by
  intro s
  have hs : s - s₀ + s₀ = s := sub_add_cancel s s₀
  have h1 := hbr (s - s₀)
  have h2 := hstar (s - s₀)
  rw [he₂, hed₂, hr₁, hr₂, he₁, hed₁, hs] at h1
  rw [hQt, hs] at h2
  refine mul_left_cancel₀ (hX (s - s₀)) ?_
  linear_combination -h1 + ρ₂ s * π s * h2

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem instance_left_line
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
      componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hτS : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt τ p)
    (hfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), (primeFibre ℚ K p).Finite)
    (hram : ∀ w ∈ S, w ≠ v → ∀ 𝔓 ∈ primeFibre ℚ K w,
      ¬ IsUnramifiedCharAt (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
    (hconv :
      (LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).Converges)
    (c cL : ℂ) (Ad : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ → ℂ) (σ₁ : ℝ)
    (hLτ : ∀ u : ℂ, σ₁ < u.re →
        globalZetaDual31 X.whittaker τ u g =
          ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
            ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
            (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces ℚ / Real.sqrt |(NumberField.discr ℚ : ℝ)| : ℝ) : ℂ) *
            (cL * Ad (weylPrime3 * transposeInv3 g) u *
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 localZetaDual31 v (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
                  (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) (X.whittakerLoc v) (localChar τ v) u
                  (componentAt3 (𝓞 ℚ) ℚ v g)) *
              ∏ w ∈ S.erase v,
                (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
                 ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set
                   (w.adicCompletion ℚ)) : ℂ)⁻¹ *
                   localZetaDual31 w (Measure.comap Units.val
                    (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
                    (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w) (X.whittakerLoc w) (localChar τ w) u
                    (componentAt3 (𝓞 ℚ) ℚ w g))) *
          (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
              ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v.1).eval
                  (((TateGlobal.localChar τ⁻¹ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) *
                    (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-u)))⁻¹))
    (Z : ℂ → ℂ) (σZ : ℝ) (hZ : ∀ s : ℂ, s.re < σZ → Z s = c * globalZetaDual31 X.whittaker τ (1 - s) g)
    (Λd : ℂ → ℂ) (σΛ : ℝ)
    (hΛd :
      (∀ u : ℂ, σΛ < u.re →
        Λd u = (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactorDual u *
          (LanglandsTunnell.HeckeTate.heckeDatum K
            (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).LFunDual u))
    (Zvd : ℂ → ℂ) (σv : ℝ)
    (hZvd : ∀ s : ℂ, s.re < σv →
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
       ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
         (v.adicCompletion ℚ)) : ℂ)⁻¹ *
         localZetaDual31 v (Measure.comap Units.val
          (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
          (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) (X.whittakerLoc v) (localChar τ v) (1 - s)
          (componentAt3 (𝓞 ℚ) ℚ v g)) =
        Zvd s)
    (P γ : HeightOneSpectrum (𝓞 ℚ) → ℂ → ℂ) (σw : HeightOneSpectrum (𝓞 ℚ) → ℝ)
    (hheld : ∀ w ∈ S.erase v, ∀ s : ℂ, s.re < σw w →
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
       ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set
         (w.adicCompletion ℚ)) : ℂ)⁻¹ *
         localZetaDual31 w (Measure.comap Units.val
          (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
          (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w) (X.whittakerLoc w) (localChar τ w) (1 - s)
          (componentAt3 (𝓞 ℚ) ℚ w g)) =
        γ w s * P w s)
    (ed : ℂ → ℂ) (σe : ℝ)
    (hfibd : ∀ s : ℂ, s.re < σe →
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
              uR aR uC kC).dual 𝔓).eval (((LanglandsTunnell.HeckeTate.heckeDatum K
                  (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                      uR aR uC kC).norm 𝔓 : ℂ) ^ (-(1 - s))))⁻¹) * ed s =
        1) :
    ∃ σ : ℝ, ∀ s : ℂ, s.re < σ →
      (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactorDual (1 - s) * Z s =
        c * ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
          ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
          (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces ℚ / Real.sqrt |(NumberField.discr ℚ : ℝ)| : ℝ) : ℂ) *
          cL * Ad (weylPrime3 * transposeInv3 g) (1 - s) * Zvd s *
          ((∏ w ∈ S.erase v, γ w s) * (∏ w ∈ S.erase v, P w s)) * Λd (1 - s) * ed s := by
  have _ := hcont
  have _ := hW
  have _ := hW'
  have _ := hcontW
  have _ := hcontW'
  have _ := hexp
  have _ := hSbad
  have _ := hS
  have _ := mT
  have _ := hg
  obtain ⟨M, hM⟩ := ((S.erase v).image fun w => -σw w).exists_le
  refine ⟨min (min (min 0 (1 - σ₁)) (min σZ (1 - σΛ))) (min (min σv σe) (-M)), fun s hs => ?_⟩
  simp only [lt_min_iff] at hs
  obtain ⟨⟨⟨h0, hs₁⟩, hsZ, hsΛ⟩, ⟨hsv, hse⟩, hsM⟩ := hs
  have hre : (1 - s).re = 1 - s.re := by rw [Complex.sub_re, Complex.one_re]
  have hmult := multipliable_inv_of_summable_norm_sub_one _
    (hconv (1 - s) (by change (1 : ℝ) < (1 - s).re; rw [hre]; linarith)).2.1
  have key := congrArg (· * ed s)
    (LFunDual_heckeDatum_eq_finprod_fibre_mul_tprod_inducedLDual K μ τ uR aR uC kC S v hv (1 - s) hfin hτS hram
      hmult)
  beta_reduce at key
  rw [mul_right_comm, hfibd s hse, one_mul] at key
  rw [hZ s hsZ, hLτ (1 - s) (by rw [hre]; linarith), hZvd s hsv, hΛd (1 - s) (by rw [hre]; linarith),
    Finset.prod_congr rfl fun w hw =>
      hheld w hw s (lt_of_lt_of_le hsM (neg_le.1 (hM _ (Finset.mem_image_of_mem (fun w => -σw w) hw)))),
    Finset.prod_mul_distrib, ← key]
  ring

theorem differentiable_eval_cpow_neg_mul_cpow_mul (Q : Polynomial ℂ) (N : ℂ) (hN : N ≠ 0) (e : ℂ) :
    Differentiable ℂ (fun s : ℂ => Q.eval (N ^ (-s)) * N ^ (e * s)) := by
  have h1 : Differentiable ℂ (fun s : ℂ => N ^ (-s)) := differentiable_neg.const_cpow (Or.inl hN)
  have h2 : Differentiable ℂ (fun s : ℂ => N ^ (e * s)) := (differentiable_id.const_mul e).const_cpow (Or.inl hN)
  exact (Q.differentiable.comp h1).mul h2

theorem differentiable_cpow_mul_half_sub (N e : ℂ) (hN : N ≠ 0) :
    Differentiable ℂ (fun s : ℂ => N ^ (e * (1 / 2 - s))) := by
  exact (((differentiable_const (1 / 2 : ℂ)).sub differentiable_id).const_mul e).const_cpow (Or.inl hN)

theorem place_dual_data_of_localFE
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (w : HeightOneSpectrum (𝓞 ℚ)) (τ : (w.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ) (u : (w.adicCompletion ℚ)ˣ) (g : LocalGL3 w) (P : ℂ → ℂ) (σ₁ : ℝ)
    (hP :
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
              P s = Q.eval ((Ideal.absNorm w.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm w.asIdeal : ℂ) ^ ((m : ℂ) * s)))
    (hdual :
      letI := localBorel ℚ w
      (∀ s : ℂ, σ₁ < (1 - s).re →
              localZetaDual31 w (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w))) (selfDualHaarAt ℚ w)
                  (X.whittakerLoc w) τ (1 - s) g =
                ((TateGlobal.localChar X.centralChar w u : ℂˣ) : ℂ) * ((τ u : ℂˣ) : ℂ) *
                  (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w (TateGlobal.localChar X.centralChar w * τ) *
                    LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w τ ^ 2 *
                      (Ideal.absNorm w.asIdeal : ℂ) ^ ((3 * (c : ℂ)) * (1 / 2 - s))) * P s)) :
    letI := localBorel ℚ w
    Differentiable ℂ P ∧
      Differentiable ℂ (fun s : ℂ =>
        ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set
            (w.adicCompletion ℚ)) : ℂ)⁻¹ *
          (((TateGlobal.localChar X.centralChar w u : ℂˣ) : ℂ) * ((τ u : ℂˣ) : ℂ) *
            (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w (TateGlobal.localChar X.centralChar w * τ) *
              LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w τ ^ 2 *
                (Ideal.absNorm w.asIdeal : ℂ) ^ ((3 * (c : ℂ)) * (1 / 2 - s))))) ∧
      ∀ s : ℂ, s.re < 1 - σ₁ →
        ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set
            (w.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZetaDual31 w (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w))) (selfDualHaarAt ℚ w)
                (X.whittakerLoc w) τ (1 - s) g =
          ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set
              (w.adicCompletion ℚ)) : ℂ)⁻¹ *
              (((TateGlobal.localChar X.centralChar w u : ℂˣ) : ℂ) * ((τ u : ℂˣ) : ℂ) *
                (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w (TateGlobal.localChar X.centralChar w * τ) *
                  LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w τ ^ 2 *
                    (Ideal.absNorm w.asIdeal : ℂ) ^ ((3 * (c : ℂ)) * (1 / 2 - s)))) *
            P s := by
  obtain ⟨Q, m, hPQ⟩ := hP
  have hN0 : (Ideal.absNorm w.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot)
  refine ⟨?_, ?_, ?_⟩
  · have hPfun : P = fun s : ℂ =>
        Q.eval ((Ideal.absNorm w.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm w.asIdeal : ℂ) ^ ((m : ℂ) * s) :=
      funext hPQ
    rw [hPfun]
    exact differentiable_eval_cpow_neg_mul_cpow_mul Q _ hN0 (m : ℂ)
  · exact (((differentiable_cpow_mul_half_sub _ (3 * (c : ℂ)) hN0).const_mul _).const_mul _).const_mul _
  · intro s hs
    have hs' : σ₁ < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    rw [hdual s hs']
    ring

theorem selfDualHaarAt_real_adicCompletionIntegers_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ v
    ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
        (v.adicCompletion ℚ)) : ℂ) ≠ 0 := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  have hq : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  rw [Complex.ofReal_ne_zero, MeasureTheory.measureReal_def, ENNReal.toReal_ne_zero,
    LanglandsTunnell.TateLocal.selfDualHaarAt, MeasureTheory.Measure.coe_nnreal_smul_apply,
    ← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts, MeasureTheory.Measure.addHaarMeasure_self, mul_one]
  exact ⟨ENNReal.coe_ne_zero.mpr (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne', ENNReal.coe_ne_top⟩

theorem localZeta_relations_at_v_of_shift
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (v : HeightOneSpectrum (𝓞 ℚ)) (R₁ R₂ : Polynomial ℂ) (m : ℤ) (η χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s₀ : ℂ)
    (g : LocalGL3 v)
    (hshift :
      letI := localBorel ℚ v
      ∀ (W : LocalGL3 v → ℂ) (g : LocalGL3 v) (s : ℂ),
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W (η * χ) s g =
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W η (s + s₀) g ∧
        localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W (η * χ)
            (1 - s) g =
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W η
            (1 - (s + s₀)) g)
    (hFE :
      letI := localBorel ℚ v
      ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc
          v) η g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) η s g *
            Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt
          ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        (∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            (X.whittakerLoc v) η (1 - s) g *
            (Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
          R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s))) :
    letI := localBorel ℚ v
    ∃ (q₁' q₂ r₁' r₂ : ℂ → ℂ) (σ σ' : ℝ),
      Differentiable ℂ q₁' ∧ Differentiable ℂ q₂ ∧ Differentiable ℂ r₁' ∧ Differentiable ℂ r₂ ∧
      (∀ s : ℂ, σ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) (η * χ) s g *
          q₂ s = q₁' s) ∧
      (∀ s : ℂ, s.re < σ' →
        ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
            (v.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (X.whittakerLoc v) (η * χ) (1 - s) g *
          (q₂ s * r₂ s) =
        r₁' s * q₁' s) ∧
      (∀ s : ℂ, r₁' s =
        ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
            (v.adicCompletion ℚ)) : ℂ)⁻¹ *
          (R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + s₀))) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * (s + s₀)))) ∧
      (∀ s : ℂ, r₂ s = R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + s₀)))) ∧
      (∃ Q₂ : Polynomial ℂ, Q₂ ≠ 0 ∧
        ∀ s : ℂ, q₂ s = Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + s₀)))) ∧
      ∃ (Q₁ : Polynomial ℂ) (n : ℤ), ∀ s : ℂ,
        q₁' s = Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + s₀))) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * (s + s₀)) := by
  obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ₂, -, hnat, -, hdual⟩ := hFE
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have htr : Differentiable ℂ fun s : ℂ => s + s₀ := differentiable_id.add_const s₀
  have hcp : Differentiable ℂ fun s : ℂ => (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) :=
    differentiable_neg.const_cpow (Or.inl hN)
  refine ⟨fun s => Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + s₀))) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * (s + s₀)),
    fun s => Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + s₀))),
    fun s => ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
        (v.adicCompletion ℚ)) : ℂ)⁻¹ *
      (R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + s₀))) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * (s + s₀))),
    fun s => R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + s₀))),
    σ₀ - s₀.re, 1 - σ₁ - s₀.re,
    (differentiable_eval_cpow_neg_mul_cpow_mul Q₁ _ hN n).comp htr, (Q₂.differentiable.comp hcp).comp htr,
    ((differentiable_eval_cpow_neg_mul_cpow_mul R₁ _ hN m).comp htr).const_mul _,
    (R₂.differentiable.comp hcp).comp htr, fun s hs => ?_, fun s hs => ?_, fun s => rfl, fun s => rfl,
    ⟨Q₂, hQ₂, fun s => rfl⟩, Q₁, n, fun s => rfl⟩
  · have h1 := (hshift (X.whittakerLoc v) g s).1
    rw [h1]
    exact hnat (s + s₀) (by rw [Complex.add_re]; linarith)
  · have h2 := (hshift (X.whittakerLoc v) g s).2
    have hd := hdual (s + s₀) (by rw [Complex.sub_re, Complex.one_re, Complex.add_re]; linarith)
    dsimp only
    rw [h2, mul_assoc, hd, show ((m : ℂ) + (n : ℂ)) * (s + s₀) = (m : ℂ) * (s + s₀) + (n : ℂ) * (s + s₀) by ring,
      Complex.cpow_add _ _ hN]
    ring

theorem exists_forall_finset_prod_ne_zero {ι : Type} (T : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ T, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → f i s ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (∏ i ∈ T, f i s) ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun s _ => by simp⟩
  | @insert a T ha ih =>
    obtain ⟨σ₁, h₁⟩ := h a (Finset.mem_insert_self a T)
    obtain ⟨σ₂, h₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
    rw [Finset.prod_insert ha]
    exact mul_ne_zero (h₁ s (lt_of_le_of_lt (le_max_left _ _) hs)) (h₂ s (lt_of_le_of_lt (le_max_right _ _) hs))

theorem exists_forall_eval_cpow_neg_mul_cpow_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) (N : ℕ) (hN : 1 < N)
    (e : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Q.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ (e * s) ≠ 0 := by
  obtain ⟨σ, hσ⟩ := eval_cpow_ne_zero_of_ne_zero Q hQ (N : ℝ) (by exact_mod_cast hN)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨σ, fun s hs => ?_⟩
  have h := hσ s hs
  rw [Complex.ofReal_natCast] at h
  exact mul_ne_zero h fun h0 => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h0).1

theorem exists_forall_eval_cpow_neg_add_mul_cpow_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) (N : ℕ) (hN : 1 < N)
    (e s₀ : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Q.eval ((N : ℂ) ^ (-(s + s₀))) * (N : ℂ) ^ (e * (s + s₀)) ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_forall_eval_cpow_neg_mul_cpow_ne_zero Q hQ N hN e
  exact ⟨σ - s₀.re, fun s hs => hσ (s + s₀) (by rw [Complex.add_re]; linarith)⟩

theorem exists_forall_eval_cpow_neg_add_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) (N : ℕ) (hN : 1 < N) (s₀ : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Q.eval ((N : ℂ) ^ (-(s + s₀))) ≠ 0 := by
  obtain ⟨σ, hσ⟩ := eval_cpow_ne_zero_of_ne_zero Q hQ (N : ℝ) (by exact_mod_cast hN)
  refine ⟨σ - s₀.re, fun s hs => ?_⟩
  have h := hσ (s + s₀) (by rw [Complex.add_re]; linarith)
  rwa [Complex.ofReal_natCast] at h

theorem finprod_mem_inv_mul_finprod_mem_eq_one {ι : Type} (T : Set ι) (hT : T.Finite) (f : ι → ℂ)
    (hf : ∀ i ∈ T, f i ≠ 0) :
    (∏ᶠ i ∈ T, (f i)⁻¹) * ∏ᶠ i ∈ T, f i = 1 := by
  rw [← finprod_mem_mul_distrib hT]
  exact finprod_mem_of_eqOn_one fun i hi => inv_mul_cancel₀ (hf i hi)

theorem exists_forall_mem_ne_zero_of_finite {ι : Type} (T : Set ι) (hT : T.Finite) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ T, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → f i s ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ i ∈ T, f i s ≠ 0 := by
  classical
  choose! σf hσf using h
  obtain ⟨M, hM⟩ := Finset.exists_le (hT.toFinset.image σf)
  exact ⟨M, fun s hs i hi =>
    hσf i hi s (lt_of_le_of_lt (hM _ (Finset.mem_image_of_mem σf (hT.mem_toFinset.mpr hi))) hs)⟩

theorem exists_heightOneSpectrum_ratRingOfIntegers_notMem (T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ x : HeightOneSpectrum (𝓞 ℚ), x ∉ T := by
  haveI : Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
    Infinite.of_injective _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective
  exact Infinite.exists_notMem_finset T

theorem eq_comp_add_of_forall_eq_of_forall_eq (Z Z' P : ℂ → ℂ) (s₀ : ℂ) (σ : ℝ)
    (hsh : ∀ s : ℂ, Z' s = Z (s + s₀)) (hP : ∀ s : ℂ, σ < s.re → Z s = P s) :
    ∀ s : ℂ, σ - s₀.re < s.re → Z' s = P (s + s₀) := by
  intro s hs
  rw [hsh]
  exact hP (s + s₀) (by rw [Complex.add_re]; linarith)

theorem heckeDatum_dual_ne_zero
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (LanglandsTunnell.HeckeTate.heckeDatum K χ uR aR uC kC).dual 𝔓 ≠ 0 := by
  intro h
  have h0 := congrArg (fun q : Polynomial ℂ => q.coeff 0) h
  simp only [LanglandsTunnell.HeckeTate.heckeDatum] at h0
  split_ifs at h0 <;> simp at h0

theorem differentiable_fun_finset_prod {ι : Type} (T : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ T, Differentiable ℂ (f i)) : Differentiable ℂ (fun s : ℂ => ∏ i ∈ T, f i s) := by
  have : (fun s : ℂ => ∏ i ∈ T, f i s) = fun s => (∏ i ∈ T, f i) s := by
    funext s; simp only [Finset.prod_apply]
  rw [this]
  exact Differentiable.finsetProd hf

theorem differentiable_fun_finprod_mem {ι : Type} (T : Set ι) (hT : T.Finite) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ T, Differentiable ℂ (f i)) : Differentiable ℂ (fun s : ℂ => ∏ᶠ i ∈ T, f i s) := by
  have : (fun s : ℂ => ∏ᶠ i ∈ T, f i s) = fun s => ∏ i ∈ hT.toFinset, f i s := by
    funext s; exact finprod_mem_eq_finite_toFinset_prod (fun i => f i s) hT
  rw [this]
  exact differentiable_fun_finset_prod hT.toFinset f fun i hi => hf i (hT.mem_toFinset.mp hi)

theorem differentiable_eval_cpow_neg (Q : Polynomial ℂ) (N : ℂ) (hN : N ≠ 0) :
    Differentiable ℂ (fun s : ℂ => Q.eval (N ^ (-s))) := by
  exact Q.differentiable.comp (differentiable_neg.const_cpow (Or.inl hN))

theorem ramificationIdx_eq_one_and_inertiaDeg_le_three_and_finsum_inertiaDeg_eq_three_of_not_isRamifiedIn
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3) (v : HeightOneSpectrum (𝓞 ℚ))
    (hKv : ¬ IsRamifiedIn K v) :
    (∀ w : v.Extension (𝓞 K), v.asIdeal.ramificationIdx' w.1.asIdeal = 1) ∧
      (∀ w : v.Extension (𝓞 K), v.asIdeal.inertiaDeg' w.1.asIdeal = 1 ∨ v.asIdeal.inertiaDeg' w.1.asIdeal = 2 ∨
        v.asIdeal.inertiaDeg' w.1.asIdeal = 3) ∧
      ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, v.asIdeal.inertiaDeg' 𝔓.asIdeal = 3 := by
  have he : ∀ 𝔓 ∈ primeFibre ℚ K v, v.asIdeal.ramificationIdx' 𝔓.asIdeal = 1 := by
    intro 𝔓 h𝔓
    by_contra hne
    exact hKv ⟨𝔓, h𝔓, hne⟩
  have himage : (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) '' primeFibre ℚ K v
      = Ideal.primesOver v.asIdeal (𝓞 K) := by
    ext P
    constructor
    · rintro ⟨𝔓, h𝔓, rfl⟩
      rw [mem_primeFibre] at h𝔓
      refine ⟨𝔓.isPrime, ⟨?_⟩⟩
      rw [← h𝔓]
      rfl
    · intro hP
      refine ⟨⟨P, hP.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot hP⟩, ?_, rfl⟩
      rw [mem_primeFibre]
      exact HeightOneSpectrum.ext hP.2.over.symm
  have hbridge : ∀ f : Ideal (𝓞 K) → ℕ,
      ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, f 𝔓.asIdeal = ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K), f P := by
    intro f
    rw [← finsum_mem_image (f := f) (g := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h), himage, ← IsDedekindDomain.coe_primesOverFinset v.ne_bot (𝓞 K),
      finsum_mem_coe_finset]
  have hfund := Ideal.sum_ramification_inertia (𝓞 K) ℚ K v.ne_bot
  rw [hdeg] at hfund
  have hsum3 : ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K), v.asIdeal.inertiaDeg' P = 3 := by
    rw [← hfund]
    refine Finset.sum_congr rfl fun P hP => ?_
    obtain ⟨𝔓, h𝔓, rfl⟩ : P ∈ (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) '' primeFibre ℚ K v := by
      rw [himage, ← IsDedekindDomain.coe_primesOverFinset v.ne_bot (𝓞 K)]
      exact hP
    rw [he 𝔓 h𝔓, one_mul]
  refine ⟨fun w => he w.1 w.2, fun w => ?_, (hbridge fun P => v.asIdeal.inertiaDeg' P).trans hsum3⟩
  have hlies : w.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  have hpos : 0 < v.asIdeal.inertiaDeg' w.1.asIdeal := Ideal.inertiaDeg'_pos _ _
  have hle : v.asIdeal.inertiaDeg' w.1.asIdeal ≤ 3 := by
    rw [← hsum3]
    refine Finset.single_le_sum (f := fun P => v.asIdeal.inertiaDeg' P) (fun _ _ => Nat.zero_le _) ?_
    exact (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 K)).mpr ⟨w.1.isPrime, hlies⟩
  omega

theorem mul_cpow_shift_eq_pow_mul_of_eq_cpow_neg (vol c₁ c₂ e₁ e₂ N x s s₀ : ℂ) (hN : N ≠ 0) (n : ℕ)
    (hx : x = N ^ (-s₀)) :
    vol * (c₁ * c₂ * (e₁ * e₂ ^ 2 * N ^ ((3 * (n : ℂ)) * (1 / 2 - (s + s₀))))) =
      x ^ (3 * n) * (vol * (c₁ * c₂ * (e₁ * e₂ ^ 2 * N ^ ((3 * (n : ℂ)) * (1 / 2 - s))))) := by
  subst hx
  have key : (N : ℂ) ^ ((3 * (n : ℂ)) * (1 / 2 - (s + s₀))) =
      (N ^ (-s₀)) ^ (3 * n) * N ^ ((3 * (n : ℂ)) * (1 / 2 - s)) := by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hN]
    congr 1
    push_cast
    ring
  rw [key]
  ring

theorem eq_natCast_cpow_neg_of_eq_ofReal_cpow_of_eq_inv (x : ℂ) (m : ℝ) (N : ℕ) (s : ℂ)
    (hx : x = ((m : ℝ) : ℂ) ^ s) (hm : m = ((N : ℕ) : ℝ)⁻¹) : x = (N : ℂ) ^ (-s) := by
  rw [hx, hm, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.cpow_neg,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne)]

theorem absNorm_eq_absNorm_pow_inertiaDeg_of_mem_primeFibre (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ 𝔓 ∈ primeFibre ℚ K v,
      (Ideal.absNorm 𝔓.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  intro 𝔓 h𝔓
  have h : 𝔓.under (𝓞 ℚ) = v := (mem_primeFibre ℚ v 𝔓).mp h𝔓
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h]; rfl⟩
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal v.asIdeal v.isPrime v.ne_bot]
  push_cast
  rfl

open scoped Classical in

theorem heckeRootNumber_eq_mul_finprod_primeFibre_mul_prod_mul_finprod_and_mul_heckeConductor_cpow_eq
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (hfinε : {𝔓 : HeightOneSpectrum (𝓞 K) | LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓) ≠ 1}.Finite)
    (hfinQ : {𝔓 : HeightOneSpectrum (𝓞 K) | LanglandsTunnell.Converse.pinnedExp K χ 𝔓 ≠ 0}.Finite)
    (εA : ℂ) (hεA : ∀ χ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, LanglandsTunnell.HeckeTate.heckeRootNumber K χ' aR kC =
      εA * ∏ᶠ 𝔓 : HeightOneSpectrum (𝓞 K), LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ' 𝔓))
    (Qv : ℂ → ℂ)
    (hQv : ∀ s : ℂ, ((∏ᶠ 𝔓 ∈ primeFibre ℚ K v,
      (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (LanglandsTunnell.Converse.pinnedExp K χ 𝔓) : ℝ) : ℂ) ^ (1 / 2 - s) = Qv s) :
    LanglandsTunnell.HeckeTate.heckeRootNumber K χ aR kC =
        εA *
        (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓)) *
        (∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓)) *
        ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓) ∧
      ∀ s : ℂ,
        LanglandsTunnell.HeckeTate.heckeRootNumber K χ aR kC *
            ((LanglandsTunnell.HeckeTate.heckeConductor K χ : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - s) =
          LanglandsTunnell.HeckeTate.heckeRootNumber K χ aR kC *
            (Qv s * (((∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
        (LanglandsTunnell.Converse.pinnedExp K χ 𝔓)) *
              ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
                (LanglandsTunnell.Converse.pinnedExp K χ 𝔓) : ℝ) : ℂ) ^
              (1 / 2 - s)) := by
  have hnn : ∀ T : Set (HeightOneSpectrum (𝓞 K)),
      0 ≤ ∏ᶠ 𝔓 ∈ T, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (LanglandsTunnell.Converse.pinnedExp K χ 𝔓) := fun T =>
    finprod_nonneg fun 𝔓 => finprod_nonneg fun _ => zpow_nonneg (Nat.cast_nonneg _) _
  have hrest : 0 ≤ (∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
        (LanglandsTunnell.Converse.pinnedExp K χ 𝔓)) *
      ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
        (LanglandsTunnell.Converse.pinnedExp K χ 𝔓) :=
    mul_nonneg (Finset.prod_nonneg fun w _ => hnn _) (hnn _)
  refine ⟨?_, ?_⟩
  · rw [hεA χ,
      mul_finprod_stdRootNumberAt_eq_mul_finprod_primeFibre_mul_prod_erase_mul_finprod_compl K χ εA S v hv hfinε]
  · intro s
    unfold LanglandsTunnell.HeckeTate.heckeConductor
    rw [finprod_absNorm_zpow_pinnedExp_eq_finprod_primeFibre_mul_prod_erase_mul_finprod_compl K χ S v hv
      hfinQ, mul_assoc, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (hnn _) hrest, hQv s]

theorem finprod_compl_stdRootNumberAt_mul_comp_eq_and_finprod_compl_absNorm_zpow_pinnedExp_mul_comp_eq
    (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμu : IsUnitaryChar (𝓞 K) K μ)
    (θ₁ θ₂ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hθ₁u : IsUnitaryChar (𝓞 ℚ) ℚ θ₁) (hθ₂u : IsUnitaryChar (𝓞 ℚ) ℚ θ₂)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (hθ₁ : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt θ₁ w)
    (hθ₂ : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt θ₂ w)
    (hlev : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ S →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓) = 0) :
    (∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
        (localChar (μ * θ₂.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) =
      ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
        (localChar (μ * θ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) ∧
    (∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
        (LanglandsTunnell.Converse.pinnedExp K
          (μ * θ₂.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) =
      ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
        (LanglandsTunnell.Converse.pinnedExp K
          (μ * θ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) := by
  have hoff : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ S →
      LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar (μ * θ₂.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
          LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar (μ * θ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) ∧
        LanglandsTunnell.Converse.pinnedExp K (μ * θ₂.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 =
          LanglandsTunnell.Converse.pinnedExp K (μ * θ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 := by
    intro 𝔓 hw
    have hnb : ¬ IsBadPlace K μ (𝔓.under (𝓞 ℚ)) := fun h => hw ((hSbad _).mp h)
    have hμ0 : LanglandsTunnell.TateLocal.HasConductorExponentAt K 𝔓 (localChar μ 𝔓) 0 := by
      refine LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt K μ 𝔓 ?_
      by_contra hr
      exact hnb (Or.inr ⟨𝔓, (mem_primeFibre ℚ _ 𝔓).mpr rfl, hr⟩)
    have h1 := stdRootNumberAt_and_pinnedExp_localChar_mul_comp_idelicNorm_eq_of_zero K μ θ₁ hθ₁u 𝔓
      (hθ₁ _ hw) hμ0 (hμu _) (LanglandsTunnell.TateLocal.psiLocal_ne_one K 𝔓) (hlev 𝔓 hw)
    have h2 := stdRootNumberAt_and_pinnedExp_localChar_mul_comp_idelicNorm_eq_of_zero K μ θ₂ hθ₂u 𝔓
      (hθ₂ _ hw) hμ0 (hμu _) (LanglandsTunnell.TateLocal.psiLocal_ne_one K 𝔓) (hlev 𝔓 hw)
    exact ⟨h2.1.trans h1.1.symm, h2.2.trans h1.2.symm⟩
  exact ⟨finprod_mem_congr rfl fun 𝔓 h𝔓 => (hoff 𝔓 h𝔓).1,
    finprod_mem_congr rfl fun 𝔓 h𝔓 => by rw [(hoff 𝔓 h𝔓).2]⟩

theorem toAdd_unzero_exp_int (n : ℤ) (h : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0) :
    (WithZero.unzero h).toAdd = n :=
  congrArg Multiplicative.toAdd (WithZero.coe_inj.mp (WithZero.coe_unzero h))

theorem modulus_uniformizerUnit_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    (LanglandsTunnell.TateLocal.modulus
        ((NumberField.AdelicLevel.uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v, coe_nnnorm,
    NumberField.FinitePlace.norm_def, NumberField.AdelicLevel.valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp_int, zpow_neg_one,
    NNReal.coe_inv, NNReal.coe_natCast]

theorem finprod_eval_euler_and_dual_heckeDatum_eq_one_of_forall_not_isUnramifiedCharAt
    {F : Type} [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace F, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace F, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ)
    (T : Set (HeightOneSpectrum (𝓞 F))) (x y : HeightOneSpectrum (𝓞 F) → ℂ)
    (h : ∀ 𝔓 ∈ T, ¬ NumberField.TateGlobal.IsUnramifiedCharAt χ 𝔓) :
    (∏ᶠ 𝔓 ∈ T, ((LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).euler 𝔓).eval (x 𝔓)) = 1 ∧
      ∏ᶠ 𝔓 ∈ T, ((LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).dual 𝔓).eval (y 𝔓) = 1 := by
  refine ⟨?_, ?_⟩
  · exact (finprod_mem_congr rfl fun 𝔓 h𝔓 => by
      simp only [LanglandsTunnell.HeckeTate.heckeDatum]
      rw [if_neg (h 𝔓 h𝔓), Polynomial.eval_C]).trans (finprod_mem_one T)
  · exact (finprod_mem_congr rfl fun 𝔓 h𝔓 => by
      simp only [LanglandsTunnell.HeckeTate.heckeDatum]
      rw [if_neg (h 𝔓 h𝔓), Polynomial.eval_C]).trans (finprod_mem_one T)

theorem multiplier_ne_zero_of_hasConductorExponentAt_of_norm_eq_one (w : HeightOneSpectrum (𝓞 ℚ))
    (ζ τ : (w.adicCompletion ℚ)ˣ →* ℂˣ) (n b : ℕ) (hn : 1 ≤ n)
    (hτ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ w τ n)
    (hτu : ‖((τ (NumberField.AdelicLevel.uniformizerUnit ℚ w) : ℂˣ) : ℂ)‖ = 1)
    (hζ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ w ζ b) (hζu : ∀ z, ‖((ζ z : ℂˣ) : ℂ)‖ = 1)
    (hlt : b < n) (u : (w.adicCompletion ℚ)ˣ) (x : ℂ) :
    ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real
        (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) : ℂ)⁻¹ *
      (((ζ u : ℂˣ) : ℂ) * ((τ u : ℂˣ) : ℂ)) * LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w (ζ * τ) *
      LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w τ ^ 2 * (Ideal.absNorm w.asIdeal : ℂ) ^ x ≠ 0 := by
  have hvol : ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real
      (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) : ℂ) ≠ 0 :=
    selfDualHaarAt_real_adicCompletionIntegers_ne_zero w
  have hζτ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ w (ζ * τ) n := by
    rw [mul_comm ζ τ]
    exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt ℚ w τ ζ n b
      hτ hζ hlt
  have hζτu : ‖(((ζ * τ) (NumberField.AdelicLevel.uniformizerUnit ℚ w) : ℂˣ) : ℂ)‖ = 1 := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hζu, hτu, one_mul]
  have hε1 : LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w (ζ * τ) ≠ 0 :=
    LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt ℚ w (ζ * τ) n hn hζτ hζτu
  have hε2 : LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w τ ≠ 0 :=
    LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt ℚ w τ n hn hτ hτu
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : (Ideal.absNorm w.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hvol)
    (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))) hε1) (pow_ne_zero 2 hε2))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hN))

theorem isUnramifiedCharAt_of_hasConductorExponentAt_localChar_zero (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F))
    (h : LanglandsTunnell.TateLocal.HasConductorExponentAt F v (localChar χ v) 0) :
    NumberField.TateGlobal.IsUnramifiedCharAt χ v := by
  intro t ht ht'
  refine (LanglandsTunnell.TateLocal.hasConductorExponentAt_zero_iff F v).mp h t ?_
  have h1 : Valued.v (t : v.adicCompletion F) ≤ 1 := ht
  have h2 : Valued.v ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 := ht'
  have h3 : Valued.v (t : v.adicCompletion F) *
      Valued.v ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h4 := mul_le_mul_right h2 (Valued.v (t : v.adicCompletion F))
  rw [h3, mul_one] at h4
  exact le_antisymm h1 h4

theorem heckeRootNumber_ne_zero_and_mul_heckeConductor_cpow_ne_zero_of_isAdmissibleTwist
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist K χ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hram : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ S → ¬ IsUnramifiedCharAt χ 𝔓)
    (hlev : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ S →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓) = 0) :
    LanglandsTunnell.HeckeTate.heckeRootNumber K χ aR kC ≠ 0 ∧
      ∀ s : ℂ, LanglandsTunnell.HeckeTate.heckeRootNumber K χ aR kC *
        ((LanglandsTunnell.HeckeTate.heckeConductor K χ : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - s) ≠ 0 := by
  have hε : ∀ 𝔓 : HeightOneSpectrum (𝓞 K),
      LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓) ≠ 0 := fun 𝔓 => by
    obtain ⟨n, hn⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K 𝔓 (localChar χ 𝔓)
      (NumberField.TateGlobal.continuous_localChar χ hχ.2.1 𝔓)
    rcases eq_or_ne n 0 with rfl | hn0
    · have hS : 𝔓.under (𝓞 ℚ) ∉ S := fun h =>
        hram 𝔓 h (isUnramifiedCharAt_of_hasConductorExponentAt_localChar_zero K χ 𝔓 hn)
      exact ne_of_eq_of_ne (LanglandsTunnell.TateLocal.stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero K 𝔓
        (localChar χ 𝔓) hn (hχ.2.2 _) (hlev 𝔓 hS) (LanglandsTunnell.TateLocal.psiLocal_ne_one K 𝔓)) one_ne_zero
    · exact LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt K 𝔓 (localChar χ 𝔓) n
        (Nat.one_le_iff_ne_zero.mpr hn0) hn (hχ.2.2 _)
  have hW : LanglandsTunnell.HeckeTate.heckeRootNumber K χ aR kC ≠ 0 := by
    unfold LanglandsTunnell.HeckeTate.heckeRootNumber
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ => by
      unfold LanglandsTunnell.signEpsilon; split_ifs; exacts [one_ne_zero, Complex.I_ne_zero])
      (Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ Complex.I_ne_zero)) (finprod_ne_zero hε)
  have hC : LanglandsTunnell.HeckeTate.heckeConductor K χ ≠ 0 := by
    unfold LanglandsTunnell.HeckeTate.heckeConductor
    exact finprod_ne_zero fun w => zpow_ne_zero _
      (Nat.cast_ne_zero.mpr (by have := NumberField.HeightOneSpectrum.one_lt_absNorm w; omega))
  exact ⟨hW, fun s => mul_ne_zero hW (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hC)))⟩

theorem isAdmissibleTwist_mul' (F : Type) [Field F] [NumberField F] (χ η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχ : IsAdmissibleTwist F χ) (hη : IsAdmissibleTwist F η) : IsAdmissibleTwist F (χ * η) := by
  obtain ⟨h1, h2, h3⟩ := hχ
  obtain ⟨h1', h2', h3'⟩ := hη
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.mul_apply, h1 u, h1' u, one_mul]
  · exact h2.mul h2'
  · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h3 x, h3' x, one_mul]

theorem cpow_ofReal_finprod_primeFibre_absNorm_zpow_eq_natCast_cpow_mul' (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (hfin : (primeFibre ℚ K v).Finite) (pe : HeightOneSpectrum (𝓞 K) → ℤ)
    (L : ℕ)
    (hN : ∀ 𝔓 ∈ primeFibre ℚ K v,
      (Ideal.absNorm 𝔓.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ v.asIdeal.inertiaDeg' 𝔓.asIdeal)
    (hL : ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * pe 𝔓 = (L : ℤ)) (s : ℂ) :
    ((∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (pe 𝔓) : ℝ) : ℂ) ^ (1 / 2 - s) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((L : ℂ) * (1 / 2 - s)) := by
  have hNv0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega)
  have hprod : ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (pe 𝔓) =
      ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (Ideal.absNorm v.asIdeal : ℝ) ^ ((v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * pe 𝔓) :=
    finprod_mem_congr rfl fun 𝔓 h𝔓 => by rw [hN 𝔓 h𝔓, ← zpow_natCast, ← zpow_mul]
  have hzp : ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (Ideal.absNorm v.asIdeal : ℝ) ^ ((v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * pe 𝔓) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (L : ℤ) := by
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin, ← hL, finsum_mem_eq_finite_toFinset_sum _ hfin]
    classical
    induction hfin.toFinset using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hNv0, ih]
  rw [hprod, hzp, zpow_natCast, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.cpow_nat_mul' (by rw [Complex.natCast_arg, mul_zero]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [Complex.natCast_arg, mul_zero]; exact Real.pi_pos.le)]

theorem exists_forall_finsum_inertiaDeg_mul_pinnedExp_eq_three_mul
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (b : HeightOneSpectrum (𝓞 K) → ℕ) (hb : ∀ 𝔓, HasConductorExponentAt K 𝔓 (localChar μ 𝔓) (b 𝔓))
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ c₀ : ℕ, ∀ (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (n : ℕ), c₀ ≤ n → HasConductorExponentAt ℚ w (localChar τ w) n →
      ∑ᶠ 𝔓 ∈ primeFibre ℚ K w, (w.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
          LanglandsTunnell.Converse.pinnedExp K
            (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 = ((3 * n : ℕ) : ℤ) := by
  have hfin : (primeFibre ℚ K w).Finite := primeFibre_finite K w
  obtain ⟨c₅, hc₅⟩ := exists_forall_lt_hasConductorExponentAt_comp_norm_of_le K hdeg w (hfin.toFinset.sup b)
  obtain ⟨c₂, hc₂⟩ := exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq K hdeg w
  refine ⟨max c₅ c₂, fun τ n hn hτn => ?_⟩
  have hb₀ : ∀ 𝔓 ∈ primeFibre ℚ K w, b 𝔓 ≤ hfin.toFinset.sup b := fun 𝔓 h =>
    Finset.le_sup (hfin.mem_toFinset.mpr h)
  have hmem : ∀ P : w.Extension (𝓞 K), P.1 ∈ primeFibre ℚ K w := fun P => (mem_primeFibre ℚ w P.1).mpr P.2
  have hA := hc₅ τ n hτn ((le_max_left c₅ c₂).trans hn)
  choose aE hbaE haE using hA
  have hν₁ : ∀ P : w.Extension (𝓞 K),
      HasConductorExponentAt K P.1
        (localChar (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) P.1) (aE P) := by
    intro P
    rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ τ w P]
    have hcomm : localChar μ P.1 * (localChar τ w).comp (Units.map (Algebra.norm (w.adicCompletion ℚ))) =
        (localChar τ w).comp (Units.map (Algebra.norm (w.adicCompletion ℚ))) * localChar μ P.1 :=
      MonoidHom.ext fun x => by rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_comm]
    rw [hcomm]
    exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt K P.1 _ _ (aE P)
      (b P.1) (haE P) (hb P.1) (lt_of_le_of_lt (hb₀ P.1 (hmem P)) (hbaE P))
  have hpe : ∀ P : w.Extension (𝓞 K), LanglandsTunnell.Converse.pinnedExp K
      (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) P.1 =
      (aE P : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1) := by
    intro P
    unfold LanglandsTunnell.Converse.pinnedExp
    rw [LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K P.1 (hν₁ P)]
  have h2 := hc₂ (localChar τ w) n ((le_max_right c₅ c₂).trans hn) hτn aE haE
  rw [← finsum_set_coe_eq_finsum_mem, Nat.cast_mul, Nat.cast_ofNat, ← h2]
  exact finsum_congr fun P => by rw [hpe P]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem right_identity_at_twist_at_point_archTwisted
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hS' : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure] :
    ∃ cS : ℂ, cS ≠ 0 ∧
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
        componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
    ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt τ p) →
      ∃ (L : ℂ → ℂ) (σ₀ : ℝ), ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
              ((inducedEulerPoly ℚ (inducedCoeff K μ) p.1).eval
                (LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ p.1 * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)))⁻¹)
            (L s) ∧
        globalZeta30 X.whittaker τ s g =
          ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
            (cS *
                archZeta30 ν_mul (fun h => X.whittakerArch (h * archComponent3 (𝓞 ℚ) ℚ g)) (τ.comp E) s 1 *
                (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
                 localZeta30 v (Measure.comap Units.val
                    (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
                  (X.whittakerLoc v) (localChar τ v) s (componentAt3 (𝓞 ℚ) ℚ v g)) *
                ∏ w ∈ S.erase v,
                  (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
                   localZeta30 w (Measure.comap Units.val
                    (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
                    (X.whittakerLoc w) (localChar τ w) s
                    (componentAt3 (𝓞 ℚ) ℚ w g))) *
            L s := by
  have _ := hcont
  have _ := hW
  have _ := hW'
  have _ := hcontW
  have _ := hcontW'
  have hfac := sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn K ψ μ D U gen X hX
    S hSbad hS hS' v hv E hE ν_mul
  obtain ⟨cS, hcS, hdirect, -⟩ := hfac
  refine ⟨cS, hcS, fun g hg τ hτ hτS => ?_⟩
  have hL0 :=
    globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn K _hdeg ψ _hψ μ _hμ _hlev D U gen X hX hexp S hSbad hS τ hτ hτS g hg
  obtain ⟨L, σ₀, hL⟩ := hL0
  have hd0 := hdirect τ hτ g hg
  obtain ⟨σ₁, hσ₁⟩ := hd0
  refine ⟨L, max σ₀ σ₁, fun s hs => ⟨(hL s (lt_of_le_of_lt (le_max_left _ _) hs)).1, ?_⟩⟩
  rw [(hL s (lt_of_le_of_lt (le_max_left _ _) hs)).2, hσ₁ s (lt_of_le_of_lt (le_max_right _ _) hs)]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem left_identity_at_twist_at_point_archTwisted
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hS' : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure] :
    ∃ cS : ℂ, cS ≠ 0 ∧
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
        componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
    ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt τ p) →
      ∃ σ₁ : ℝ, ∀ u : ℂ, σ₁ < u.re →
        globalZetaDual31 X.whittaker τ u g =
          ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
            ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
            (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces ℚ / Real.sqrt |(NumberField.discr ℚ : ℝ)| : ℝ) : ℂ) *
            (cS * archZeta30 ν_mul (fun h => ∫ y : mixedEmbedding.mixedSpace ℚ,
                dualWhittakerFn3 X.whittakerArch (h *
                  lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) *
                    archComponent3 (𝓞 ℚ) ℚ (weylPrime3 * transposeInv3 g))) (τ⁻¹.comp E) u 1 *
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 localZetaDual31 v (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
                  (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) (X.whittakerLoc v) (localChar τ v) u
                  (componentAt3 (𝓞 ℚ) ℚ v g)) *
              ∏ w ∈ S.erase v,
                (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
                 ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set
                   (w.adicCompletion ℚ)) : ℂ)⁻¹ *
                   localZetaDual31 w (Measure.comap Units.val
                    (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
                    (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w) (X.whittakerLoc w) (localChar τ w) u
                    (componentAt3 (𝓞 ℚ) ℚ w g))) *
          (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
              ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v.1).eval
                  (((TateGlobal.localChar τ⁻¹ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) *
                    (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-u)))⁻¹) := by
  have hfac := sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn K ψ μ D U gen X hX
    S hSbad hS hS' v hv E hE ν_mul
  obtain ⟨cS, hcS, -, hdual⟩ := hfac
  refine ⟨cS, hcS, fun g hg τ hτ hτS => ?_⟩
  have hτi : IsAdmissibleTwist ℚ τ⁻¹ := isAdmissibleTwist_inv τ hτ
  have hτSi : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt τ⁻¹ p :=
    fun p hp => isUnramifiedCharAt_inv τ p (hτS p hp)
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      componentAt3 (𝓞 ℚ) ℚ w (weylPrime3 * transposeInv3 g) =
        weylPrime3 * transposeInv3 (componentAt3 (𝓞 ℚ) ℚ w g) := by
    intro w
    rw [map_mul, componentAt3_weylPrime3 w, componentAt3_transposeInv3 w]
  have hg' : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
      componentAt3 (𝓞 ℚ) ℚ w (weylPrime3 * transposeInv3 g) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
    intro w hw
    rw [hcomp w]
    exact mul_mem (weylPrime3_mem_localMaximalCompact3 w)
      (transposeInv3_mem_localMaximalCompact3 w (componentAt3 (𝓞 ℚ) ℚ w g) (hg w hw))
  have hchar : ∀ w : HeightOneSpectrum (𝓞 ℚ), (localChar τ⁻¹ w)⁻¹ = localChar τ w := by
    intro w
    rw [localChar_inv τ w]
    exact inv_inv (localChar τ w)
  have hu0 :=
    dual_unfolding_at_twist K _hdeg ψ _hψ μ _hμ _hlev D U gen X hX hcont hW hW' hcontW hcontW' hexp S hSbad hS' τ⁻¹ hτi
      hτSi (weylPrime3 * transposeInv3 g) hg'
  obtain ⟨σ₀, hσ₀⟩ := hu0
  have hd0 := hdual τ⁻¹ hτi (weylPrime3 * transposeInv3 g) hg'
  obtain ⟨σ₁, hσ₁⟩ := hd0
  refine ⟨max σ₀ σ₁, fun u hu => ?_⟩
  unfold globalZetaDual31
  rw [← dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn K ψ μ D U gen X hX hcont,
    hσ₀ u (lt_of_le_of_lt (le_max_left _ _) hu), hσ₁ u (lt_of_le_of_lt (le_max_right _ _) hu)]
  simp only [hcomp, localZeta31_dualWhittakerFn3_eq_localZetaDual31_inv, hchar]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem lfun_relations_at_twist_type
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hτ : IsAdmissibleTwist ℚ τ)
    (e : ℤ) (hτinf : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 e) :
    ∃ (Λ Λd : ℂ → ℂ) (σ : ℝ), Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
      (∀ s : ℂ, σ < s.re → Λ s ≠ 0 ∧
        Λ s = (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).archFactor s *
          (LanglandsTunnell.HeckeTate.heckeDatum K
            (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).LFun s) ∧
      (∀ u : ℂ, σ < u.re →
        Λd u = (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).archFactorDual u *
          (LanglandsTunnell.HeckeTate.heckeDatum K
            (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).LFunDual u) ∧
      (LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).Converges ∧
      (0 : ℝ) <
        LanglandsTunnell.HeckeTate.heckeConductor K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) ∧
      ∀ s : ℂ,
        Λ s =
          LanglandsTunnell.HeckeTate.heckeRootNumber K
            (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) (fun w hw => aR w hw + (e : ZMod 2)) kC *
            ((LanglandsTunnell.HeckeTate.heckeConductor K
                (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - s) *
            Λd (1 - s) := by
  have h0 := inducedL_fe K μ _hμ _hns uR aR uC kC huR huC τ hτ 0 e hτinf
  obtain ⟨hnice, -⟩ := h0
  simp only [add_zero] at hnice
  obtain ⟨-, hconv, hN, Λ, Λd, hΛ, hΛd, -, -, hL, hLd, hfe⟩ := hnice
  have hgR :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).gammaR =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).gammaR := rfl
  have hgC :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).gammaC =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).gammaC := rfl
  have hgRd :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).gammaRDual =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).gammaRDual := rfl
  have hgCd :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).gammaCDual =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).gammaCDual := rfl
  have habs :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).abscissa = 1 := rfl
  have hcen :
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).center = 1 / 2 := rfl
  have harch : ∀ s : ℂ,
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).archFactor s =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).archFactor s := by
    intro s
    unfold LanglandsTunnell.LDatum.archFactor
    rw [hgR, hgC]
  have harchd : ∀ s : ℂ,
      (LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).archFactorDual s =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).archFactorDual s := by
    intro s
    unfold LanglandsTunnell.LDatum.archFactorDual
    rw [hgRd, hgCd]
  have hσ0 := archFactor_ne_zero_and_archFactorDual_ne_zero (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC)
  obtain ⟨σ₃, hσ₃⟩ := hσ0
  refine ⟨Λ, Λd, max 1 σ₃, hΛ, hΛd, fun s hs => ?_, fun u hu => ?_, hconv, hN, fun s => ?_⟩
  · have hs1 :
        (LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).abscissa < s.re := by
      rw [habs]
      exact lt_of_le_of_lt (le_max_left _ _) hs
    have hs3 : σ₃ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have h := hL s hs1
    simp only [one_mul, harch] at h
    refine ⟨?_, h⟩
    rw [h]
    exact mul_ne_zero (hσ₃ s hs3).1 (hconv s hs1).2.2.1
  · have hu1 :
        (LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (e : ZMod 2)) uC kC).abscissa < u.re := by
      rw [habs]
      exact lt_of_le_of_lt (le_max_left _ _) hu
    have h := hLd u hu1
    simp only [one_mul, harchd] at h
    exact h
  · have h := hfe s
    rw [hcen] at h
    rw [h]
    congr 1
    · congr 2
      norm_num
    · congr 1
      norm_num

theorem archZeta30_comp_eq_archZeta30_comp_of_isArchCompAt
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e e' : ℤ)
    (hσ : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e)
    (hτ : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 e') (he : (-1 : ℂ) ^ e = (-1 : ℂ) ^ e') (s : ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archZeta30 ν_mul Warch (σ.comp E) s g = archZeta30 ν_mul Warch (τ.comp E) (s + t) g := by
  unfold archZeta30
  congr 1
  funext a
  have hw := Rat.isReal_infinitePlace
  have hx0 : (a : InfiniteAdeleRing ℚ) Rat.infinitePlace ≠ 0 :=
    (Units.map (Pi.evalMonoidHom (fun v : InfinitePlace ℚ => v.Completion) Rat.infinitePlace) a).ne_zero
  have hnorm : ‖(a : InfiniteAdeleRing ℚ)‖ = ‖(a : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ := by
    rw [NumberField.InfiniteAdeleRing.norm_def, Fintype.prod_subsingleton _ Rat.infinitePlace,
      NumberField.InfinitePlace.mult, if_pos hw, pow_one]
  have hsign : (NumberField.InfinitePlace.Completion.extensionEmbedding Rat.infinitePlace
      ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace) /
        (‖(a : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ : ℂ)) ^ e =
      (NumberField.InfinitePlace.Completion.extensionEmbedding Rat.infinitePlace
      ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace) /
        (‖(a : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ : ℂ)) ^ e' := by
    have hr : (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace) : ℂ) =
        NumberField.InfinitePlace.Completion.extensionEmbedding Rat.infinitePlace
          ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace) :=
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw _
    have hn : ‖(a : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ =
        |NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
          ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace)| := by
      have := (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace)
      rw [Real.norm_eq_abs] at this
      exact this.symm
    have hr0 : NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((a : InfiniteAdeleRing ℚ) Rat.infinitePlace) ≠ 0 := (map_ne_zero _).mpr hx0
    rw [← hr, hn]
    rcases hr0.lt_or_gt with hlt | hgt
    · rw [abs_of_neg hlt, Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.mpr hr0), he]
    · rw [abs_of_pos hgt, div_self (Complex.ofReal_ne_zero.mpr hr0), one_zpow, one_zpow]
  have hσa : (((σ.comp E) a : ℂˣ) : ℂ) = ((‖(a : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ : ℂ)) ^ t *
      (((τ.comp E) a : ℂˣ) : ℂ) := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, apply_of_infPart_eq_of_isArchCompAt σ E hE t e hσ a Rat.infinitePlace hw,
      apply_of_infPart_eq_of_isArchCompAt τ E hE 0 e' hτ a Rat.infinitePlace hw, hsign,
      NumberField.InfinitePlace.mult, if_pos hw, Nat.cast_one, one_mul, one_mul, Complex.cpow_zero, one_mul]
  rw [hσa, hnorm, show s + t - 1 = t + (s - 1) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx0))]
  ring

theorem eq_neg_one_of_inv_eq_psiQ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf) :
    a = -1 := by

  have key : ∀ q : ℚ, Complex.exp ((2 * Real.pi * Complex.I) * ((a * q : ℚ) : ℂ)) *
      Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ)) = 1 := by
    intro q
    have h1 : ψ (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)
        (algebraMap ℚ (InfiniteAdeleRing ℚ) q)) =
        NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) (a * q)) := by
      rw [show ψ (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)
          (algebraMap ℚ (InfiniteAdeleRing ℚ) q)) = (ψ.compAddMonoidHom
            (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))) (algebraMap ℚ (InfiniteAdeleRing ℚ) q)
          from rfl, hψinf, hpsiInf, ← map_mul]
    have h2 : ψ⁻¹ (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)
        (algebraMap ℚ (InfiniteAdeleRing ℚ) q)) =
        NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) q) := by
      rw [hψQ, NumberField.StandardAddChar.psiQ_apply, AddMonoidHom.inl_apply]
      change NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) q) *
        NumberField.StandardAddChar.psiFin 0 = _
      rw [AddChar.map_zero_eq_one, mul_one]
    rw [AddChar.inv_apply', h1] at h2
    rw [← NumberField.StandardAddChar.psiArch_algebraMap, ← NumberField.StandardAddChar.psiArch_algebraMap, ← h2,
      mul_inv_cancel₀]
    rw [NumberField.StandardAddChar.psiArch_algebraMap]
    exact Complex.exp_ne_zero _
  by_contra ha
  have ha1 : (a + 1 : ℚ) ≠ 0 := fun h => ha (by linarith)
  have h := key (1 / (2 * (a + 1)))
  rw [← Complex.exp_add, ← mul_add] at h
  have hq : ((a * (1 / (2 * (a + 1))) : ℚ) : ℂ) + ((1 / (2 * (a + 1)) : ℚ) : ℂ) = 1 / 2 := by
    have ha1' : ((a : ℂ) + 1) ≠ 0 := by exact_mod_cast ha1
    push_cast
    field_simp
  rw [hq, show (2 * Real.pi * Complex.I) * (1 / 2 : ℂ) = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I] at h
  norm_num at h

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem instance_right_line'
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
      componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hτS : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt τ p)
    (hfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), (primeFibre ℚ K p).Finite)
    (hram : ∀ w ∈ S, w ≠ v → ∀ 𝔓 ∈ primeFibre ℚ K w,
      ¬ IsUnramifiedCharAt (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
    (hconv :
      (LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).Converges)
    (cR : ℂ) (A L : ℂ → ℂ) (σ₀ : ℝ)
    (hRτ : ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
              ((inducedEulerPoly ℚ (inducedCoeff K μ) p.1).eval
                (LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ p.1 * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)))⁻¹)
            (L s) ∧
        globalZeta30 X.whittaker τ s g =
          ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
            (cR *
                A s *
                (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
                 localZeta30 v (Measure.comap Units.val
                    (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
                  (X.whittakerLoc v) (localChar τ v) s (componentAt3 (𝓞 ℚ) ℚ v g)) *
                ∏ w ∈ S.erase v,
                  (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
                   localZeta30 w (Measure.comap Units.val
                    (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
                    (X.whittakerLoc w) (localChar τ w) s
                    (componentAt3 (𝓞 ℚ) ℚ w g))) *
            L s)
    (Z : ℂ → ℂ) (σZ : ℝ) (hZ : ∀ s : ℂ, σZ < s.re → Z s = globalZeta30 X.whittaker τ s g)
    (Λ : ℂ → ℂ) (σΛ : ℝ)
    (hΛ :
      (∀ s : ℂ, σΛ < s.re → Λ s ≠ 0 ∧
        Λ s = (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactor s *
          (LanglandsTunnell.HeckeTate.heckeDatum K
            (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).LFun s))
    (Zv : ℂ → ℂ) (σv : ℝ)
    (hZv : ∀ s : ℂ, σv < s.re →
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
       localZeta30 v (Measure.comap Units.val
          (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
        (X.whittakerLoc v) (localChar τ v) s (componentAt3 (𝓞 ℚ) ℚ v g)) =
        Zv s)
    (P : HeightOneSpectrum (𝓞 ℚ) → ℂ → ℂ) (σw : HeightOneSpectrum (𝓞 ℚ) → ℝ)
    (hheld : ∀ w ∈ S.erase v, ∀ s : ℂ, σw w < s.re →
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
       localZeta30 w (Measure.comap Units.val
        (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
        (X.whittakerLoc w) (localChar τ w) s
        (componentAt3 (𝓞 ℚ) ℚ w g)) =
        P w s)
    (e : ℂ → ℂ) (σe : ℝ)
    (hfib : ∀ s : ℂ, σe < s.re →
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
              uR aR uC kC).euler 𝔓).eval (((LanglandsTunnell.HeckeTate.heckeDatum K
                  (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
                      uR aR uC kC).norm 𝔓 : ℂ) ^ (-s)))⁻¹) * e s =
        1) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactor s * Z s =
        ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) * cR *
          A s *
          Zv s * (∏ w ∈ S.erase v, P w s) * Λ s * e s := by
  have _ := hcont
  have _ := hW
  have _ := hW'
  have _ := hcontW
  have _ := hcontW'
  have _ := hexp
  have _ := hSbad
  have _ := hS
  have _ := hg
  obtain ⟨M, hM⟩ := ((S.erase v).image σw).exists_le
  refine ⟨max (max (max 1 σ₀) (max σZ σΛ)) (max (max σv σe) M), fun s hs => ?_⟩
  simp only [max_lt_iff] at hs
  obtain ⟨⟨⟨h1, hs₀⟩, hsZ, hsΛ⟩, ⟨hsv, hse⟩, hsM⟩ := hs
  have hmult := multipliable_inv_of_summable_norm_sub_one _ (hconv s (by change (1 : ℝ) < s.re; exact h1)).1
  have key := congrArg (· * e s)
    (LFun_heckeDatum_eq_finprod_fibre_mul_inducedL K μ τ uR aR uC kC S v hv s (L s) hfin hτS hram hmult
      (hRτ s hs₀).1)
  beta_reduce at key
  rw [mul_right_comm, hfib s hse, one_mul] at key
  rw [hZ s hsZ, (hRτ s hs₀).2, hZv s hsv, (hΛ s hsΛ).2,
    Finset.prod_congr rfl fun w hw => hheld w hw s (lt_of_le_of_lt (hM _ (Finset.mem_image_of_mem σw hw)) hsM),
    ← key]
  ring

open scoped Classical in

theorem heckeRootNumber_eq_and_mul_heckeConductor_cpow_eq_of_twists'' (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ₁ θ₂ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (aR₁ aR₂ : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S) (L₁ L₂ : ℕ)
    (εA₁ εA₂ : ℂ)
    (hεA₁ : ∀ χ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, LanglandsTunnell.HeckeTate.heckeRootNumber K χ' aR₁ kC =
      εA₁ * ∏ᶠ 𝔓 : HeightOneSpectrum (𝓞 K), LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ' 𝔓))
    (hεA₂ : ∀ χ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, LanglandsTunnell.HeckeTate.heckeRootNumber K χ' aR₂ kC =
      εA₂ * ∏ᶠ 𝔓 : HeightOneSpectrum (𝓞 K), LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ' 𝔓))
    (hfin₁ε : {𝔓 : HeightOneSpectrum (𝓞 K) | LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
        (localChar (μ * θ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) ≠ 1}.Finite)
    (hfin₁Q : {𝔓 : HeightOneSpectrum (𝓞 K) | LanglandsTunnell.Converse.pinnedExp K
      (μ * θ₁.comp
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 ≠ 0}.Finite)
    (hfin₂ε : {𝔓 : HeightOneSpectrum (𝓞 K) | LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
        (localChar (μ * θ₂.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) ≠ 1}.Finite)
    (hfin₂Q : {𝔓 : HeightOneSpectrum (𝓞 K) | LanglandsTunnell.Converse.pinnedExp K
      (μ * θ₂.comp
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 ≠ 0}.Finite)
    (hfib : (primeFibre ℚ K v).Finite)
    (hL₁ : ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K
      (μ * θ₁.comp
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 = (L₁ : ℤ))
    (hL₂ : ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K
      (μ * θ₂.comp
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 = (L₂ : ℤ))
    (hN : ∀ 𝔓 ∈ primeFibre ℚ K v,
      (Ideal.absNorm 𝔓.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ v.asIdeal.inertiaDeg' 𝔓.asIdeal)
    (hagree : ∀ w ∈ S.erase v, ∀ 𝔓 ∈ primeFibre ℚ K w,
      LanglandsTunnell.Converse.pinnedExp K (μ * θ₂.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 =
        LanglandsTunnell.Converse.pinnedExp K (μ * θ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
    (hεoff : (∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
        (localChar (μ * θ₂.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) =
      ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
        (localChar (μ * θ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓))
    (hQoff : (∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
        (LanglandsTunnell.Converse.pinnedExp K
          (μ * θ₂.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) =
      ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
        (LanglandsTunnell.Converse.pinnedExp K
          (μ * θ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) :
    LanglandsTunnell.HeckeTate.heckeRootNumber K
        (μ * θ₁.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR₁ kC =
      εA₁ *
        (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
          (localChar (μ * θ₁.comp
            (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) *
        (∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
          (localChar (μ * θ₁.comp
            (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) *
        ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
        (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
          (localChar (μ * θ₁.comp
            (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) ∧
    LanglandsTunnell.HeckeTate.heckeRootNumber K
        (μ * θ₂.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR₂ kC =
      εA₂ *
        (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
          (localChar (μ * θ₂.comp
            (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) *
        (∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
          (localChar (μ * θ₂.comp
            (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) *
        ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
        (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
          (localChar (μ * θ₁.comp
            (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) ∧
    (∀ s : ℂ, LanglandsTunnell.HeckeTate.heckeRootNumber K
        (μ * θ₁.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR₁ kC *
        ((LanglandsTunnell.HeckeTate.heckeConductor K
          (μ * θ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) : ℝ) : ℂ) ^
          ((1 / 2 : ℂ) - s) =
      LanglandsTunnell.HeckeTate.heckeRootNumber K
        (μ * θ₁.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR₁ kC *
        ((Ideal.absNorm v.asIdeal : ℂ) ^ ((L₁ : ℂ) * (1 / 2 - s)) *
          (((∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
            (LanglandsTunnell.Converse.pinnedExp K
              (μ * θ₁.comp
              (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) *
            ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
            (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
              (LanglandsTunnell.Converse.pinnedExp K
                (μ * θ₁.comp
                (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) : ℝ) : ℂ) ^
            (1 / 2 - s))) ∧
    ∀ s : ℂ, LanglandsTunnell.HeckeTate.heckeRootNumber K
        (μ * θ₂.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR₂ kC *
        ((LanglandsTunnell.HeckeTate.heckeConductor K
          (μ * θ₂.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) : ℝ) : ℂ) ^
          ((1 / 2 : ℂ) - s) =
      LanglandsTunnell.HeckeTate.heckeRootNumber K
        (μ * θ₂.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR₂ kC *
        ((Ideal.absNorm v.asIdeal : ℂ) ^ ((L₂ : ℂ) * (1 / 2 - s)) *
          (((∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
            (LanglandsTunnell.Converse.pinnedExp K
              (μ * θ₁.comp
              (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) *
            ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
            (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
              (LanglandsTunnell.Converse.pinnedExp K
                (μ * θ₁.comp
                (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) : ℝ) : ℂ) ^
            (1 / 2 - s)) := by
  have hfibpow₁ := cpow_ofReal_finprod_primeFibre_absNorm_zpow_eq_natCast_cpow_mul' K v hfib
    (LanglandsTunnell.Converse.pinnedExp K (μ * θ₁.comp
    (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) L₁ hN hL₁
  have hfibpow₂ := cpow_ofReal_finprod_primeFibre_absNorm_zpow_eq_natCast_cpow_mul' K v hfib
    (LanglandsTunnell.Converse.pinnedExp K (μ * θ₂.comp
    (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) L₂ hN hL₂
  have hQheld : (∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
      (LanglandsTunnell.Converse.pinnedExp K
        (μ * θ₂.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) =
      (∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
      (LanglandsTunnell.Converse.pinnedExp K
        (μ * θ₁.comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) :=
    Finset.prod_congr rfl fun w hw => finprod_mem_congr rfl fun 𝔓 h𝔓 => by rw [hagree w hw 𝔓 h𝔓]
  have hreg₁ := heckeRootNumber_eq_mul_finprod_primeFibre_mul_prod_mul_finprod_and_mul_heckeConductor_cpow_eq K
    (μ * θ₁.comp
    (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR₁ kC S v hv hfin₁ε hfin₁Q εA₁ hεA₁
    (fun s => (Ideal.absNorm v.asIdeal : ℂ) ^ ((L₁ : ℂ) * (1 / 2 - s))) hfibpow₁
  have hreg₂ := heckeRootNumber_eq_mul_finprod_primeFibre_mul_prod_mul_finprod_and_mul_heckeConductor_cpow_eq K
    (μ * θ₂.comp
    (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR₂ kC S v hv hfin₂ε hfin₂Q εA₂ hεA₂
    (fun s => (Ideal.absNorm v.asIdeal : ℂ) ^ ((L₂ : ℂ) * (1 / 2 - s))) hfibpow₂
  refine ⟨hreg₁.1, ?_, hreg₁.2, ?_⟩
  · rw [hreg₂.1, hεoff]
  · intro s
    exact (hreg₂.2 s).trans (by rw [hQheld, hQoff])

theorem star_identity_of_local_collapses' (γv γw₁ γw₂ C₁ C₂ Qv₁ Qv₂ Qr Qt : ℂ → ℂ)
    (S E T εA₁ εA₂ εv₁ εv₂ εh₁ εh₂ εoff Sh ε₁ ε₂ : ℂ) (hA₂ : εA₂ ≠ 0)
    (hC₁ : ∀ s : ℂ, C₁ s = ε₁ * (Qv₁ s * Qr s)) (hC₂ : ∀ s : ℂ, C₂ s = ε₂ * (Qv₂ s * Qr s))
    (hε₁ : ε₁ = εA₁ * εv₁ * εh₁ * εoff) (hε₂ : ε₂ = εA₂ * εv₂ * εh₂ * εoff)
    (hγw : ∀ s : ℂ, γw₂ s = Sh * γw₁ s) (hεh : εh₂ = Sh * εh₁)
    (hγv : ∀ s : ℂ, γv s = S * εv₂ * Qv₂ s) (hεv₁ : εv₁ = T * E) (hQ : ∀ s : ℂ, T * Qv₁ s = Qt s) :
    ∀ s : ℂ, γv s * γw₂ s * C₁ s = (S * εA₁ * εA₂⁻¹) * E * Qt s * (γw₁ s * C₂ s) := by
  intro s
  have hinv : εA₂⁻¹ * εA₂ = 1 := inv_mul_cancel₀ hA₂
  rw [hC₁, hC₂, hγv, hγw, hε₁, hε₂, hεv₁, hεh, ← hQ]
  linear_combination (-(S * εA₁ * E * T * Qv₁ s * γw₁ s * εv₂ * Sh * εh₁ * εoff * Qv₂ s * Qr s)) * hinv

theorem finprod_localChar_comp_idelicNorm_mul_apply_neg_one
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∏ᶠ 𝔓 ∈ primeFibre ℚ K v,
        ((localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) 𝔓 (-1) : ℂˣ) : ℂ) =
      ((localChar ηA v (-1) : ℂˣ) : ℂ) * ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((localChar μ 𝔓 (-1) : ℂˣ) : ℂ) := by
  classical
  haveI := subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  letI hft : Fintype (v.Extension (𝓞 K)) := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) v
  have hcomm : ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ =
      μ * ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm :=
    MonoidHom.ext fun x => by rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_comm]

  have hfac : ∀ P : v.Extension (𝓞 K),
      ((localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) P.1 (-1) : ℂˣ) : ℂ) =
        ((localChar μ P.1 (-1) : ℂˣ) : ℂ) *
          ((localChar ηA v (-1) : ℂˣ) : ℂ) ^ Module.finrank (v.adicCompletion ℚ) (P.1.adicCompletion K) := by
    intro P
    haveI : Module.Free (v.adicCompletion ℚ) (P.1.adicCompletion K) := Module.Free.of_divisionRing _ _
    have hN : Units.map (↑(Algebra.norm (v.adicCompletion ℚ))) (-1 : (P.1.adicCompletion K)ˣ) =
        (-1) ^ Module.finrank (v.adicCompletion ℚ) (P.1.adicCompletion K) := by
      ext
      simp only [Units.coe_map, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
      rw [show (-1 : P.1.adicCompletion K) = algebraMap (v.adicCompletion ℚ) (P.1.adicCompletion K) (-1) by
          rw [map_neg, map_one]]
      exact Algebra.norm_algebraMap (R := v.adicCompletion ℚ) (S := P.1.adicCompletion K) _
    rw [hcomm, NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ ηA v P,
      MonoidHom.mul_apply, MonoidHom.comp_apply, hN, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
  have hsum : ∑ P : v.Extension (𝓞 K), Module.finrank (v.adicCompletion ℚ) (P.1.adicCompletion K) = 3 := by
    have h := Ideal.sum_ramification_inertia_extensions (𝓞 ℚ) ℚ K (𝓞 K) v
    rw [← finsum_eq_sum_of_fintype] at h
    rw [← finsum_eq_sum_of_fintype, ← hdeg, ← h]
    exact finsum_congr fun P =>
      (HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank ℚ K P).symm
  have hsq : ((localChar ηA v (-1) : ℂˣ) : ℂ) ^ 3 = ((localChar ηA v (-1) : ℂˣ) : ℂ) := by
    have h2 : ((localChar ηA v (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
    rw [pow_succ, h2, one_mul]
  have hmem : ∀ 𝔓, 𝔓 ∈ primeFibre ℚ K v ↔ 𝔓.under (𝓞 ℚ) = v := fun 𝔓 => mem_primeFibre ℚ v 𝔓
  rw [← finprod_set_coe_eq_finprod_mem, ← finprod_set_coe_eq_finprod_mem]
  change ∏ᶠ P : v.Extension (𝓞 K), _ = _ * ∏ᶠ P : v.Extension (𝓞 K), _
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Finset.prod_congr rfl fun P _ => hfac P,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, hsq, mul_comm]

open LanglandsTunnell LanglandsTunnell.CubicLambda

theorem isArchCompAt_mul_of_zero_zero_left (χ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (w : InfinitePlace ℚ) (e : ℤ)
    (hχ : IsArchCompAt ℚ χ w 0 0) (hη : IsArchCompAt ℚ η w 0 e) : IsArchCompAt ℚ (χ * η) w 0 e := by
  intro x
  have hx := hχ x
  have hx' := hη x
  simp only [mul_zero, Complex.cpow_zero, zpow_zero, one_mul] at hx
  change ((((χ * η) (archUnitHom w x) : ℂˣ)) : ℂ) = _
  change (((χ (archUnitHom w x) : ℂˣ)) : ℂ) = 1 at hx
  change (((η (archUnitHom w x) : ℂˣ)) : ℂ) = _ at hx'
  rw [MonoidHom.mul_apply, Units.val_mul, hx, hx', one_mul]

set_option maxHeartbeats 3200000 in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in
theorem solution_core_GEN
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
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (c : ℂ) (hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (hbad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
        X.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (h1 : ∀ w ∈ S, w ≠ v → X.whittakerLoc w 1 = 1)
    (hadm : ∀ w ∈ S, ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
      ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
        (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hψw : ∀ w ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hS' : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hψv : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (ω₃ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω₃ : IsAdmissibleTwist ℚ ω₃ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω₃ p ∧ eulerCoeff ℚ ω₃ p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω₃ v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (aQ : ℚ) (ha : aQ ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) aQ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) aQ * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(aQ : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
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
                (((ω₃ (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|aQ| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0)
    (hArchEq : X.whittakerArch = Warch)
    (harch₀ : ∃ (gInf₀ : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧ (-1 : ℂ) ^ e = 1) ∧
      ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf₀)) (σ.comp E) s 1 ≠ 0)
    :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ∀ (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (cη b : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η cη → cη ≤ b →
        (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v,
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
          NumberField.TateGlobal.localChar ηA v = η →
          LanglandsTunnell.Converse.IsAdmissibleTwist K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
        ∀ ℓ : ℕ, ((ℓ : ℤ) = ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) *
          LanglandsTunnell.Converse.pinnedExp K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) →

        (∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
          (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧
            ((η (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) ∧
          ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0) →
        ∀ (R₁ R₂ : Polynomial ℂ) (m : ℤ), R₁ ≠ 0 → R₂ ≠ 0 →
          (∀ g : LocalGL3 v,
            letI := localBorel ℚ v
            ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
              IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc
                v) η g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) η s g *
                  Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
                Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
              IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt
                ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                  (X.whittakerLoc v) η (1 - s) g *
                  (Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
                R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
                  (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s))) →
        ∀ s : ℂ,
          R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) =
            lam * ((∏ᶠ w ∈ primeFibre ℚ K v,
                ((NumberField.TateGlobal.localChar
                  (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
              ∏ᶠ w ∈ primeFibre ℚ K v,
                LanglandsTunnell.TateLocal.stdRootNumberAt K w
                  (NumberField.TateGlobal.localChar
                    (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  classical
  haveI := subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  obtain ⟨gInf₀, σ₀ar, hσ₀adm, ⟨t₀, e₀, hσ₀ar, he₀⟩, hnv₀⟩ := harch₀
  obtain ⟨hW0, -, -, -, -, hFEarch, -⟩ := hWarch
  have hlocFE := fun (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ∈ S) =>
    localFE_at_badPlace_of_deep_twist K ψ _hψ μ _hμ D U gen X hX hexp hbad S hSbad v hv h1 hadm hcent _hlev hψw w hw
  choose uF cF huF hcF using hlocFE
  have hμexp : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), ∃ b : ℕ, HasConductorExponentAt K 𝔓 (localChar μ 𝔓) b := fun 𝔓 =>
    LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K 𝔓 (localChar μ 𝔓)
      (continuous_localChar μ _hμ.2.1 𝔓)
  choose b hb using hμexp
  have hfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), (primeFibre ℚ K p).Finite := fun p => primeFibre_finite K p
  let b₀ : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun p => (hfin p).toFinset.sup b
  have hb₀ : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ 𝔓 ∈ primeFibre ℚ K p, b 𝔓 ≤ b₀ p := fun p 𝔓 h𝔓 =>
    Finset.le_sup ((hfin p).mem_toFinset.mpr h𝔓)
  have hHW := fun w (hw : w ∈ S) =>
    exists_forall_finprod_primeFibre_stdRootNumberAt_localChar_mul_comp_idelicNorm_mul_eq_pow_mul K _hdeg μ
      _hμ.2.2 b hb w
  choose cHW hcHW using hHW
  have hbωex := fun w (hw : w ∈ S) => exists_hasConductorExponentAt_localChar_centralChar K ψ μ _ X hX hcont hexp.1 w
  choose bω hbω using hbωex
  obtain ⟨cL, hcL⟩ := exists_forall_finsum_inertiaDeg_mul_pinnedExp_eq_three_mul K _hdeg μ b hb v
  let d : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun w =>
    if hw : w ∈ S then max (max (max (cF w hw) (cHW w hw)) cL) (max 2 (max (2 * b₀ w) (2 * bω w hw))) else 0
  have hd : ∀ w (hw : w ∈ S), cF w hw ≤ d w := fun w hw => by
    simp only [d, dif_pos hw]
    exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have hdHW : ∀ w (hw : w ∈ S), cHW w hw ≤ d w := fun w hw => by
    simp only [d, dif_pos hw]
    exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hdL : ∀ w (hw : w ∈ S), cL ≤ d w := fun w hw => by
    simp only [d, dif_pos hw]
    exact le_max_of_le_left (le_max_right _ _)
  have hdtwo : ∀ w (hw : w ∈ S), 2 ≤ d w := fun w hw => by
    simp only [d, dif_pos hw]
    exact le_max_of_le_right (le_max_left _ _)
  have hdb : ∀ w (hw : w ∈ S), 2 * b₀ w ≤ d w := fun w hw => by
    simp only [d, dif_pos hw]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hdbω : ∀ w (hw : w ∈ S), 2 * bω w hw ≤ d w := fun w hw => by
    simp only [d, dif_pos hw]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))

  obtain ⟨τ₀, hτ₀adm, hτ₀v, hτ₀held, hτ₀off, hτ₀arch⟩ := exists_comparisonTwist S v hv d
  obtain ⟨x, hxS⟩ := exists_heightOneSpectrum_ratRingOfIntegers_notMem S
  have hxv : x ≠ v := fun h => hxS (h ▸ hv)
  have hx_mem : x ∈ ({v, x} : Finset (HeightOneSpectrum (𝓞 ℚ))) := by simp
  have hv_mem : v ∈ ({v, x} : Finset (HeightOneSpectrum (𝓞 ℚ))) := by simp
  obtain ⟨σd, hσdadm, hσdx, hσddeep, hσdoff, hσdarch⟩ := exists_comparisonTwist {v, x} x hx_mem d
  obtain ⟨a, hda, ha_even, hσa⟩ := hσddeep v hv_mem hxv.symm
  have hσdheld : ∀ w ∈ S, w ≠ v → IsUnramifiedCharAt σd w := fun w hw hwv =>
    hσdoff w (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hwv, fun h => hxS (h ▸ hw)⟩)
  have hσdS : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt σd w := fun w hw => by
    by_cases hwx : w = x
    · subst hwx
      exact hσdx
    · exact hσdoff w (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hw (h ▸ hv), hwx⟩)
  obtain ⟨s₀, hs₀⟩ := exists_forall_apply_eq_modulus_cpow v (localChar τ₀ v) hτ₀v
  have hτσ₀adm : IsAdmissibleTwist ℚ (τ₀ * σd) := isAdmissibleTwist_mul τ₀ σd hτ₀adm hσdadm
  have hτ₀0 : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar τ₀ v) 0 :=
    LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt ℚ τ₀ v hτ₀v
  have hτσ₀a : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar (τ₀ * σd) v) a := by
    rw [show localChar (τ₀ * σd) v = localChar σd v * localChar τ₀ v from
      (MonoidHom.mul_comp τ₀ σd _).trans (mul_comm _ _)]
    exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt ℚ v _ _ a 0 hσa
      hτ₀0 (by have := hdtwo v hv; omega)
  have hν₀ram : ∀ 𝔓 ∈ primeFibre ℚ K v,
      ¬ IsUnramifiedCharAt (μ * (τ₀ * σd).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 :=
    (hcHW v hv (τ₀ * σd) a ((hdHW v hv).trans hda) hτσ₀a).1
  have hL₂₀ : ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      LanglandsTunnell.Converse.pinnedExp K
        (μ * (τ₀ * σd).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 = ((3 * a : ℕ) : ℤ) :=
    hcL (τ₀ * σd) a ((hdL v hv).trans hda) hτσ₀a
  have hν₀adm := isAdmissibleTwist_mul_comp_idelicNorm_of_isAdmissibleTwist K μ _hμ (τ₀ * σd) hτσ₀adm
  have hvol : ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
      (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) ≠ 0 :=
    selfDualHaarAt_real_adicCompletionIntegers_ne_zero v
  have hεvTwo₀ : (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
      (localChar (μ * (τ₀ * σd).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) ≠ 0 := by
    refine finprod_mem_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ hx hy => mul_ne_zero hx hy) ?_
    intro 𝔓 h𝔓
    obtain ⟨n, hn⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K 𝔓
      (localChar (μ * (τ₀ * σd).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
      (continuous_localChar _ hν₀adm.2.1 𝔓)
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      exact absurd (isUnramifiedCharAt_of_hasConductorExponentAt_localChar_zero K _ 𝔓 hn) (hν₀ram 𝔓 h𝔓)
    · exact LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt K 𝔓 _ n hn0 hn
        (hν₀adm.2.2 _)
  have hζu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((TateGlobal.localChar X.centralChar v z : ℂˣ) : ℂ)‖ = 1 := (hcent v hv).1
  have hζσ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v
      (TateGlobal.localChar X.centralChar v * localChar σd v) a := by
    have h := LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt ℚ v
      (localChar σd v) (TateGlobal.localChar X.centralChar v) a (bω v hv) hσa (hbω v hv)
      (by have := hdbω v hv; have := hdtwo v hv; omega)
    have hcomm : localChar σd v * TateGlobal.localChar X.centralChar v =
        TateGlobal.localChar X.centralChar v * localChar σd v :=
      MonoidHom.ext fun x => by rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_comm]
    rw [hcomm] at h
    exact h
  have huζσ : ‖(((TateGlobal.localChar X.centralChar v * localChar σd v)
      (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hζu, one_mul]
    exact hσdadm.2.2 _
  have ha0 : 0 < a := by have := hdtwo v hv; omega
  have hGv : ((TateGlobal.localChar X.centralChar v (uF v hv) : ℂˣ) : ℂ) * (((localChar σd v) (uF v hv) : ℂˣ) : ℂ) *
      (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (TateGlobal.localChar X.centralChar v * (localChar σd v)) *
        LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (localChar σd v) ^ (2 : ℕ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (mul_ne_zero
      (LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt ℚ v _ a ha0 hζσ huζσ)
      (pow_ne_zero _ (LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt ℚ v _ a ha0 hσa
        (hσdadm.2.2 _))))
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega)
  have hMv : (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((localChar μ 𝔓 (-1) : ℂˣ) : ℂ)) ≠ 0 :=
    finprod_mem_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ hx hy => mul_ne_zero hx hy)
      (fun 𝔓 _ => Units.ne_zero _)

  refine ⟨((TateGlobal.localChar X.centralChar v (uF v hv) : ℂˣ) : ℂ) * (((localChar σd v) (uF v hv) : ℂˣ) : ℂ) *
      (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (TateGlobal.localChar X.centralChar v * (localChar σd v)) *
        LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (localChar σd v) ^ (2 : ℕ)) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (a : ℂ)) * s₀) *
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
        (localChar (μ * (τ₀ * σd).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓))⁻¹ *
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((localChar μ 𝔓 (-1) : ℂˣ) : ℂ))⁻¹,
    mul_ne_zero (mul_ne_zero (mul_ne_zero hGv (fun h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1))
      (inv_ne_zero hεvTwo₀)) (inv_ne_zero hMv), ?_⟩
  intro η cη bη hηc hcb hdepth ηA hηAadm hηAv hηAK ℓ hℓ harch R₁ R₂ m hR₁ hR₂ hFE1
  obtain ⟨gInf, σar, hσaradm, ⟨tar, ear, hσar, hpar⟩, hnv⟩ := harch

  obtain ⟨β, hβadm, hβunits, -, hβoff, eβ, hβarch'⟩ :=
    HeckeCharacter.exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt {v}
      (Function.update (fun w : HeightOneSpectrum (𝓞 ℚ) => (1 : (w.adicCompletion ℚ)ˣ →* ℂˣ)) v η) (fun _ => cη)
      (fun w hw => by
        rw [Finset.mem_singleton] at hw
        subst hw
        rw [Function.update_self]
        exact hηc)
  have hβv : ∀ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
      ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ → localChar β v u = η u := by
    intro u h1 h2
    have h := hβunits v (Finset.mem_singleton_self v) u h1 h2
    rwa [Function.update_self] at h
  have hβoff' : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → IsUnramifiedCharAt β w := fun w hw =>
    hβoff w (by rwa [Finset.mem_singleton])
  have hβpar := NumberField.TateGlobal.prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt β hβadm.1
    hβadm.2.1 {v} (fun w hw => hβoff w hw) 0 eβ hβarch'
  rw [Finset.prod_singleton] at hβpar
  have hβneg : localChar β v (-1) = η (-1) :=
    hβv (-1) (by rw [Units.val_neg, Units.val_one]; exact neg_mem (one_mem _))
      (by rw [inv_neg_one, Units.val_neg, Units.val_one]; exact neg_mem (one_mem _))
  have heβ : (-1 : ℂ) ^ eβ = ((η (-1) : ℂˣ) : ℂ) := by rw [← hβpar, hβneg]

  obtain ⟨τ₁, hτ₁def⟩ : ∃ τ₁ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, τ₁ = τ₀ * β := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, σ = β⁻¹ * σd := ⟨_, rfl⟩
  have hτσ : τ₁ * σ = τ₀ * σd := by
    rw [hτ₁def, hσdef]
    exact MonoidHom.ext fun x => by
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
        mul_assoc, ← mul_assoc (β x), mul_inv_cancel, one_mul]
  have hτ₁adm : IsAdmissibleTwist ℚ τ₁ := hτ₁def ▸ isAdmissibleTwist_mul τ₀ β hτ₀adm hβadm
  have hτ₁off : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt τ₁ w := fun w hw =>
    hτ₁def ▸ isUnramifiedCharAt_mul ℚ τ₀ β w (hτ₀off w hw) (hβoff' w (fun h => hw (h ▸ hv)))
  have hτ₁arch : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ₁ w 0 eβ := fun w hw =>
    hτ₁def ▸ isArchCompAt_mul_of_zero_zero_left τ₀ β w eβ (hτ₀arch w hw) (hβarch' w hw)
  have hτ₁held : ∀ w ∈ S, w ≠ v → ∃ n : ℕ, d w ≤ n ∧ Even n ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ w (localChar τ₁ w) n := by
    intro w hw hwv
    obtain ⟨n, hdn, hev, hn⟩ := hτ₀held w hw hwv
    refine ⟨n, hdn, hev, ?_⟩
    rw [hτ₁def, show localChar (τ₀ * β) w = localChar τ₀ w * localChar β w from MonoidHom.mul_comp τ₀ β _]
    exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt ℚ w _ _ n 0 hn
      (LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt ℚ β w (hβoff' w hwv))
      (by have := hdtwo w hw; omega)
  have hσadm : IsAdmissibleTwist ℚ σ := hσdef ▸ isAdmissibleTwist_mul _ _ (isAdmissibleTwist_inv β hβadm) hσdadm
  have hσheld : ∀ w ∈ S, w ≠ v → IsUnramifiedCharAt σ w := fun w hw hwv =>
    hσdef ▸ isUnramifiedCharAt_mul ℚ _ _ w (isUnramifiedCharAt_inv β w (hβoff' w hwv)) (hσdheld w hw hwv)
  have hσS : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt σ w := fun w hw =>
    hσdef ▸ isUnramifiedCharAt_mul ℚ _ _ w (isUnramifiedCharAt_inv β w (hβoff' w (fun h => hw (h ▸ hv)))) (hσdS w hw)
  have hτ₂adm : IsAdmissibleTwist ℚ (τ₁ * σ) := isAdmissibleTwist_mul τ₁ σ hτ₁adm hσadm

  obtain ⟨θ, hθdef⟩ : ∃ θ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, θ = τ₁ * ηA⁻¹ := ⟨_, rfl⟩
  have hθv : IsUnramifiedCharAt θ v := by
    intro t h1 h2
    rw [hθdef, hτ₁def,
      show localChar (τ₀ * β * ηA⁻¹) v = localChar τ₀ v * localChar β v * (localChar ηA v)⁻¹ from rfl,
      MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hτ₀v t h1 h2, hβv t h1 h2, hηAv, one_mul,
      mul_inv_cancel]
  obtain ⟨sθ, hsθ⟩ := exists_forall_apply_eq_modulus_cpow v (localChar θ v) hθv
  have hθ0 : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar θ v) 0 :=
    LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt ℚ θ v hθv
  have hηθ : ηA * θ = τ₁ := by
    rw [hθdef]
    exact MonoidHom.ext fun x => by
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_comm, inv_mul_cancel_right]
  have hτ₁v : localChar τ₁ v = η * localChar θ v := by
    rw [← hηθ, show localChar (ηA * θ) v = localChar ηA v * localChar θ v from MonoidHom.mul_comp ηA θ _, hηAv]
  have hinst₁ : ∀ w (hw : w ∈ S), w ≠ v → ∃ n : ℕ, Even n ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ w (localChar τ₁ w) n ∧ d w ≤ n := by
    intro w hw hwv
    obtain ⟨n, hdn, hn_even, hn⟩ := hτ₁held w hw hwv
    exact ⟨n, hn_even, hn, hdn⟩
  choose n₁ hn₁even hn₁exp hn₁ge using hinst₁
  have hloc₁ := fun w (hw : w ∈ S) (hwv : w ≠ v) =>
    (hcF w hw).2 (localChar τ₁ w) (n₁ w hw hwv) (hn₁exp w hw hwv) (hτ₁adm.2.2 _) ((hd w hw).trans (hn₁ge w hw hwv))
  choose σA σB hblk₁ hwit₁ using hloc₁
  choose g₁ s₁ hs₁ hZ₁ using hwit₁
  have htv := exists_testVector_localZeta30_ne_zero K ψ _hψ μ D U gen X hX hexp hbad S hSbad v hv η
    (fun g => by
      obtain ⟨_, _, _, σg, _, -, hc, -⟩ := hFE1 g
      exact ⟨σg, hc⟩)
  obtain ⟨g₀, σ₀v, hconv₀, hne₀⟩ := htv
  have hshift₁ := localZeta30_unramifiedTwist_eq_shift v η (localChar θ v) sθ hsθ
  have hwall₁ := localZeta_relations_at_v_of_shift K ψ μ D U gen X hX v R₁ R₂ m η (localChar θ v) sθ g₀
    hshift₁ (hFE1 g₀)
  have hloc₂ := (hcF v hv).2 (localChar σd v) a hσa (hσdadm.2.2 _) ((hd v hv).trans hda)
  obtain ⟨σC, σD, hblk₂, g₂, s₂, hs₂, hZ₂⟩ := hloc₂
  have hshift₂ := localZeta30_unramifiedTwist_eq_shift v (localChar σd v) (localChar τ₀ v) s₀ hs₀
  have hmulcv : localChar (τ₁ * σ) v = localChar σd v * localChar τ₀ v := by
    rw [hτσ]
    exact (MonoidHom.mul_comp τ₀ σd _).trans (mul_comm _ _)
  let hOne : (w : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 w := fun w =>
    if hw : w ∈ S then (if hwv : w = v then hwv ▸ g₀ else g₁ w hw hwv) else 1
  let hTwo : (w : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 w := fun w =>
    if hw : w ∈ S then (if hwv : w = v then hwv ▸ g₂ else g₁ w hw hwv) else 1
  obtain ⟨gOne, hgOneS, hgOneOff, hgOneArch⟩ := exists_forall_componentAt3_eq_and_archComponent3_eq S hOne gInf
  obtain ⟨gTwo, hgTwoS, hgTwoOff, hgTwoArch⟩ := exists_forall_componentAt3_eq_and_archComponent3_eq S hTwo gInf₀
  have hgOne_v : componentAt3 (𝓞 ℚ) ℚ v gOne = g₀ := by
    rw [hgOneS v hv]
    simp [hOne, hv]
  have hgTwo_v : componentAt3 (𝓞 ℚ) ℚ v gTwo = g₂ := by
    rw [hgTwoS v hv]
    simp [hTwo, hv]
  have hgOne_w : ∀ w (hw : w ∈ S) (hwv : w ≠ v), componentAt3 (𝓞 ℚ) ℚ w gOne = g₁ w hw hwv := by
    intro w hw hwv
    rw [hgOneS w hw]
    simp [hOne, hw, hwv]
  have hgTwo_w : ∀ w (hw : w ∈ S) (hwv : w ≠ v), componentAt3 (𝓞 ℚ) ℚ w gTwo = g₁ w hw hwv := by
    intro w hw hwv
    rw [hgTwoS w hw]
    simp [hTwo, hw, hwv]
  have hτ₂off : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt (τ₁ * σ) p := fun p hp =>
    isUnramifiedCharAt_mul ℚ τ₁ σ p (hτ₁off p hp) (hσS p hp)
  have hτ₂arch : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ (τ₁ * σ) w 0 0 := fun w hw =>
    hτσ ▸ isArchCompAt_mul_of_zero_zero τ₀ σd w (hτ₀arch w hw) (hσdarch w hw)
  obtain ⟨Λ₁, Λd₁, σΛ₁, hΛ₁d, hΛd₁d, hΛ₁, hΛd₁, hconv₁, hcond₁, hfe₁⟩ :=
    lfun_relations_at_twist_type K μ _hμ _hns uR aR uC kC hcR hcC τ₁ hτ₁adm eβ hτ₁arch
  obtain ⟨Λ₂, Λd₂, σΛ₂, hΛ₂d, hΛd₂d, hΛ₂, hΛd₂, hconv₂, hcond₂, hfe₂⟩ :=
    lfun_relations_at_twist K μ _hμ _hns uR aR uC kC hcR hcC (τ₁ * σ) hτ₂adm hτ₂arch
  have hgOneK : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
      componentAt3 (𝓞 ℚ) ℚ w gOne ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := fun w hw => by
    rw [hgOneOff w hw]
    exact one_mem _
  have hgTwoK : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
      componentAt3 (𝓞 ℚ) ℚ w gTwo ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := fun w hw => by
    rw [hgTwoOff w hw]
    exact one_mem _
  obtain ⟨cS, hcS, hnat⟩ := right_identity_at_twist_at_point_archTwisted K _hdeg ψ _hψ μ _hμ _hlev D U gen X hX hcont
    hW hW' hcontW hcontW' hexp S hSbad v hv hS hS' E hE ν_mul
  obtain ⟨cSd, hcSd, hdualId⟩ := left_identity_at_twist_at_point_archTwisted K _hdeg ψ _hψ μ _hμ _hlev D U gen X hX
    hcont hW hW' hcontW hcontW' hexp S hSbad v hv hS hS' E hE ν_mul
  obtain ⟨L₁, σL₁, hnat₁⟩ := hnat gOne hgOneK τ₁ hτ₁adm hτ₁off
  obtain ⟨L₂, σL₂, hnat₂⟩ := hnat gTwo hgTwoK (τ₁ * σ) hτ₂adm hτ₂off
  obtain ⟨σLd₁, hdual₁⟩ := hdualId gOne hgOneK τ₁ hτ₁adm hτ₁off
  obtain ⟨σLd₂, hdual₂⟩ := hdualId gTwo hgTwoK (τ₁ * σ) hτ₂adm hτ₂off
  have hblk₁' := fun w (hw : w ∈ S) (hwv : w ≠ v) => hblk₁ w hw hwv (g₁ w hw hwv)
  choose P₁ hP₁ using hblk₁'
  have hpd₁ := fun w (hw : w ∈ S) (hwv : w ≠ v) =>
    place_dual_data_of_localFE K ψ μ D U gen X hX w (localChar τ₁ w) (n₁ w hw hwv) (uF w hw) (g₁ w hw hwv) (P₁ w hw hwv)
      (σB w hw hwv) (hP₁ w hw hwv).1 (hP₁ w hw hwv).2.2.2.2
  have hram₁ : ∀ w ∈ S, w ≠ v → ∀ 𝔓 ∈ primeFibre ℚ K w,
      ¬ IsUnramifiedCharAt (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 :=
    fun w hw hwv =>
      (hcHW w hw τ₁ (n₁ w hw hwv) ((hdHW w hw).trans (hn₁ge w hw hwv)) (hn₁exp w hw hwv)).1
  have hne₁ := fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
    eval_cpow_ne_zero_of_ne_zero
      ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).euler 𝔓)
      (heckeDatum_euler_ne_zero K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC 𝔓)
      ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℝ)
      (by
        exact_mod_cast one_lt_heckeDatum_norm K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC 𝔓)
  obtain ⟨σe₁, hσe₁⟩ := exists_forall_mem_ne_zero_of_finite (primeFibre ℚ K v) (hfin v)
    (fun 𝔓 s => ((LanglandsTunnell.HeckeTate.heckeDatum K
      (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).euler 𝔓).eval
      (((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℂ) ^ (-s)))
    (fun 𝔓 _ => by
      obtain ⟨σ, hσ⟩ := hne₁ 𝔓
      exact ⟨σ, fun s hs => by simpa [Complex.ofReal_natCast] using hσ s hs⟩)
  have hfib₁ : ∀ s : ℂ, σe₁ < s.re →
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).euler 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℂ) ^
          (-s)))⁻¹) *
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).euler 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℂ) ^
          (-s))) = 1 :=
    fun s hs =>
      finprod_mem_inv_mul_finprod_mem_eq_one (primeFibre ℚ K v) (hfin v) _ (fun 𝔓 h𝔓 => hσe₁ s hs 𝔓 h𝔓)
  let Pw₁ : HeightOneSpectrum (𝓞 ℚ) → ℂ → ℂ := fun w =>
    if h : w ∈ S.erase v then P₁ w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1 else fun _ => 0
  let σw₁ : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun w =>
    if h : w ∈ S.erase v then σA w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1 else 0
  have hheld₁ : ∀ w ∈ S.erase v, ∀ s : ℂ, σw₁ w < s.re →
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
       localZeta30 w
          (Measure.comap Units.val
            (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
          (X.whittakerLoc w) (localChar τ₁ w) s (componentAt3 (𝓞 ℚ) ℚ w gOne))
        = Pw₁ w s := by
    intro w hw s hs
    have hw' : w ∈ S := (Finset.mem_erase.mp hw).2
    have hwv' : w ≠ v := (Finset.mem_erase.mp hw).1
    simp only [Pw₁, σw₁, dif_pos hw] at hs ⊢
    rw [hgOne_w w hw' hwv']
    exact (hP₁ w hw' hwv').2.2.1 s hs
  have hS4 :=
    LanglandsTunnell.CubicInduction.exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn K
      _hdeg ψ _hψ μ _hμ _hlev _hns D U gen _ X hX hcont hW hW' hcontW hcontW' c hc
  obtain ⟨E₁, hE₁, hB₁, σE₁, σE₁', hE₁Z, hE₁Zd⟩ := hS4 gOne τ₁ hτ₁adm
  obtain ⟨E₂, hE₂, hB₂, σE₂, σE₂', hE₂Z, hE₂Zd⟩ := hS4 gTwo (τ₁ * σ) hτ₂adm
  obtain ⟨σI₁, hI₁⟩ := instance_right_line' K _hdeg ψ _hψ μ _hμ _hlev D U gen X hX hcont hW hW' hcontW hcontW' hexp S
    hSbad v hv hS ν_mul gOne hgOneK uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC τ₁ hτ₁off hfin hram₁ hconv₁ cS
    (fun s : ℂ => archZeta30 ν_mul (fun h => X.whittakerArch (h * archComponent3 (𝓞 ℚ) ℚ gOne)) (τ₁.comp E) s 1)
    L₁ σL₁ hnat₁ E₁ σE₁ hE₁Z Λ₁ σΛ₁ hΛ₁ _ 0 (fun s _ => rfl) Pw₁ σw₁ hheld₁ _ σe₁ hfib₁
  have hτ₂exp : ∀ w (hw : w ∈ S) (hwv : w ≠ v),
      HasConductorExponentAt ℚ w (localChar (τ₁ * σ) w) (n₁ w hw hwv) := by
    intro w hw hwv
    have hmulc : localChar (τ₁ * σ) w = localChar τ₁ w * localChar σ w := MonoidHom.mul_comp τ₁ σ _
    rw [hmulc]
    exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt ℚ w _ _
      (n₁ w hw hwv) 0 (hn₁exp w hw hwv)
      (LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt ℚ σ w (hσheld w hw hwv))
      (by have := hdtwo w hw; have := hn₁ge w hw hwv; omega)
  have hram₂ : ∀ w ∈ S, w ≠ v → ∀ 𝔓 ∈ primeFibre ℚ K w,
      ¬ IsUnramifiedCharAt (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 :=
    fun w hw hwv =>
      (hcHW w hw (τ₁ * σ) (n₁ w hw hwv) ((hdHW w hw).trans (hn₁ge w hw hwv)) (hτ₂exp w hw hwv)).1
  have hne₂ := fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
    eval_cpow_ne_zero_of_ne_zero
      ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).euler 𝔓)
      (heckeDatum_euler_ne_zero K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC 𝔓)
      ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℝ)
      (by
        exact_mod_cast one_lt_heckeDatum_norm K
          (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC 𝔓)
  obtain ⟨σe₂, hσe₂⟩ := exists_forall_mem_ne_zero_of_finite (primeFibre ℚ K v) (hfin v)
    (fun 𝔓 s => ((LanglandsTunnell.HeckeTate.heckeDatum K
      (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).euler 𝔓).eval
      (((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
          uR aR uC kC).norm 𝔓 : ℂ) ^ (-s)))
    (fun 𝔓 _ => by
      obtain ⟨σ, hσ⟩ := hne₂ 𝔓
      exact ⟨σ, fun s hs => by simpa [Complex.ofReal_natCast] using hσ s hs⟩)
  have hfib₂ : ∀ s : ℂ, σe₂ < s.re →
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).euler 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℂ) ^
          (-s)))⁻¹) *
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).euler 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℂ) ^
          (-s))) = 1 :=
    fun s hs =>
      finprod_mem_inv_mul_finprod_mem_eq_one (primeFibre ℚ K v) (hfin v) _ (fun 𝔓 h𝔓 => hσe₂ s hs 𝔓 h𝔓)
  have hsub := fun w (hw : w ∈ S) (hwv : w ≠ v) =>
    exists_forall_apply_eq_modulus_cpow w (localChar σ w) (hσheld w hw hwv)
  choose s₀w hs₀w using hsub
  have hsh := fun w (hw : w ∈ S) (hwv : w ≠ v) =>
    localZeta30_unramifiedTwist_eq_shift w (localChar τ₁ w) (localChar σ w) (s₀w w hw hwv) (hs₀w w hw hwv)
  have hshifted := fun w (hw : w ∈ S) (hwv : w ≠ v) =>
    eq_comp_add_of_forall_eq_of_forall_eq _ _ (P₁ w hw hwv) (s₀w w hw hwv) (σA w hw hwv)
      (fun s => (hsh w hw hwv (X.whittakerLoc w) (g₁ w hw hwv) s).1) (hP₁ w hw hwv).2.2.1
  let Pw₂ : HeightOneSpectrum (𝓞 ℚ) → ℂ → ℂ := fun w s =>
    if h : w ∈ S.erase v then Pw₁ w (s + s₀w w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1) else 0
  let σw₂ : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun w =>
    if h : w ∈ S.erase v then σw₁ w - (s₀w w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1).re else 0
  have hheld₂ : ∀ w ∈ S.erase v, ∀ s : ℂ, σw₂ w < s.re →
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
       localZeta30 w
          (Measure.comap Units.val
            (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
          (X.whittakerLoc w) (localChar (τ₁ * σ) w) s (componentAt3 (𝓞 ℚ) ℚ w gTwo))
        = Pw₂ w s := by
    intro w hw s hs
    have hw' : w ∈ S := (Finset.mem_erase.mp hw).2
    have hwv' : w ≠ v := (Finset.mem_erase.mp hw).1
    simp only [Pw₂, σw₂, Pw₁, σw₁, dif_pos hw] at hs ⊢
    rw [hgTwo_w w hw' hwv', show localChar (τ₁ * σ) w = localChar τ₁ w * localChar σ w from MonoidHom.mul_comp τ₁ σ _]
    exact hshifted w hw' hwv' s hs
  obtain ⟨σI₂, hI₂⟩ := instance_right_line' K _hdeg ψ _hψ μ _hμ _hlev D U gen X hX hcont hW hW' hcontW hcontW' hexp S
    hSbad v hv hS ν_mul gTwo hgTwoK uR aR uC kC (τ₁ * σ) hτ₂off hfin hram₂ hconv₂ cS
    (fun s : ℂ => archZeta30 ν_mul (fun h => X.whittakerArch (h * archComponent3 (𝓞 ℚ) ℚ gTwo)) ((τ₁ * σ).comp E) s 1)
    L₂ σL₂ hnat₂ E₂ σE₂ hE₂Z Λ₂ σΛ₂ hΛ₂ _ 0 (fun s _ => rfl) Pw₂ σw₂ hheld₂ _ σe₂ hfib₂
  let γw₁ : HeightOneSpectrum (𝓞 ℚ) → ℂ → ℂ := fun w s =>
    if h : w ∈ S.erase v then
      ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real
          (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) : ℂ)⁻¹ *
        (((TateGlobal.localChar X.centralChar w (uF w (Finset.mem_erase.mp h).2) : ℂˣ) : ℂ) * (((localChar τ₁ w) (uF w (Finset.mem_erase.mp h).2) : ℂˣ) : ℂ) *
        (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w (TateGlobal.localChar X.centralChar w * (localChar τ₁ w)) *
        LanglandsTunnell.TateLocal.stdRootNumberAt ℚ w (localChar τ₁ w) ^ 2 * (Ideal.absNorm w.asIdeal : ℂ) ^ ((3 *
        ((n₁ w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1) : ℂ)) * (1 / 2 - s))))
    else 0
  let σwd₁ : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun w =>
    if h : w ∈ S.erase v then 1 - σB w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1 else 0
  have hheldd₁ : ∀ w ∈ S.erase v, ∀ s : ℂ, s.re < σwd₁ w →
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
       ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real
          (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) : ℂ)⁻¹ *
          localZetaDual31 w
            (Measure.comap Units.val
              (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
            (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)
            (X.whittakerLoc w) (localChar τ₁ w) (1 - s) (componentAt3 (𝓞 ℚ) ℚ w gOne))
        = γw₁ w s * Pw₁ w s := by
    intro w hw s hs
    have hw' : w ∈ S := (Finset.mem_erase.mp hw).2
    have hwv' : w ≠ v := (Finset.mem_erase.mp hw).1
    simp only [γw₁, σwd₁, Pw₁, dif_pos hw] at hs ⊢
    rw [hgOne_w w hw' hwv']
    exact (hpd₁ w hw' hwv').2.2 s hs
  let γw₂ : HeightOneSpectrum (𝓞 ℚ) → ℂ → ℂ := fun w s =>
    if h : w ∈ S.erase v then γw₁ w (s + s₀w w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1) else 0
  let σwd₂ : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun w =>
    if h : w ∈ S.erase v then σwd₁ w - (s₀w w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1).re else 0
  have hheldd₂ : ∀ w ∈ S.erase v, ∀ s : ℂ, s.re < σwd₂ w →
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
       ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real
          (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) : ℂ)⁻¹ *
          localZetaDual31 w
            (Measure.comap Units.val
              (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
            (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)
            (X.whittakerLoc w) (localChar (τ₁ * σ) w) (1 - s) (componentAt3 (𝓞 ℚ) ℚ w gTwo))
        = γw₂ w s * Pw₂ w s := by
    intro w hw s hs
    have hw' : w ∈ S := (Finset.mem_erase.mp hw).2
    have hwv' : w ≠ v := (Finset.mem_erase.mp hw).1
    simp only [γw₂, σwd₂, γw₁, σwd₁, Pw₂, Pw₁, dif_pos hw] at hs ⊢
    rw [hgTwo_w w hw' hwv', show localChar (τ₁ * σ) w = localChar τ₁ w * localChar σ w from MonoidHom.mul_comp τ₁ σ _,
      (hsh w hw' hwv' (X.whittakerLoc w) (g₁ w hw' hwv') s).2]
    exact (hpd₁ w hw' hwv').2.2 (s + s₀w w hw' hwv') (by rw [Complex.add_re]; linarith)
  have hned₁ := fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
    eval_cpow_ne_zero_of_ne_zero
      ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).dual 𝔓)
      (heckeDatum_dual_ne_zero K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC 𝔓)
      ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℝ)
      (by
        exact_mod_cast one_lt_heckeDatum_norm K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC 𝔓)
  obtain ⟨σed₁, hσed₁⟩ := exists_forall_mem_ne_zero_of_finite (primeFibre ℚ K v) (hfin v)
    (fun 𝔓 u => ((LanglandsTunnell.HeckeTate.heckeDatum K
      (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).dual 𝔓).eval
      (((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℂ) ^ (-u)))
    (fun 𝔓 _ => by
      obtain ⟨σ, hσ⟩ := hned₁ 𝔓
      exact ⟨σ, fun u hu => by simpa [Complex.ofReal_natCast] using hσ u hu⟩)
  have hfibd₁ : ∀ s : ℂ, s.re < 1 - σed₁ →
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).dual 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℂ) ^
          (-(1 - s))))⁻¹) *
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).dual 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℂ) ^
          (-(1 - s)))) = 1 :=
    fun s hs =>
      finprod_mem_inv_mul_finprod_mem_eq_one (primeFibre ℚ K v) (hfin v) _
        (fun 𝔓 h𝔓 => hσed₁ (1 - s) (by rw [Complex.sub_re, Complex.one_re]; linarith) 𝔓 h𝔓)
  have hned₂ := fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
    eval_cpow_ne_zero_of_ne_zero
      ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).dual 𝔓)
      (heckeDatum_dual_ne_zero K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC 𝔓)
      ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℝ)
      (by
        exact_mod_cast one_lt_heckeDatum_norm K
          (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC 𝔓)
  obtain ⟨σed₂, hσed₂⟩ := exists_forall_mem_ne_zero_of_finite (primeFibre ℚ K v) (hfin v)
    (fun 𝔓 u => ((LanglandsTunnell.HeckeTate.heckeDatum K
      (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).dual 𝔓).eval
      (((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
          uR aR uC kC).norm 𝔓 : ℂ) ^ (-u)))
    (fun 𝔓 _ => by
      obtain ⟨σ, hσ⟩ := hned₂ 𝔓
      exact ⟨σ, fun u hu => by simpa [Complex.ofReal_natCast] using hσ u hu⟩)
  have hfibd₂ : ∀ s : ℂ, s.re < 1 - σed₂ →
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, (((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).dual 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℂ) ^
          (-(1 - s))))⁻¹) *
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).dual 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℂ) ^
          (-(1 - s)))) = 1 :=
    fun s hs =>
      finprod_mem_inv_mul_finprod_mem_eq_one (primeFibre ℚ K v) (hfin v) _
        (fun 𝔓 h𝔓 => hσed₂ (1 - s) (by rw [Complex.sub_re, Complex.one_re]; linarith) 𝔓 h𝔓)
  let Ad₁ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ → ℂ := fun g' u =>
    archZeta30 ν_mul (fun h => ∫ y : mixedEmbedding.mixedSpace ℚ,
      dualWhittakerFn3 X.whittakerArch (h *
        lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g'))
      (τ₁⁻¹.comp E) u 1
  let Ad₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ → ℂ := fun g' u =>
    archZeta30 ν_mul (fun h => ∫ y : mixedEmbedding.mixedSpace ℚ,
      dualWhittakerFn3 X.whittakerArch (h *
        lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g'))
      ((τ₁ * σ)⁻¹.comp E) u 1
  obtain ⟨σJ₁, hJ₁⟩ := instance_left_line K _hdeg ψ _hψ μ _hμ _hlev D U gen X hX hcont hW hW' hcontW hcontW' hexp S
    hSbad v hv hS ν_mul gOne hgOneK uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC τ₁ hτ₁off hfin hram₁ hconv₁ c cSd Ad₁ σLd₁ hdual₁ E₁ σE₁' hE₁Zd
    Λd₁ σΛ₁ hΛd₁ _ 0 (fun s _ => rfl) Pw₁ γw₁ σwd₁ hheldd₁ _ (1 - σed₁) hfibd₁
  obtain ⟨σJ₂, hJ₂⟩ := instance_left_line K _hdeg ψ _hψ μ _hμ _hlev D U gen X hX hcont hW hW' hcontW hcontW' hexp S
    hSbad v hv hS ν_mul gTwo hgTwoK uR aR uC kC (τ₁ * σ) hτ₂off hfin hram₂ hconv₂ c cSd Ad₂ σLd₂ hdual₂ E₂ σE₂'
    hE₂Zd Λd₂ σΛ₂ hΛd₂ _ 0 (fun s _ => rfl) Pw₂ γw₂ σwd₂ hheldd₂ _ (1 - σed₂) hfibd₂
  obtain ⟨q₁', q₂, r₁', r₂, σq, σq', hq₁D, hq₂D, hr₁D, hr₂D, hZvq, hZvdq, hr₁f, hr₂f, hq₂f, hq₁f⟩ := hwall₁
  obtain ⟨P₂v, hP₂vsh, hP₂vc, hP₂vl, hP₂vcd, hP₂vdl⟩ := hblk₂ g₂
  obtain ⟨hP₂vD, hγ₂vD, hdual₂v⟩ :=
    place_dual_data_of_localFE K ψ μ D U gen X hX v (localChar σd v) a (uF v hv) g₂ P₂v σD hP₂vsh hP₂vdl
  let eOne : ℂ → ℂ :=
    (fun s : ℂ => ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).euler 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℂ) ^
          (-s)))
  let eTwo : ℂ → ℂ :=
    (fun s : ℂ => ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).euler 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℂ) ^
          (-s)))
  let ZvOne : ℂ → ℂ :=
    (fun s : ℂ =>
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
       localZeta30 v
          (Measure.comap Units.val
            (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
          (X.whittakerLoc v) (localChar τ₁ v) s (componentAt3 (𝓞 ℚ) ℚ v gOne)))
  let PvTwo : ℂ → ℂ := (fun s : ℂ => P₂v (s + s₀))
  let PwOne : ℂ → ℂ := (fun s : ℂ => ∏ w ∈ S.erase v, Pw₁ w s)
  let PwTwo : ℂ → ℂ := (fun s : ℂ => ∏ w ∈ S.erase v, Pw₂ w s)
  let A₁ : ℂ → ℂ := (fun s : ℂ => archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (τ₁.comp E) s 1)
  let A₂ : ℂ → ℂ := (fun s : ℂ => archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf₀)) ((τ₁ * σ).comp E) s 1)
  obtain ⟨σa, ha1⟩ :=
    archFactor_ne_zero_and_archFactorDual_ne_zero (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC)
  obtain ⟨σa₂, ha2⟩ :=
    archFactor_ne_zero_and_archFactorDual_ne_zero (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC)

  obtain ⟨Ph₁, hPh₁D, ⟨σP₁, -, hPh₁⟩, -, -, ⟨σPd₁, -, hPd₁⟩⟩ := hFEarch τ₁ hτ₁adm 0 eβ hτ₁arch gInf
  obtain ⟨Ph₂, hPh₂D, ⟨σP₂, -, hPh₂⟩, -, -, ⟨σPd₂, -, hPd₂⟩⟩ := hFEarch (τ₁ * σ) hτ₂adm 0 0 hτ₂arch gInf₀
  simp only [add_zero, Int.cast_zero] at hPh₁ hPd₁ hPh₂ hPd₂
  have hA₁P : ∀ s : ℂ, σP₁ < s.re →
      A₁ s = Ph₁ s * (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).archFactor s := by
    intro s hs
    simp only [A₁]
    rw [hArchEq]
    exact hPh₁ s hs
  have hA₂P : ∀ s : ℂ, σP₂ < s.re →
      A₂ s = Ph₂ s * (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactor s := by
    intro s hs
    simp only [A₂]
    rw [hArchEq]
    exact hPh₂ s hs
  have hPw₁D : Differentiable ℂ PwOne :=
    differentiable_fun_finset_prod (S.erase v) Pw₁ fun w hw => by
      simp only [Pw₁, dif_pos hw]
      exact (hpd₁ w (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1).1
  have hPw₂D : Differentiable ℂ PwTwo :=
    differentiable_fun_finset_prod (S.erase v) Pw₂ fun w hw => by
      simp only [Pw₂, Pw₁, dif_pos hw]
      exact (hpd₁ w (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1).1.comp
        (differentiable_id.add_const _)
  have he₁D : Differentiable ℂ
      eOne :=
    differentiable_fun_finprod_mem (primeFibre ℚ K v) (hfin v) _ fun 𝔓 _ =>
      differentiable_eval_cpow_neg _ _
        (Nat.cast_ne_zero.mpr (by
          have := one_lt_heckeDatum_norm K
            (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC 𝔓
          omega))
  have he₂D : Differentiable ℂ
      eTwo :=
    differentiable_fun_finprod_mem (primeFibre ℚ K v) (hfin v) _ fun 𝔓 _ =>
      differentiable_eval_cpow_neg _ _
        (Nat.cast_ne_zero.mpr (by
          have := one_lt_heckeDatum_norm K
            (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC 𝔓
          omega))
  have hPvD : Differentiable ℂ PvTwo := hP₂vD.comp (differentiable_id.add_const s₀)
  let σR : ℝ := max (max (max σI₁ σI₂) (max σq σa)) (max (max σa₂ (σC - s₀.re)) (max σP₁ σP₂))
  have hσI₁ : σI₁ ≤ σR := le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have hσI₂ : σI₂ ≤ σR := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hσq : σq ≤ σR := le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have hσaR : σa ≤ σR := le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  have hσa₂R : σa₂ ≤ σR := le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  have hσC : σC - s₀.re ≤ σR := le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have hσP₁ : σP₁ ≤ σR := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hσP₂ : σP₂ ≤ σR := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hR₁ : ∀ s : ℂ, σR < s.re →
      (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).archFactor s * E₁ s =
        ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) * cS *
          A₁ s *
          ZvOne s *
          PwOne s * Λ₁ s *
          eOne s := by
    intro s hs
    have h := hI₁ s (lt_of_le_of_lt hσI₁ hs)
    simp only [hgOneArch] at h
    exact h
  have hR₂ : ∀ s : ℂ, σR < s.re →
      (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactor s * E₂ s =
        ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) * cS *
          A₂ s * PvTwo s *
          PwTwo s * Λ₂ s *
          eTwo s := by
    intro s hs
    have h := hI₂ s (lt_of_le_of_lt hσI₂ hs)
    simp only [hgTwoArch] at h
    have hmulc := hmulcv
    have hsC : σC < (s + s₀).re := by
      rw [Complex.add_re]
      linarith [lt_of_le_of_lt hσC hs]
    rw [hgTwo_v, hmulc, (hshift₂ (X.whittakerLoc v) g₂ s).1, hP₂vl (s + s₀) hsC] at h
    exact h

  have hR₁' : ∀ s : ℂ, σR < s.re →
      (fun _ : ℂ => (1 : ℂ)) s * E₁ s =
        ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) * cS * (fun _ : ℂ => (1 : ℂ)) s *
          (fun s : ℂ => Ph₁ s * ZvOne s) s * PwOne s * Λ₁ s * eOne s := by
    intro s hs
    have h := hR₁ s hs
    have hAF := (ha1 s (lt_of_le_of_lt hσaR hs)).1
    rw [hA₁P s (lt_of_le_of_lt hσP₁ hs)] at h
    apply mul_left_cancel₀ hAF
    linear_combination h
  have hR₂' : ∀ s : ℂ, σR < s.re →
      (fun _ : ℂ => (1 : ℂ)) s * E₂ s =
        ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) * cS * (fun _ : ℂ => (1 : ℂ)) s *
          (fun s : ℂ => Ph₂ s * PvTwo s) s * PwTwo s * Λ₂ s * eTwo s := by
    intro s hs
    have h := hR₂ s hs
    have hAF := (ha2 s (lt_of_le_of_lt hσa₂R hs)).1
    rw [hA₂P s (lt_of_le_of_lt hσP₂ hs)] at h
    apply mul_left_cancel₀ hAF
    linear_combination h
  have hZv : ∀ s : ℂ, σR < s.re → ZvOne s * q₂ s = q₁' s := by
    intro s hs
    have h := hZvq s (lt_of_le_of_lt hσq hs)
    rw [← hτ₁v, ← hgOne_v] at h
    exact h
  have hZv' : ∀ s : ℂ, σR < s.re →
      (fun s : ℂ => Ph₁ s * ZvOne s) s * q₂ s = (fun s : ℂ => Ph₁ s * q₁' s) s := by
    intro s hs
    simp only
    rw [mul_assoc, hZv s hs]
  have hElimR := eliminate_right E₁ E₂ Λ₁ Λ₂
    eOne
    eTwo
    (fun s : ℂ => Ph₁ s * ZvOne s)
    (fun s : ℂ => Ph₂ s * PvTwo s) PwOne PwTwo
    (fun s : ℂ => Ph₁ s * q₁' s) q₂ (fun _ : ℂ => (1 : ℂ))
    (fun _ : ℂ => (1 : ℂ))
    (((NumberField.Idele.productMeasureData ℚ S).c : ℂ) * cS) σR hE₁ hE₂ hΛ₁d hΛ₂d he₁D he₂D (hPh₂D.mul hPvD) hPw₁D
    hPw₂D (hPh₁D.mul hq₁D) hq₂D (fun _ _ => one_ne_zero) hR₁' hR₂' hZv'
  let Cone : ℂ → ℂ :=
    (fun s : ℂ => LanglandsTunnell.HeckeTate.heckeRootNumber K
      (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) (fun w hw => aR w hw + (eβ : ZMod 2)) kC *
      ((LanglandsTunnell.HeckeTate.heckeConductor K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) : ℝ) : ℂ) ^
        ((1 / 2 : ℂ) - s))
  let Ctwo : ℂ → ℂ :=
    (fun s : ℂ => LanglandsTunnell.HeckeTate.heckeRootNumber K
      (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR kC *
      ((LanglandsTunnell.HeckeTate.heckeConductor K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) : ℝ) : ℂ) ^
        ((1 / 2 : ℂ) - s))
  let edOne : ℂ → ℂ :=
    (fun s : ℂ => ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).dual 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℂ) ^
          (-(1 - s))))
  let edTwo : ℂ → ℂ :=
    (fun s : ℂ => ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).dual 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℂ) ^
          (-(1 - s))))
  let ZdOne : ℂ → ℂ :=
    (fun u : ℂ =>
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
       ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
          localZetaDual31 v
            (Measure.comap Units.val
              (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
            (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)
            (X.whittakerLoc v) (localChar τ₁ v) u
            (componentAt3 (𝓞 ℚ) ℚ v gOne)))
  let gvTwo : ℂ → ℂ :=
    (fun s : ℂ =>
      ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
        (((TateGlobal.localChar X.centralChar v (uF v hv) : ℂˣ) : ℂ) * (((localChar σd v) (uF v hv) : ℂˣ) : ℂ) *
        (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (TateGlobal.localChar X.centralChar v * (localChar σd v)) *
        LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (localChar σd v) ^ 2 * (Ideal.absNorm v.asIdeal : ℂ) ^ ((3 *
        (a : ℂ)) * (1 / 2 - (s + s₀))))))
  let gwOne : ℂ → ℂ := (fun s : ℂ => ∏ w ∈ S.erase v, γw₁ w s)
  let gwTwo : ℂ → ℂ := (fun s : ℂ => ∏ w ∈ S.erase v, γw₂ w s)

  have ha1eq : aQ = -1 := eq_neg_one_of_inv_eq_psiQ ψ hψQ aQ psiInf hpsiInf hψinf
  have hν_add' : ν_add = MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume := by
    rw [hν_add, ha1eq]
    simp
  have habs1 : ∀ z : ℂ, ((|aQ| : ℝ) : ℂ) ^ z = 1 := fun z => by
    rw [ha1eq]
    simp
  let Ce₁ : ℂ := ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
      fun w => signEpsilon (aR w.1 w.2 + (eβ : ZMod 2))) *
    ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod fun w => Complex.I ^ (kC w.1 w.2).natAbs)
  let Ce₂ : ℂ := ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
      fun w => signEpsilon (aR w.1 w.2)) *
    ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod fun w => Complex.I ^ (kC w.1 w.2).natAbs)
  let Lam : ℂ := ∏ w : InfinitePlace K, lambdaArch K w
  let Ω₁ : ℂ := ((ω₃ (E aInf) : ℂˣ) : ℂ) * ((τ₁ (E aInf) : ℂˣ) : ℂ) ^ 3
  let Ω₂ : ℂ := ((ω₃ (E aInf) : ℂˣ) : ℂ) * (((τ₁ * σ) (E aInf) : ℂˣ) : ℂ) ^ 3
  have hAd₁ : ∀ s : ℂ, σPd₁ < (1 - s).re →
      Ad₁ (weylPrime3 * transposeInv3 gOne) (1 - s) =
        Ce₁ * Lam * Ω₁ * Ph₁ s *
          (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).archFactorDual (1 - s) := by
    intro s hs
    have hglue := LanglandsTunnell.CubicInduction.archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace
      ν_mul ν_add hν_add' Warch (τ₁.comp E) (1 - s) gInf
    simp only [Ad₁]
    rw [map_mul, archComponent3_weylPrime3, archComponent3_transposeInv3, hgOneArch, hArchEq,
      show τ₁⁻¹.comp E = (τ₁.comp E)⁻¹ from MonoidHom.ext fun _ => rfl, hglue, hPd₁ s hs, habs1]
    simp only [Ce₁, Lam, Ω₁]
    ring
  have hAd₂ : ∀ s : ℂ, σPd₂ < (1 - s).re →
      Ad₂ (weylPrime3 * transposeInv3 gTwo) (1 - s) =
        Ce₂ * Lam * Ω₂ * Ph₂ s *
          (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactorDual (1 - s) := by
    intro s hs
    have hglue := LanglandsTunnell.CubicInduction.archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace
      ν_mul ν_add hν_add' Warch ((τ₁ * σ).comp E) (1 - s) gInf₀
    simp only [Ad₂]
    rw [map_mul, archComponent3_weylPrime3, archComponent3_transposeInv3, hgTwoArch, hArchEq,
      show (τ₁ * σ)⁻¹.comp E = ((τ₁ * σ).comp E)⁻¹ from MonoidHom.ext fun _ => rfl, hglue, hPd₂ s hs, habs1]
    simp only [Ce₂, Lam, Ω₂]
    ring
  have hC₁D : Differentiable ℂ
      Cone :=
    (((differentiable_const _).sub differentiable_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hcond₁.ne'))).const_mul _
  have hC₂D : Differentiable ℂ
      Ctwo :=
    (((differentiable_const _).sub differentiable_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hcond₂.ne'))).const_mul _
  have hed₁D : Differentiable ℂ
      edOne :=
    differentiable_fun_finprod_mem (primeFibre ℚ K v) (hfin v) _ fun 𝔓 _ =>
      (differentiable_eval_cpow_neg _ _
        (Nat.cast_ne_zero.mpr (by
          have := one_lt_heckeDatum_norm K
            (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC 𝔓
          omega))).comp ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hed₂D : Differentiable ℂ
      edTwo :=
    differentiable_fun_finprod_mem (primeFibre ℚ K v) (hfin v) _ fun 𝔓 _ =>
      (differentiable_eval_cpow_neg _ _
        (Nat.cast_ne_zero.mpr (by
          have := one_lt_heckeDatum_norm K
            (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC 𝔓
          omega))).comp ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hγw₁D : Differentiable ℂ gwOne :=
    differentiable_fun_finset_prod (S.erase v) γw₁ fun w hw => by
      simp only [γw₁, dif_pos hw]
      exact (hpd₁ w (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1).2.1
  have hγw₂D : Differentiable ℂ gwTwo :=
    differentiable_fun_finset_prod (S.erase v) γw₂ fun w hw => by
      simp only [γw₂, γw₁, dif_pos hw]
      exact (hpd₁ w (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1).2.1.comp
        (differentiable_id.add_const _)
  have hγvD : Differentiable ℂ
      gvTwo :=
    hγ₂vD.comp (differentiable_id.add_const s₀)
  let σL : ℝ := min (min (min σJ₁ σJ₂) (min σq' (1 - σa))) (min (min (1 - σa₂) (1 - σD - s₀.re)) (min (1 - σPd₁) (1 - σPd₂)))
  have hσJ₁ : σL ≤ σJ₁ := min_le_of_left_le (min_le_of_left_le (min_le_left _ _))
  have hσJ₂ : σL ≤ σJ₂ := min_le_of_left_le (min_le_of_left_le (min_le_right _ _))
  have hσq' : σL ≤ σq' := min_le_of_left_le (min_le_of_right_le (min_le_left _ _))
  have hσa' : σL ≤ 1 - σa := min_le_of_left_le (min_le_of_right_le (min_le_right _ _))
  have hσa₂' : σL ≤ 1 - σa₂ := min_le_of_right_le (min_le_of_left_le (min_le_left _ _))
  have hσD' : σL ≤ 1 - σD - s₀.re := min_le_of_right_le (min_le_of_left_le (min_le_right _ _))
  have hσPd₁ : σL ≤ 1 - σPd₁ := min_le_of_right_le (min_le_of_right_le (min_le_left _ _))
  have hσPd₂ : σL ≤ 1 - σPd₂ := min_le_of_right_le (min_le_of_right_le (min_le_right _ _))
  have hL₁ : ∀ s : ℂ, s.re < σL →
      (LanglandsTunnell.HeckeTate.heckeDatum K μ uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).archFactorDual (1 - s) * E₁ s =
        (c * ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
      (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces ℚ / Real.sqrt |(NumberField.discr ℚ : ℝ)| : ℝ) :
        ℂ) * cSd) *
          Ad₁ (weylPrime3 * transposeInv3 gOne) (1 - s) * ZdOne (1 - s) *
          (gwOne s * PwOne s) * Λd₁ (1 - s) *
          edOne s := by
    intro s hs
    exact hJ₁ s (lt_of_lt_of_le hs hσJ₁)
  have hL₂ : ∀ s : ℂ, s.re < σL →
      (LanglandsTunnell.HeckeTate.heckeDatum K μ uR aR uC kC).archFactorDual (1 - s) * E₂ s =
        (c * ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
      (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces ℚ / Real.sqrt |(NumberField.discr ℚ : ℝ)| : ℝ) :
        ℂ) * cSd) *
          Ad₂ (weylPrime3 * transposeInv3 gTwo) (1 - s) *
          (gvTwo s * PvTwo s) *
          (gwTwo s * PwTwo s) * Λd₂ (1 - s) *
          edTwo s := by
    intro s hs
    have h := hJ₂ s (lt_of_lt_of_le hs hσJ₂)
    have hmulc := hmulcv
    have hsD : (s + s₀).re < 1 - σD := by
      rw [Complex.add_re]
      linarith [lt_of_lt_of_le hs hσD']
    rw [hgTwo_v, hmulc, (hshift₂ (X.whittakerLoc v) g₂ s).2, hdual₂v (s + s₀) hsD] at h
    exact h
  let Zd₁' : ℂ → ℂ := fun u => Ce₁ * Lam * Ω₁ * Ph₁ (1 - u) * ZdOne u
  have hL₁' : ∀ s : ℂ, s.re < σL →
      (fun _ : ℂ => (1 : ℂ)) (1 - s) * E₁ s = (c * ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
      (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces ℚ / Real.sqrt |(NumberField.discr ℚ : ℝ)| : ℝ) :
        ℂ) * cSd) * (fun _ : ℂ => (1 : ℂ)) (1 - s) * Zd₁' (1 - s) *
        (gwOne s * PwOne s) * Λd₁ (1 - s) * edOne s := by
    intro s hs
    have h := hL₁ s hs
    have hre : σPd₁ < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith [lt_of_lt_of_le hs hσPd₁]
    have hAF := (ha1 (1 - s) (by rw [Complex.sub_re, Complex.one_re]; linarith [lt_of_lt_of_le hs hσa'])).2
    rw [hAd₁ s hre] at h
    simp only [Zd₁', sub_sub_cancel]
    apply mul_left_cancel₀ hAF
    linear_combination h
  have hL₂' : ∀ s : ℂ, s.re < σL →
      (fun _ : ℂ => (1 : ℂ)) (1 - s) * E₂ s = (c * ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
      (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces ℚ / Real.sqrt |(NumberField.discr ℚ : ℝ)| : ℝ) :
        ℂ) * cSd) * (fun _ : ℂ => (1 : ℂ)) (1 - s) *
        ((fun s : ℂ => Ce₂ * Lam * Ω₂ * gvTwo s) s * (fun s : ℂ => Ph₂ s * PvTwo s) s) *
        (gwTwo s * PwTwo s) * Λd₂ (1 - s) * edTwo s := by
    intro s hs
    have h := hL₂ s hs
    have hre : σPd₂ < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith [lt_of_lt_of_le hs hσPd₂]
    have hAF := (ha2 (1 - s) (by rw [Complex.sub_re, Complex.one_re]; linarith [lt_of_lt_of_le hs hσa₂'])).2
    rw [hAd₂ s hre] at h
    apply mul_left_cancel₀ hAF
    linear_combination h
  have hZd : ∀ s : ℂ, s.re < σL → ZdOne (1 - s) * (q₂ s * r₂ s) = r₁' s * q₁' s := by
    intro s hs
    have h := hZvdq s (lt_of_lt_of_le hs hσq')
    rw [← hτ₁v, ← hgOne_v] at h
    exact h
  have hZd' : ∀ s : ℂ, s.re < σL →
      Zd₁' (1 - s) * (q₂ s * r₂ s) = (fun s : ℂ => Ce₁ * Lam * Ω₁ * r₁' s) s * (fun s : ℂ => Ph₁ s * q₁' s) s := by
    intro s hs
    have h := hZd s hs
    simp only [Zd₁', sub_sub_cancel]
    linear_combination (Ce₁ * Lam * Ω₁ * Ph₁ s) * h
  have hElimL := eliminate_left E₁ E₂ Λ₁ Λ₂ Λd₁ Λd₂
    Cone
    Ctwo
    eOne
    eTwo
    edOne
    edTwo
    Zd₁'
    (fun s : ℂ => Ce₂ * Lam * Ω₂ * gvTwo s)
    (fun s : ℂ => Ph₂ s * PvTwo s) gwOne gwTwo
    PwOne PwTwo (fun s : ℂ => Ce₁ * Lam * Ω₁ * r₁' s) (fun s : ℂ => Ph₁ s * q₁' s) q₂ r₂
    (fun _ : ℂ => (1 : ℂ))
    (fun _ : ℂ => (1 : ℂ))
    (c * ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
      (((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces ℚ / Real.sqrt |(NumberField.discr ℚ : ℝ)| : ℝ) :
        ℂ) * cSd)
    σL hE₁ hE₂ hΛ₁d hΛ₂d hC₁D hC₂D he₁D he₂D hed₁D hed₂D ((differentiable_const _).mul hγvD) (hPh₂D.mul hPvD) hγw₁D
    hγw₂D hPw₁D hPw₂D ((differentiable_const _).mul hr₁D) (hPh₁D.mul hq₁D) hq₂D hr₂D
    (fun _ _ => one_ne_zero) hL₁' hL₂' hfe₁ hfe₂ hZd'
  have hPw₁ne : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → PwOne s ≠ 0 :=
    exists_forall_finset_prod_ne_zero (S.erase v) Pw₁ fun w hw => by
      have hw' : w ∈ S := (Finset.mem_erase.mp hw).2
      have hwv' : w ≠ v := (Finset.mem_erase.mp hw).1
      obtain ⟨Q, m, hQm⟩ := (hP₁ w hw' hwv').1
      have hQ : Q ≠ 0 := fun hQ0 => by
        have h := hQm (s₁ w hw' hwv')
        rw [hQ0, Polynomial.eval_zero, zero_mul] at h
        exact hZ₁ w hw' hwv' (((hP₁ w hw' hwv').2.2.1 _ (hs₁ w hw' hwv')).trans h)
      obtain ⟨σ, hσ⟩ := exists_forall_eval_cpow_neg_mul_cpow_ne_zero Q hQ (Ideal.absNorm w.asIdeal)
        (NumberField.HeightOneSpectrum.one_lt_absNorm w) (m : ℂ)
      refine ⟨σ, fun s hs => ?_⟩
      simp only [Pw₁, dif_pos hw]
      rw [hQm s]
      exact hσ s hs
  have hPw₂ne : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → PwTwo s ≠ 0 :=
    exists_forall_finset_prod_ne_zero (S.erase v) Pw₂ fun w hw => by
      have hw' : w ∈ S := (Finset.mem_erase.mp hw).2
      have hwv' : w ≠ v := (Finset.mem_erase.mp hw).1
      obtain ⟨Q, m, hQm⟩ := (hP₁ w hw' hwv').1
      have hQ : Q ≠ 0 := fun hQ0 => by
        have h := hQm (s₁ w hw' hwv')
        rw [hQ0, Polynomial.eval_zero, zero_mul] at h
        exact hZ₁ w hw' hwv' (((hP₁ w hw' hwv').2.2.1 _ (hs₁ w hw' hwv')).trans h)
      obtain ⟨σ, hσ⟩ := exists_forall_eval_cpow_neg_add_mul_cpow_ne_zero Q hQ (Ideal.absNorm w.asIdeal)
        (NumberField.HeightOneSpectrum.one_lt_absNorm w) (m : ℂ)
        (s₀w w hw' hwv')
      refine ⟨σ, fun s hs => ?_⟩
      simp only [Pw₂, Pw₁, dif_pos hw]
      rw [hQm (s + s₀w w hw' hwv')]
      exact hσ s hs
  have hPvne : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → PvTwo s ≠ 0 := by
    obtain ⟨Q, m, hQm⟩ := hP₂vsh
    have hQ : Q ≠ 0 := fun hQ0 => by
      have h := hQm s₂
      rw [hQ0, Polynomial.eval_zero, zero_mul] at h
      exact hZ₂ ((hP₂vl s₂ hs₂).trans h)
    obtain ⟨σ, hσ⟩ := exists_forall_eval_cpow_neg_add_mul_cpow_ne_zero Q hQ (Ideal.absNorm v.asIdeal)
      (NumberField.HeightOneSpectrum.one_lt_absNorm v) (m : ℂ) s₀
    exact ⟨σ, fun s hs => by
      show P₂v (s + s₀) ≠ 0
      rw [hQm (s + s₀)]
      exact hσ s hs⟩
  have hq₂ne : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → q₂ s ≠ 0 := by
    obtain ⟨Q₂, hQ₂, hq₂⟩ := hq₂f
    obtain ⟨σ, hσ⟩ := exists_forall_eval_cpow_neg_add_ne_zero Q₂ hQ₂ (Ideal.absNorm v.asIdeal)
      (NumberField.HeightOneSpectrum.one_lt_absNorm v) sθ
    exact ⟨σ, fun s hs => by rw [hq₂ s]; exact hσ s hs⟩
  obtain ⟨σPw₁, hPw₁ne⟩ := hPw₁ne
  obtain ⟨σPw₂, hPw₂ne⟩ := hPw₂ne
  obtain ⟨σPv, hPvne⟩ := hPvne
  obtain ⟨σq2, hq₂ne⟩ := hq₂ne
  let σX : ℝ := max (max (max σR σq2) (max (σ₀v - sθ.re) σPv))
    (max (max σPw₁ σPw₂) (max (max σΛ₁ σΛ₂) (max σe₁ σe₂)))
  have hXR : σR ≤ σX := le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have hXq2 : σq2 ≤ σX := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hX0 : σ₀v - sθ.re ≤ σX := le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have hXPv : σPv ≤ σX := le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  have hXPw₁ : σPw₁ ≤ σX := le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  have hXPw₂ : σPw₂ ≤ σX := le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have hXΛ₁ : σΛ₁ ≤ σX := le_max_of_le_right (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
  have hXΛ₂ : σΛ₂ ≤ σX := le_max_of_le_right (le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))
  have hXe₁ : σe₁ ≤ σX := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hXe₂ : σe₂ ≤ σX := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

  have htar : tar.re = 0 :=
    re_eq_zero_of_isArchCompAt_of_isUnitaryChar ℚ σar hσaradm.2.2 Rat.infinitePlace tar ear (hσar _ Rat.isReal_infinitePlace)
  have ht₀ : t₀.re = 0 :=
    re_eq_zero_of_isArchCompAt_of_isUnitaryChar ℚ σ₀ar hσ₀adm.2.2 Rat.infinitePlace t₀ e₀ (hσ₀ar _ Rat.isReal_infinitePlace)
  have hpar' : (-1 : ℂ) ^ ear = (-1 : ℂ) ^ eβ := by rw [← hpar, heβ]
  have hP₁w : ∃ s₁ : ℂ, σX + 1 < s₁.re ∧ Ph₁ s₁ ≠ 0 := by
    obtain ⟨s, hs, hne⟩ := hnv (σX + 1)
    rw [archZeta30_comp_eq_archZeta30_comp_of_isArchCompAt E hE ν_mul _ σar τ₁ tar ear eβ hσar hτ₁arch hpar' s 1] at hne
    have hs' : σX + 1 < (s + tar).re := by rw [Complex.add_re, htar, add_zero]; exact hs
    refine ⟨s + tar, hs', fun h0 => hne ?_⟩
    have := hA₁P (s + tar) (lt_of_le_of_lt (hσP₁.trans hXR) (by linarith))
    simp only [A₁] at this
    rw [this, h0, zero_mul]
  have hP₂w : ∃ s₂ : ℂ, Ph₂ s₂ ≠ 0 := by
    obtain ⟨s, hs, hne⟩ := hnv₀ σX
    rw [archZeta30_comp_eq_archZeta30_one_of_isArchCompAt E hE ν_mul _ σ₀ar t₀ e₀ hσ₀ar he₀ s 1,
      ← archComp_eq_of_isArchCompAt_zero_zero E hE (τ₁ * σ) hτ₂adm hτ₂arch] at hne
    refine ⟨s + t₀, fun h0 => hne ?_⟩
    have := hA₂P (s + t₀) (lt_of_le_of_lt (hσP₂.trans hXR) (by rw [Complex.add_re, ht₀, add_zero]; exact hs))
    simp only [A₂] at this
    rw [this, h0, zero_mul]
  obtain ⟨s₁, hs₁, hP₁s₁⟩ := hP₁w
  obtain ⟨s₂, hP₂s₂⟩ := hP₂w
  have hev : ∀ᶠ z in nhds s₁, Ph₁ z ≠ 0 ∧ σX < z.re :=
    (hPh₁D.continuous.continuousAt.eventually_ne hP₁s₁).and
      ((Complex.continuous_re.tendsto s₁).eventually_const_lt (show σX < s₁.re by linarith))
  have hP₂nz : ¬ (∀ᶠ z in nhds s₁, Ph₂ z = 0) := fun h =>
    hP₂s₂ ((hPh₂D.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ s₁) h (Set.mem_univ s₂))
  obtain ⟨sA, ⟨hP₁A, hsA⟩, hP₂A⟩ := (hev.and_frequently (Filter.not_eventually.mp hP₂nz)).exists
  have he₁sA : (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).euler 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC).norm 𝔓 : ℂ) ^
          (-sA))) ≠ 0 := fun h0 => by
    have h := hfib₁ sA (lt_of_le_of_lt hXe₁ hsA)
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  have he₂sA : (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((LanglandsTunnell.HeckeTate.heckeDatum K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).euler 𝔓).eval
        (((LanglandsTunnell.HeckeTate.heckeDatum K
          (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) uR aR uC kC).norm 𝔓 : ℂ) ^
          (-sA))) ≠ 0 := fun h0 => by
    have h := hfib₂ sA (lt_of_le_of_lt hXe₂ hsA)
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  have hE₂sA : E₂ sA ≠ 0 := by
    have h := hR₂' sA (lt_of_le_of_lt hXR hsA)
    simp only [one_mul, mul_one] at h
    rw [h]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr (NumberField.Idele.productMeasureData ℚ S).c_pos.ne') hcS)
      (mul_ne_zero hP₂A (hPvne sA (lt_of_le_of_lt hXPv hsA)))) (hPw₂ne sA (lt_of_le_of_lt hXPw₂ hsA)))
      (hΛ₂ sA (lt_of_le_of_lt hXΛ₂ hsA)).1) he₂sA
  have hq₁sA : q₁' sA ≠ 0 := by
    rw [← hZvq sA (lt_of_le_of_lt hσq (lt_of_le_of_lt hXR hsA))]
    refine mul_ne_zero ?_ (hq₂ne sA (lt_of_le_of_lt hXq2 hsA))
    rw [(hshift₁ (X.whittakerLoc v) g₀ sA).1]
    exact hne₀ (sA + sθ) (by rw [Complex.add_re]; linarith [lt_of_le_of_lt hX0 hsA])
  have hXsA : E₂ sA * (fun s : ℂ => Ph₁ s * q₁' s) sA * PwOne sA * Λ₁ sA *
      eOne sA ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hE₂sA (mul_ne_zero hP₁A hq₁sA))
      (hPw₁ne sA (lt_of_le_of_lt hXPw₁ hsA))) (hΛ₁ sA (lt_of_le_of_lt hXΛ₁ hsA)).1) he₁sA
  let Xf : ℂ → ℂ := fun s =>
    E₂ s * (fun s : ℂ => Ph₁ s * q₁' s) s * PwOne s * Λ₁ s *
          eOne s
  let αf : ℂ → ℂ := fun s =>
    (fun s : ℂ => Ce₂ * Lam * Ω₂ * gvTwo s) s *
          gwTwo s *
          edTwo s *
          r₂ s *
          Cone s *
          eOne s
  let βf : ℂ → ℂ := fun s =>
    (fun s : ℂ => Ce₁ * Lam * Ω₁ * r₁' s) s * gwOne s *
          edOne s *
          Ctwo s *
          eTwo s
  have hXD : Differentiable ℂ Xf := ((((hE₂.mul (hPh₁D.mul hq₁D)).mul hPw₁D).mul hΛ₁d).mul he₁D)
  have hαD : Differentiable ℂ αf :=
    (((((((differentiable_const _).mul hγvD)).mul hγw₂D).mul hed₂D).mul hr₂D).mul hC₁D).mul he₁D
  have hβD : Differentiable ℂ βf := (((((differentiable_const _).mul hr₁D).mul hγw₁D).mul hed₁D).mul hC₂D).mul he₂D
  have hXα : ∀ s : ℂ, Xf s * αf s = Xf s * βf s := fun s =>
    ((congrArg (fun t => t * αf s) (hElimR s)).symm.trans (hElimL s))
  have hbr : ∀ s : ℂ, αf s = βf s :=
    eq_of_mul_eq_mul_of_exists_ne_zero Xf αf βf hXD hαD hβD hXα ⟨sA, hXsA⟩

  have hcommN : ∀ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ =
        μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm := fun χ =>
    MonoidHom.ext fun x => by rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_comm]

  have hτ₁c : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar τ₁ v) cη := by
    rw [hτ₁v]
    exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero ℚ v _ _ cη hηc hθ0
  have hpin₁ := LanglandsTunnell.Converse.pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
    K μ v bη hdepth τ₁ cη hτ₁c hcb
  have hpinA := LanglandsTunnell.Converse.pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
    K μ v bη hdepth ηA cη (by rw [hηAv]; exact hηc) hcb
  have hν₁adm := isAdmissibleTwist_mul_comp_idelicNorm_of_isAdmissibleTwist K μ _hμ τ₁ hτ₁adm
  have hν₁ram : ∀ 𝔓 ∈ primeFibre ℚ K v,
      ¬ IsUnramifiedCharAt (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 := by
    intro 𝔓 h𝔓 hunr
    have h0 := LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K 𝔓
      (LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt K _ 𝔓 hunr)
    have hp := hpin₁ 𝔓 h𝔓
    rw [hcommN τ₁] at hp
    unfold LanglandsTunnell.Converse.pinnedExp at hp
    rw [h0] at hp
    have hdep := hdepth 𝔓 h𝔓
    push_cast at hp
    omega
  have hν₂ram : ∀ 𝔓 ∈ primeFibre ℚ K v,
      ¬ IsUnramifiedCharAt (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 := by
    rw [hτσ]
    exact hν₀ram
  have h41 : ∀ s : ℂ, eOne s = 1 ∧ edOne s = 1 := fun s =>
    finprod_eval_euler_and_dual_heckeDatum_eq_one_of_forall_not_isUnramifiedCharAt _ uR (fun w hw => aR w hw + (eβ : ZMod 2)) uC kC _ _ _ hν₁ram
  have h42 : ∀ s : ℂ, eTwo s = 1 ∧ edTwo s = 1 := fun s =>
    finprod_eval_euler_and_dual_heckeDatum_eq_one_of_forall_not_isUnramifiedCharAt _ uR aR uC kC _ _ _ hν₂ram

  have hεA₁ : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      LanglandsTunnell.HeckeTate.heckeRootNumber K χ (fun w hw => aR w hw + (eβ : ZMod 2)) kC =
        Ce₁ * ∏ᶠ 𝔓 : HeightOneSpectrum (𝓞 K), LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓) :=
    fun _ => rfl
  have hεA₂ : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      LanglandsTunnell.HeckeTate.heckeRootNumber K χ aR kC =
        Ce₂ * ∏ᶠ 𝔓 : HeightOneSpectrum (𝓞 K), LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓 (localChar χ 𝔓) :=
    fun _ => rfl
  have hCe₂ : Ce₂ ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ => ?_)
      (Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ Complex.I_ne_zero)
    unfold signEpsilon
    split_ifs
    · exact one_ne_zero
    · exact Complex.I_ne_zero
  let εoff : ℂ := ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
    (localChar (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
  let ε₁ : ℂ := LanglandsTunnell.HeckeTate.heckeRootNumber K
    (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) (fun w hw => aR w hw + (eβ : ZMod 2)) kC
  let ε₂ : ℂ := LanglandsTunnell.HeckeTate.heckeRootNumber K
    (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) aR kC
  let Qr : ℂ → ℂ := fun s =>
    (((∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
        (LanglandsTunnell.Converse.pinnedExp K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)) *
      ∏ᶠ 𝔓 ∈ ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹'
      (↑S : Set (HeightOneSpectrum (𝓞 ℚ))))ᶜ, (Ideal.absNorm 𝔓.asIdeal : ℝ) ^
        (LanglandsTunnell.Converse.pinnedExp K
          (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) : ℝ) : ℂ) ^
      (1 / 2 - s)
  have hfin₁ := LanglandsTunnell.HeckeTate.finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero K _
    hν₁adm
  have hν₂adm := isAdmissibleTwist_mul_comp_idelicNorm_of_isAdmissibleTwist K μ _hμ (τ₁ * σ) hτ₂adm
  have hfin₂ := LanglandsTunnell.HeckeTate.finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero K _
    hν₂adm
  have hlevoff : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ S →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓) = 0 := fun 𝔓 h => by
    have hram : ¬ IsRamifiedIn K (𝔓.under (𝓞 ℚ)) := fun hr => h ((hSbad _).mp (Or.inl hr))
    have he' :=
      (ramificationIdx_eq_one_and_inertiaDeg_le_three_and_finsum_inertiaDeg_eq_three_of_not_isRamifiedIn K _hdeg _
        hram).1 ⟨𝔓, rfl⟩
    exact (LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one ℚ K _ ⟨𝔓, rfl⟩
      he').trans (LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat _)
  obtain ⟨hεoff', hQoff⟩ :=
    finprod_compl_stdRootNumberAt_mul_comp_eq_and_finprod_compl_absNorm_zpow_pinnedExp_mul_comp_eq K μ _hμ.2.2 τ₁
      (τ₁ * σ) hτ₁adm.2.2 hτ₂adm.2.2 S hSbad hτ₁off hτ₂off hlevoff
  have hagree : ∀ w ∈ S.erase v, ∀ 𝔓 ∈ primeFibre ℚ K w,
      LanglandsTunnell.Converse.pinnedExp K (μ * (τ₁ * σ).comp
        (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 =
        LanglandsTunnell.Converse.pinnedExp K (μ * τ₁.comp
          (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 := fun w hw 𝔓 h𝔓 => by
    have hwS : w ∈ S := (Finset.mem_erase.mp hw).2
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    exact ((hcHW w hwS τ₁ (n₁ w hwS hwv) ((hdHW w hwS).trans (hn₁ge w hwS hwv)) (hn₁exp w hwS hwv)).2 σ
      hτ₁adm.2.2 hσadm.2.2 (hσheld w hwS hwv)).1 𝔓 h𝔓
  have hL₁ : ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      LanglandsTunnell.Converse.pinnedExp K
        (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 = (ℓ : ℤ) := by
    rw [hℓ]
    exact finsum_mem_congr rfl fun 𝔓 h𝔓 => by rw [← hcommN τ₁, hpin₁ 𝔓 h𝔓, hpinA 𝔓 h𝔓]
  have hL₂ : ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      LanglandsTunnell.Converse.pinnedExp K
        (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 = ((3 * a : ℕ) : ℤ) := by
    rw [hτσ]
    exact hL₂₀
  have hNfib : ∀ 𝔓 ∈ primeFibre ℚ K v,
      (Ideal.absNorm 𝔓.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ v.asIdeal.inertiaDeg' 𝔓.asIdeal :=
    absNorm_eq_absNorm_pow_inertiaDeg_of_mem_primeFibre K v
  obtain ⟨hε₁', hε₂', hC₁', hC₂'⟩ :=
    heckeRootNumber_eq_and_mul_heckeConductor_cpow_eq_of_twists'' K μ τ₁ (τ₁ * σ) (fun w hw => aR w hw + (eβ : ZMod 2)) aR kC S v hv ℓ (3 * a) Ce₁ Ce₂
      hεA₁ hεA₂ hfin₁.1 hfin₁.2 hfin₂.1 hfin₂.2 (hfin v) hL₁ hL₂ hNfib hagree hεoff' hQoff

  have hmod : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      (LanglandsTunnell.TateLocal.modulus
          ((NumberField.AdelicLevel.uniformizerUnit ℚ w : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) : ℝ) =
        ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ := fun w => modulus_uniformizerUnit_rat w
  have hmodw : ∀ w (hw : w ∈ S) (hwv : w ≠ v),
      ((σ (uniformizerIdele ℚ w) : ℂˣ) : ℂ) = (Ideal.absNorm w.asIdeal : ℂ) ^ (-(s₀w w hw hwv)) :=
    fun w hw hwv => eq_natCast_cpow_neg_of_eq_ofReal_cpow_of_eq_inv _ _ _ _
      (hs₀w w hw hwv (NumberField.AdelicLevel.uniformizerUnit ℚ w)).2 (hmod w)
  have hNw0 : ∀ w : HeightOneSpectrum (𝓞 ℚ), (Ideal.absNorm w.asIdeal : ℂ) ≠ 0 := fun w =>
    Nat.cast_ne_zero.mpr (by have := NumberField.HeightOneSpectrum.one_lt_absNorm w; omega)
  let Shw : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun w =>
    if h : w ∈ S.erase v then
      ((σ (uniformizerIdele ℚ w) : ℂˣ) : ℂ) ^ (3 * n₁ w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1)
    else 1
  let Sh : ℂ := ∏ w ∈ S.erase v, Shw w
  have hγww : ∀ w ∈ S.erase v, ∀ s : ℂ, γw₂ w s = Shw w * γw₁ w s := by
    intro w hw s
    have hwS : w ∈ S := (Finset.mem_erase.mp hw).2
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    simp only [γw₂, γw₁, Shw, dif_pos hw]
    exact mul_cpow_shift_eq_pow_mul_of_eq_cpow_neg _ _ _ _ _ _ _ s (s₀w w hwS hwv) (hNw0 w) (n₁ w hwS hwv)
      (hmodw w hwS hwv)
  have hγw : ∀ s : ℂ, gwTwo s = Sh * gwOne s := by
    intro s
    simp only [gwTwo, gwOne, Sh]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w hw => hγww w hw s
  have hεhw : ∀ w ∈ S.erase v,
      ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
          (localChar (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
        Shw w * ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
          (localChar (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) := by
    intro w hw
    have hwS : w ∈ S := (Finset.mem_erase.mp hw).2
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    have h := ((hcHW w hwS τ₁ (n₁ w hwS hwv) ((hdHW w hwS).trans (hn₁ge w hwS hwv)) (hn₁exp w hwS hwv)).2 σ
      hτ₁adm.2.2 hσadm.2.2 (hσheld w hwS hwv)).2
    simp only [Shw, dif_pos hw]
    exact h
  let εhOne : ℂ := ∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
    (localChar (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
  let εhTwo : ℂ := ∏ w ∈ S.erase v, ∏ᶠ 𝔓 ∈ primeFibre ℚ K w, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
    (localChar (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
  have hεh : εhTwo = Sh * εhOne := by
    simp only [εhTwo, εhOne, Sh]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w hw => hεhw w hw

  let εvOne : ℂ := ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
    (localChar (μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
  let εvTwo : ℂ := ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
    (localChar (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
  let EvA : ℂ := ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
    (localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) 𝔓)
  have hνAadm : IsAdmissibleTwist K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) :=
    isAdmissibleTwist_mul' K _ _ hηAK _hμ
  have hνAexp : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), ∃ n : ℕ, HasConductorExponentAt K 𝔓
      (localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) 𝔓) n := fun 𝔓 =>
    LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K 𝔓 _ (continuous_localChar _ hνAadm.2.1 𝔓)
  choose aA haA using hνAexp
  have hθσ : (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) *
      θ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm =
      μ * τ₁.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm := by
    rw [hθdef]
    exact MonoidHom.ext fun x => by
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply]
      rw [mul_comm (ηA _) (μ x), mul_assoc, mul_left_comm (ηA _), mul_inv_cancel, mul_one]
  have hθadm : IsAdmissibleTwist ℚ θ := hθdef ▸ isAdmissibleTwist_mul _ _ hτ₁adm (isAdmissibleTwist_inv ηA hηAadm)
  have hP11v := finprod_primeFibre_stdRootNumberAt_localChar_mul_comp_idelicNorm_eq_zpow_finsum_mul K
    (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) θ
    hθadm.2.2 v (hfin v) hθv aA
    (fun 𝔓 _ => haA 𝔓) (fun 𝔓 _ => hνAadm.2.2 _) (fun 𝔓 _ => LanglandsTunnell.TateLocal.psiLocal_ne_one K 𝔓)
  rw [hθσ] at hP11v
  let T : ℂ := ((θ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) ^ (∑ᶠ 𝔓 ∈ primeFibre ℚ K v,
    (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      ((aA 𝔓 : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓)))
  have hεv₁ : εvOne = T * EvA := hP11v
  have hTL : (∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      ((aA 𝔓 : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓))) =
        (ℓ : ℤ) := by
    rw [hℓ]
    exact finsum_mem_congr rfl fun 𝔓 _ => by
      unfold LanglandsTunnell.Converse.pinnedExp
      rw [LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K 𝔓 (haA 𝔓)]
  have hmodθ : (((localChar θ v) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-sθ) :=
    eq_natCast_cpow_neg_of_eq_ofReal_cpow_of_eq_inv _ _ _ _ (hsθ (NumberField.AdelicLevel.uniformizerUnit ℚ v)).2
      (hmod v)
  let Qv₁ : ℂ → ℂ := fun s => (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))
  let Qv₂ : ℂ → ℂ := fun s => (Ideal.absNorm v.asIdeal : ℂ) ^ (((3 * a : ℕ) : ℂ) * (1 / 2 - s))
  let Qt : ℂ → ℂ := fun s => (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - (s + sθ)))
  have hT : T = ((Ideal.absNorm v.asIdeal : ℂ) ^ (-sθ)) ^ (ℓ : ℤ) := by
    have h2 : ((θ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) =
        (((localChar θ v) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) := rfl
    simp only [T]
    rw [hTL, h2, hmodθ]
  have hQ : ∀ s : ℂ, T * Qv₁ s = Qt s := by
    intro s
    simp only [Qv₁, Qt]
    rw [hT, ← Complex.cpow_int_mul, ← Complex.cpow_add _ _ (hNw0 v)]
    congr 1
    push_cast
    ring

  have hεvTwo₀' : εvTwo = ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
      (localChar (μ * (τ₀ * σd).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) := by
    simp only [εvTwo, hτσ]
  have hεvTwo : εvTwo ≠ 0 := hεvTwo₀' ▸ hεvTwo₀
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℂ, Λ = ((TateGlobal.localChar X.centralChar v (uF v hv) : ℂˣ) : ℂ) * (((localChar σd v) (uF v hv) : ℂˣ) : ℂ) *
      (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (TateGlobal.localChar X.centralChar v * (localChar σd v)) *
        LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (localChar σd v) ^ (2 : ℕ)) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 * (a : ℂ)) * s₀) *
      (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K 𝔓
        (localChar (μ * (τ₀ * σd).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓))⁻¹ := ⟨_, rfl⟩
  have hγv : ∀ s : ℂ, gvTwo s =
      (((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ * Λ) * εvTwo * Qv₂ s := by
    intro s
    simp only [gvTwo, Qv₂]
    rw [hΛdef, hεvTwo₀', show (3 * (a : ℂ)) * (1 / 2 - (s + s₀)) = ((3 * a : ℕ) : ℂ) * (1 / 2 - s) + (-(3 * (a : ℂ)) * s₀) by
      push_cast; ring, Complex.cpow_add _ _ hN0]
    field_simp
  have hε₁ : ε₁ = Ce₁ * εvOne * εhOne * εoff := hε₁'
  have hε₂ : ε₂ = Ce₂ * εvTwo * εhTwo * εoff := hε₂'
  have hC₁ : ∀ s : ℂ, Cone s = ε₁ * (Qv₁ s * Qr s) := hC₁'
  have hC₂ : ∀ s : ℂ, Ctwo s = ε₂ * (Qv₂ s * Qr s) := hC₂'
  have hγv' : ∀ s : ℂ, (fun s : ℂ => Ce₂ * Lam * Ω₂ * gvTwo s) s =
      (((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ * (Ce₂ * Lam * Ω₂) * Λ) * εvTwo * Qv₂ s := by
    intro s
    simp only
    rw [hγv s]
    ring
  have hstar : ∀ s : ℂ, (fun s : ℂ => Ce₂ * Lam * Ω₂ * gvTwo s) s * gwTwo s * Cone s =
      ((((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ * (Ce₂ * Lam * Ω₂) * Λ) * Ce₁ * Ce₂⁻¹) *
        EvA * Qt s * (gwOne s * Ctwo s) :=
    star_identity_of_local_collapses' (fun s : ℂ => Ce₂ * Lam * Ω₂ * gvTwo s) gwOne gwTwo Cone Ctwo Qv₁ Qv₂ Qr Qt
      (((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ * (Ce₂ * Lam * Ω₂) * Λ)
      EvA T Ce₁ Ce₂ εvOne εvTwo εhOne εhTwo εoff Sh ε₁ ε₂ hCe₂ hC₁ hC₂ hε₁ hε₂ hγw hεh hγv' hεv₁ hQ

  have hram : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ S →
      ¬ IsUnramifiedCharAt (μ * (τ₁ * σ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 :=
    fun 𝔓 h => by
      by_cases hv' : 𝔓.under (𝓞 ℚ) = v
      · exact hν₂ram 𝔓 hv'
      · exact hram₂ _ h hv' 𝔓 rfl
  have hC₂ne : ∀ s : ℂ, Ctwo s ≠ 0 := fun s =>
    (heckeRootNumber_ne_zero_and_mul_heckeConductor_cpow_ne_zero_of_isAdmissibleTwist K _ hν₂adm aR kC S hram
      hlevoff).2 s
  have hXne : ∀ s : ℂ, gwOne s * Ctwo s ≠ 0 := fun s =>
    mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun w hw => by
          have hwS : w ∈ S := (Finset.mem_erase.mp hw).2
          have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
          simp only [γw₁, dif_pos hw]
          simpa only [mul_assoc] using
            multiplier_ne_zero_of_hasConductorExponentAt_of_norm_eq_one w (TateGlobal.localChar X.centralChar w)
              (localChar τ₁ w) (n₁ w hwS hwv)
              (bω w hwS) (by have := hdtwo w hwS; have := hn₁ge w hwS hwv; omega) (hn₁exp w hwS hwv) (hτ₁adm.2.2 _)
              (hbω w hwS) ((hcent w hwS).1) (by have := hdbω w hwS; have := hn₁ge w hwS hwv; have := hdtwo w hwS; omega)
              (uF w hwS) ((3 * ((n₁ w hwS hwv : ℕ) : ℂ)) * (1 / 2 - s)))
      (hC₂ne s)
  have hU := unwind_of_bracket_identity (fun s : ℂ => Ce₂ * Lam * Ω₂ * gvTwo s) gwOne gwTwo Cone Ctwo eOne eTwo edOne
    edTwo (fun s : ℂ => Ce₁ * Lam * Ω₁ * r₁' s) r₂
    (fun s : ℂ => Ce₁ * Lam * Ω₁ * (((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
      (R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s))))
    (fun s : ℂ => R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))
    (fun _ : ℂ => (1 : ℂ)) (fun _ : ℂ => (1 : ℂ))
    Qt Qv₁
    ((((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ * (Ce₂ * Lam * Ω₂) * Λ) * Ce₁ * Ce₂⁻¹)
    EvA sθ hbr (fun s => (h42 s).1) (fun s => (h42 s).2) hstar hXne (fun s => by beta_reduce; rw [hr₁f s]) hr₂f
    (fun s => (h41 s).1) (fun s => (h41 s).2) (fun s => rfl)
  have hM : (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((NumberField.TateGlobal.localChar
      (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) 𝔓 (-1) : ℂˣ) : ℂ)) =
      ((η (-1) : ℂˣ) : ℂ) * ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((localChar μ 𝔓 (-1) : ℂˣ) : ℂ) := by
    rw [← hηAv]
    exact finprod_localChar_comp_idelicNorm_mul_apply_neg_one K _hdeg μ ηA v
  have hMv1 : (∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((localChar μ 𝔓 (-1) : ℂˣ) : ℂ))⁻¹ *
      ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((localChar μ 𝔓 (-1) : ℂˣ) : ℂ) = 1 := inv_mul_cancel₀ hMv

  have hη2 : η (-1) * η (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have haInf1 : ((aInf : InfiniteAdeleRing ℚ) Rat.infinitePlace) = -1 := by
    rw [haInf, ha1eq, map_neg, map_one]
    rfl
  have hβa : ((β (E aInf) : ℂˣ) : ℂ) = ((η (-1) : ℂˣ) : ℂ) := by
    rw [LanglandsTunnell.CubicInduction.apply_of_infPart_eq_of_isArchCompAt β E hE 0 eβ hβarch' aInf Rat.infinitePlace
      Rat.isReal_infinitePlace, haInf1, map_neg, map_one, norm_neg, norm_one, mul_zero, Complex.cpow_zero, one_mul,
      Complex.ofReal_one, div_one, ← heβ]
  have hσa3 : (((τ₁ * σ) (E aInf) : ℂˣ) : ℂ) = ((τ₁ (E aInf) : ℂˣ) : ℂ) * ((η (-1) : ℂˣ) : ℂ) := by
    have hσd1 : σd (E aInf) = 1 := by
      have := archComp_eq_of_isArchCompAt_zero_zero E hE σd hσdadm hσdarch
      exact (DFunLike.congr_fun this aInf).trans rfl
    have hβinv : ((β⁻¹ (E aInf) : ℂˣ) : ℂ) = ((η (-1) : ℂˣ) : ℂ) := by
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hβa, ← Units.val_inv_eq_inv_val]
      congr 1
      rw [inv_eq_iff_mul_eq_one, hη2]
    rw [MonoidHom.mul_apply, hσdef, MonoidHom.mul_apply, hσd1, mul_one, Units.val_mul, hβinv]
  have hΩ : Ω₂ = ((η (-1) : ℂˣ) : ℂ) * Ω₁ := by
    have hη3 : ((η (-1) : ℂˣ) : ℂ) ^ 3 = ((η (-1) : ℂˣ) : ℂ) := by
      rw [pow_succ, ← Units.val_pow_eq_pow_val, sq, hη2, Units.val_one, one_mul]
    simp only [Ω₂, Ω₁]
    rw [hσa3, mul_pow, hη3]
    ring
  have hΩ₁ : Ω₁ ≠ 0 := mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _))
  have hLam : Lam ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
    unfold lambdaArch signEpsilon
    split_ifs
    · exact one_ne_zero
    · exact one_ne_zero
    · exact Complex.I_ne_zero
  have hCe₁ : Ce₁ ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ => ?_)
      (Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ Complex.I_ne_zero)
    unfold signEpsilon
    split_ifs
    · exact one_ne_zero
    · exact Complex.I_ne_zero
  have hCe₂inv : Ce₂ * Ce₂⁻¹ = 1 := mul_inv_cancel₀ hCe₂
  intro s
  have h := hU s
  beta_reduce at h
  have h3 : Ω₁ * (R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) =
      Ω₂ * Λ * EvA * Qv₁ s * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hCe₁ hLam) (inv_ne_zero hvol))
    linear_combination h + (Ce₁ * Lam * (((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹) * Ω₂ * Λ * EvA * Qv₁ s *
        R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) * hCe₂inv
  have h4 : R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) =
      ((η (-1) : ℂˣ) : ℂ) * Λ * EvA * Qv₁ s * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
    apply mul_left_cancel₀ hΩ₁
    rw [hΩ] at h3
    linear_combination h3
  rw [hM, ← hΛdef]
  simp only [Qv₁] at h4
  linear_combination h4 - (((η (-1) : ℂˣ) : ℂ) * Λ * EvA * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) *
    R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) * hMv1

open NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion LanglandsTunnell.CubicLambda
open LanglandsTunnell

set_option maxHeartbeats 3200000 in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

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
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (c : ℂ) (hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (hbad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
        X.whittakerLoc v ∈ gl3CyclicSubspace W))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (h1 : ∀ w ∈ S, w ≠ v → X.whittakerLoc w 1 = 1)
    (hv1 : X.whittakerLoc v 1 = 1)
    (hadm : ∀ w ∈ S, ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
      ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
        (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hψw : ∀ w ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hS' : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hψv : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]

    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (ω₃ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω₃ : IsAdmissibleTwist ℚ ω₃ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω₃ p ∧ eulerCoeff ℚ ω₃ p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω₃ v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
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
                (((ω₃ (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0)
    (hArchEq : X.whittakerArch = Warch)
    :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ∀ (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (cη b : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η cη → cη ≤ b →
        (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v,
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
          NumberField.TateGlobal.localChar ηA v = η →
          LanglandsTunnell.Converse.IsAdmissibleTwist K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
        ∀ ℓ : ℕ, ((ℓ : ℤ) = ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) *
          LanglandsTunnell.Converse.pinnedExp K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) →

        (∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
          (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧
            ((η (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) ∧
          ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0) →
        ∀ (R₁ R₂ : Polynomial ℂ) (m : ℤ), R₁ ≠ 0 → R₂ ≠ 0 →
          (∀ g : LocalGL3 v,
            letI := localBorel ℚ v
            ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
              IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc
                v) η g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) η s g *
                  Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
                Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
              IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt
                ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                  (X.whittakerLoc v) η (1 - s) g *
                  (Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
                R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
                  (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s))) →
        ∀ s : ℂ,
          R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) =
            lam * ((∏ᶠ w ∈ primeFibre ℚ K v,
                ((NumberField.TateGlobal.localChar
                  (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
              ∏ᶠ w ∈ primeFibre ℚ K v,
                LanglandsTunnell.TateLocal.stdRootNumberAt K w
                  (NumberField.TateGlobal.localChar
                    (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  haveI := subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  have hSeq : ((S : Set (HeightOneSpectrum (𝓞 ℚ)))) = {v | IsBadPlace K μ v} :=
    Set.ext fun w => (Finset.mem_coe.trans (hSbad w).symm)
  have hX' : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      {v | IsBadPlace K μ v} X := hSeq ▸ hX

  have hlevAll : ∀ w : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0 := by
    intro w
    by_cases hb : IsBadPlace K μ w
    · exact hψw w ((hSbad w).mp hb)
    · exact _hlev w hb
  have h1S : ∀ w ∈ S, X.whittakerLoc w 1 = 1 := by
    intro w hw
    by_cases hwv : w = v
    · rw [hwv]; exact hv1
    · exact h1 w hw hwv
  have hne : X.whittakerArch ≠ 0 := by rw [hArchEq]; exact hWarch.1
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hWarch.1
  have hωE : ∀ z : (InfiniteAdeleRing ℚ)ˣ, ((ω₃ (E z) : ℂˣ) : ℂ) = ((X.centralChar (E z) : ℂˣ) : ℂ) := by
    intro z
    have h1 := hWarch.2.2.2.2.1 z g₀
    have h2 := LanglandsTunnell.CubicInduction.whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn K ψ μ
      (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) S X hX h1S E hE z g₀
    rw [hArchEq, h1] at h2
    exact mul_right_cancel₀ hg₀ h2
  have hωcond : ∀ w : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K w → ∃ a ≤ inducedLevelAt K μ w,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ w (localChar X.centralChar w) a := fun w hKw =>
    LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
      K _hdeg ψ μ _hμ (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) X hX' hcont hexp.1 w hKw
  have hatS : ∀ w ∈ S, X.whittakerLoc w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w), F ≠ 0 → X.whittakerLoc w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)) :=
    fun w hw => ⟨h1S w hw, (hbad S).2 w hw ((hSbad w).mpr hw), (hbad S).1 w hw ((hSbad w).mpr hw), hadm w hw⟩
  obtain ⟨hW0, hKf, hCG, hPsi, hCen, hFE, hNV⟩ := hWarch
  subst hArchEq
  have harch₀ := LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn K _hdeg
    ψ _hψ μ _hμ uR aR uC kC hcR hcC hlevAll _hns D U gen S hSbad X hX hcont hcontW hcontW' hW hW' hne hatS hcent hωcond E
    hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul
    ⟨hCG, hPsi, fun z g => by rw [hCen z g, hωE z], by simpa only [hωE] using hFE, hNV⟩
  exact solution_core_GEN K _hdeg ψ _hψ μ _hμ _hlev _hns D U gen X hX' hcont hW hW' hcontW hcontW' c hc hexp hbad
    S hSbad v hv h1 hadm hcent hψw hS hS' hψv E hE ν_mul uR aR uC kC hcR hcC hψQ ω₃ hω₃ a ha aInf haInf psiInf hpsiInf
    hψinf ν_add hν_add X.whittakerArch ⟨hW0, hKf, hCG, hPsi, hCen, hFE, hNV⟩ rfl harch₀

end S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one (solution)
