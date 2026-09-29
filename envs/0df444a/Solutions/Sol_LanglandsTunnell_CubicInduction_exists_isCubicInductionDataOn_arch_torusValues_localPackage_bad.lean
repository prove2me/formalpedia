-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/66adab03-0369-58a1-abe3-e9561ec13ba8

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_nonempty_automorphyDatum31_of_zeta_fe
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCuspidalAlong_form_of_tempered_of_entire_eulerTwists
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong
import Theorems.Thm_LanglandsTunnell_CubicInduction_summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_isCosetEigenfunction
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3
import Theorems.Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionData_dualWhittaker_eq_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_isGaugeMajorised3_of_eq_mul_prod
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rootSize_bound_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad
import Theorems.Thm_LanglandsTunnell_Converse_isArchCompAt_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_Converse_chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero
import Theorems.Thm_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det
import Theorems.Thm_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions Deep.NTSupply.instNormalRayClassSubgroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions FLT.SpectralSide.instCompactSpaceMatrix WhittakerBlock.sigmaCompactSpace_adelicGL3 ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ValuationSubring.lowerRamificationGroup_normal"
p2m_attr_erase "instance" "IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply"
p2m_attr_erase "simp" "AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right AutomorphicForm.cpowChar_apply_val AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WhittakerModel.archFnAt_zero AutomorphicForm.WhittakerModel.localFnAt_zero AutomorphicForm.mem_sigmaCentralizer_iff AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b MeasureTheory.L2.kernelIntegralLM_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot"
p2m_attr_erase "simp" "Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one ArtinL.Abelian.coeff_zero IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"
p2m_attr_erase "simp" "AutomorphicForm.gl3LFactorPoly_def AutomorphicForm.JPSSGL3Factored.mk.injEq AutomorphicForm.coeff_three_gl3LFactorPoly AutomorphicForm.coeff_one_gl3LFactorPoly AutomorphicForm.coeff_zero_gl3LFactorPoly AutomorphicForm.JPSSGL3Factored.mk.sizeOf_spec AutomorphicForm.JPSSConverseFactored.mk.sizeOf_spec AutomorphicForm.coeff_two_gl3LFactorPoly AutomorphicForm.JPSSConverseFactored.mk.injEq AutomorphicForm.coeff_zero_heckeLFactorPoly AutomorphicForm.coeff_two_heckeLFactorPoly AutomorphicForm.heckeLFactorPoly_def AutomorphicForm.HeckeEigensystem.localLFactor_def AutomorphicForm.coeff_one_heckeLFactorPoly AutomorphicForm.satakePow_two"

set_option autoImplicit false

section FilingScope

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.addCharLevel TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt signEpsilon LDatum LDatum.archFactor LDatum.archFactorDual RankinSelberg.primeFibre RankinSelberg.mem_primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3 CubicInduction.CubicInductionData CubicLambda.eulerCoeff CubicLambda.lambdaArch HeckeTate.heckeDatum TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.exists_hasConductorExponentAt_of_continuous CubicInduction.CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace CubicInduction.exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg CubicInduction.exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq CubicInduction.finite_setOf_isBadPlace_of_continuous CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod CubicInduction.exists_rootSize_bound_of_isGL3PsiWhittakerFn CubicInduction.hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong CubicInduction.hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane CubicInduction.continuous_isCuspidalAlong_isModerateGrowth3_dualForm RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange Converse.chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le CubicInduction.continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul CubicInduction.exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch CubicInduction.inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le CubicInduction.inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul CubicInduction.isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det CubicInduction.isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul CubicInduction.not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate_apply gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace HasWhittakerMultOne transposeInv3 whittaker3 IsCuspidalAlongP21 IsCuspidalAlongP12 inducedCoeff psiLoc IsKFinite dualForm AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe localMaximalCompact3 componentAt3 archComponent3 LocalGL3 varpi varpi_ne_zero cNormQ IsRightInvariant IsInducedSphericalAt IsRamifiedIn IsTwistRamifiedAbove IsBadPlace inducedLevelAt archPlaceComponent3 IsModerateGrowth3 congruenceK1 mem_localMaximalCompact3_of_mem_congruenceK1 HasSphericalTorusValuesAt lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 longWeyl3 dualWhittakerFn3 weylPrime3 CubicInductionData IsCubicInductionDataOn matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace nonempty_automorphyDatum31_of_zeta_fe isCuspidalAlong_form_of_tempered_of_entire_eulerTwists exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 hasWhittakerMultOne_of_isCosetEigenfunction exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3 exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3 CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq finite_setOf_isBadPlace_of_continuous continuous_and_isGaugeMajorised3_of_eq_mul_prod exists_rootSize_bound_of_isGL3PsiWhittakerFn hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane continuous_isCuspidalAlong_isModerateGrowth3_dualForm exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad det_upperUnipotent3 fnTwist3 twistedCentralChar3 continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists"
namespace MirabolicMajorantDual
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {L : Type*} [NormedField L]

private theorem det_ne_zero' (k : GL (Fin 3) L) : (k : Matrix (Fin 3) (Fin 3) L).det ≠ 0 := by
  have h : (k : Matrix (Fin 3) (Fin 3) L).det * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one h

private theorem det_inv' (k : GL (Fin 3) L) :
    ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = ((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]

private theorem inv_apply' (k : GL (Fin 3) L) (i j : Fin 3) :
    ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j =
      ((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹ * (k : Matrix (Fin 3) (Fin 3) L).adjugate i j := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']

private theorem dual_row_two (k : GL (Fin 3) L) (j : Fin 3) :
    ((longWeyl3 * transposeInv3 k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 j =
      ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) j 0 := by
  simp [longWeyl3, transposeInv3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem dual_row_one (k : GL (Fin 3) L) (j : Fin 3) :
    ((longWeyl3 * transposeInv3 k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 1 j =
      ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) j 1 := by
  simp [longWeyl3, transposeInv3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem dual_entry_20 (k : GL (Fin 3) L) :
    ((longWeyl3 * transposeInv3 k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 0 =
      ((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹ * bottomMinor k 1 2 := by
  rw [dual_row_two, inv_apply', Matrix.adjugate_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, bottomMinor]
  first | done | ring

private theorem dual_entry_21 (k : GL (Fin 3) L) :
    ((longWeyl3 * transposeInv3 k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 1 =
      ((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹ * -bottomMinor k 0 2 := by
  rw [dual_row_two, inv_apply', Matrix.adjugate_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, bottomMinor]
  first | done | ring

private theorem dual_entry_22 (k : GL (Fin 3) L) :
    ((longWeyl3 * transposeInv3 k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 2 =
      ((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹ * bottomMinor k 0 1 := by
  rw [dual_row_two, inv_apply', Matrix.adjugate_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, bottomMinor]
  first | done | ring

private theorem dual_minor_01 (k : GL (Fin 3) L) :
    bottomMinor (longWeyl3 * transposeInv3 k) 0 1 =
      ((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹ * -(k : Matrix (Fin 3) (Fin 3) L) 2 2 := by
  have hd := det_ne_zero' k
  simp only [bottomMinor, dual_row_one, dual_row_two, inv_apply', Matrix.adjugate_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp
  rw [Matrix.det_fin_three]
  ring

private theorem dual_minor_02 (k : GL (Fin 3) L) :
    bottomMinor (longWeyl3 * transposeInv3 k) 0 2 =
      ((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹ * (k : Matrix (Fin 3) (Fin 3) L) 2 1 := by
  have hd := det_ne_zero' k
  simp only [bottomMinor, dual_row_one, dual_row_two, inv_apply', Matrix.adjugate_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp
  rw [Matrix.det_fin_three]
  ring

private theorem dual_minor_12 (k : GL (Fin 3) L) :
    bottomMinor (longWeyl3 * transposeInv3 k) 1 2 =
      ((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹ * -(k : Matrix (Fin 3) (Fin 3) L) 2 0 := by
  have hd := det_ne_zero' k
  simp only [bottomMinor, dual_row_one, dual_row_two, inv_apply', Matrix.adjugate_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp
  rw [Matrix.det_fin_three]
  ring

private theorem max3_swap (a b c : ℝ) : max (max a b) c = max (max c b) a := by
  rw [max_comm a b, max_comm (max b a) c, max_assoc]

private theorem lastRowSup_dual (k : GL (Fin 3) L) :
    lastRowSup (longWeyl3 * transposeInv3 k) = ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖ * minorSup k := by
  simp only [lastRowSup, minorSup, dual_entry_20, dual_entry_21, dual_entry_22, norm_mul, norm_neg]
  rw [mul_max_of_nonneg _ _ (norm_nonneg _), mul_max_of_nonneg _ _ (norm_nonneg _), max3_swap]

private theorem minorSup_dual (k : GL (Fin 3) L) :
    minorSup (longWeyl3 * transposeInv3 k) = ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖ * lastRowSup k := by
  simp only [minorSup, lastRowSup, dual_minor_01, dual_minor_02, dual_minor_12, norm_mul, norm_neg]
  rw [mul_max_of_nonneg _ _ (norm_nonneg _), mul_max_of_nonneg _ _ (norm_nonneg _), max3_swap]

private theorem sqrt_scale (a x y z : ℝ) (ha : 0 ≤ a) :
    Real.sqrt ((a * x) ^ 2 + (a * y) ^ 2 + (a * z) ^ 2) = a * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
  rw [show (a * x) ^ 2 + (a * y) ^ 2 + (a * z) ^ 2 = a ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq ha]

private theorem lastRowEucl_dual (k : GL (Fin 3) L) :
    lastRowEucl (longWeyl3 * transposeInv3 k) = ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖ * minorEucl k := by
  simp only [lastRowEucl, minorEucl, dual_entry_20, dual_entry_21, dual_entry_22, norm_mul, norm_neg]
  rw [sqrt_scale _ _ _ _ (norm_nonneg _)]
  congr 1
  rw [show ‖bottomMinor k 1 2‖ ^ 2 + ‖bottomMinor k 0 2‖ ^ 2 + ‖bottomMinor k 0 1‖ ^ 2 =
    ‖bottomMinor k 0 1‖ ^ 2 + ‖bottomMinor k 0 2‖ ^ 2 + ‖bottomMinor k 1 2‖ ^ 2 by ring]

private theorem minorEucl_dual (k : GL (Fin 3) L) :
    minorEucl (longWeyl3 * transposeInv3 k) = ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖ * lastRowEucl k := by
  simp only [minorEucl, lastRowEucl, dual_minor_01, dual_minor_02, dual_minor_12, norm_mul, norm_neg]
  rw [sqrt_scale _ _ _ _ (norm_nonneg _)]
  congr 1
  rw [show ‖(k : Matrix (Fin 3) (Fin 3) L) 2 2‖ ^ 2 + ‖(k : Matrix (Fin 3) (Fin 3) L) 2 1‖ ^ 2 +
      ‖(k : Matrix (Fin 3) (Fin 3) L) 2 0‖ ^ 2 =
    ‖(k : Matrix (Fin 3) (Fin 3) L) 2 0‖ ^ 2 + ‖(k : Matrix (Fin 3) (Fin 3) L) 2 1‖ ^ 2 +
      ‖(k : Matrix (Fin 3) (Fin 3) L) 2 2‖ ^ 2 by ring]

private theorem det_longWeyl3 : ((longWeyl3 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = -1 := by
  simp [longWeyl3, Matrix.det_fin_three]

private theorem detSize_dual (k : GL (Fin 3) L) :
    detSize (longWeyl3 * transposeInv3 k) = ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖ := by
  unfold detSize
  rw [Units.val_mul, Matrix.det_mul, det_longWeyl3]
  change ‖-1 * (((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ).det‖ = _
  rw [Matrix.det_transpose, det_inv', neg_one_mul, norm_neg]

private theorem detSize_eq_inv_norm (k : GL (Fin 3) L) :
    detSize k = ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖⁻¹ := by
  rw [norm_inv, inv_inv]
  rfl

private theorem root₁_dual (k : GL (Fin 3) L) :
    detSize (longWeyl3 * transposeInv3 k) * lastRowSup (longWeyl3 * transposeInv3 k) /
        minorSup (longWeyl3 * transposeInv3 k) ^ 2 =
      minorSup k / lastRowSup k ^ 2 := by
  have he : ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (inv_ne_zero (det_ne_zero' k)))
  rw [detSize_dual, lastRowSup_dual, minorSup_dual, mul_pow, ← mul_assoc, ← sq, mul_div_mul_left _ _ he]

private theorem root₂_dual (k : GL (Fin 3) L) :
    minorSup (longWeyl3 * transposeInv3 k) / lastRowSup (longWeyl3 * transposeInv3 k) ^ 2 =
      detSize k * lastRowSup k / minorSup k ^ 2 := by
  have he0 : ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (inv_ne_zero (det_ne_zero' k))
  rw [minorSup_dual, lastRowSup_dual, detSize_eq_inv_norm, mul_pow]
  field_simp

private theorem archRoot₁_dual (k : GL (Fin 3) L) :
    detSize (longWeyl3 * transposeInv3 k) * lastRowEucl (longWeyl3 * transposeInv3 k) /
        minorEucl (longWeyl3 * transposeInv3 k) ^ 2 =
      minorEucl k / lastRowEucl k ^ 2 := by
  have he : ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (inv_ne_zero (det_ne_zero' k)))
  rw [detSize_dual, lastRowEucl_dual, minorEucl_dual, mul_pow, ← mul_assoc, ← sq, mul_div_mul_left _ _ he]

private theorem archRoot₂_dual (k : GL (Fin 3) L) :
    minorEucl (longWeyl3 * transposeInv3 k) / lastRowEucl (longWeyl3 * transposeInv3 k) ^ 2 =
      detSize k * lastRowEucl k / minorEucl k ^ 2 := by
  have he0 : ‖((k : Matrix (Fin 3) (Fin 3) L).det)⁻¹‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (inv_ne_zero (det_ne_zero' k))
  rw [minorEucl_dual, lastRowEucl_dual, detSize_eq_inv_norm, mul_pow]
  field_simp

end LanglandsTunnell.CubicInduction.MirabolicMajorantDual

end

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.addCharLevel TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt signEpsilon LDatum LDatum.archFactor LDatum.archFactorDual RankinSelberg.primeFibre RankinSelberg.mem_primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3 CubicInduction.CubicInductionData CubicLambda.eulerCoeff CubicLambda.lambdaArch HeckeTate.heckeDatum TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.exists_hasConductorExponentAt_of_continuous CubicInduction.CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace CubicInduction.exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg CubicInduction.exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq CubicInduction.finite_setOf_isBadPlace_of_continuous CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod CubicInduction.exists_rootSize_bound_of_isGL3PsiWhittakerFn CubicInduction.hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong CubicInduction.hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane CubicInduction.continuous_isCuspidalAlong_isModerateGrowth3_dualForm RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange Converse.chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le CubicInduction.continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul CubicInduction.exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch CubicInduction.inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le CubicInduction.inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul CubicInduction.isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det CubicInduction.isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul CubicInduction.not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate_apply gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace HasWhittakerMultOne transposeInv3 whittaker3 IsCuspidalAlongP21 IsCuspidalAlongP12 inducedCoeff psiLoc IsKFinite dualForm AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe localMaximalCompact3 componentAt3 archComponent3 LocalGL3 varpi varpi_ne_zero cNormQ IsRightInvariant IsInducedSphericalAt IsRamifiedIn IsTwistRamifiedAbove IsBadPlace inducedLevelAt archPlaceComponent3 IsModerateGrowth3 congruenceK1 mem_localMaximalCompact3_of_mem_congruenceK1 HasSphericalTorusValuesAt lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 longWeyl3 dualWhittakerFn3 weylPrime3 CubicInductionData IsCubicInductionDataOn matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace nonempty_automorphyDatum31_of_zeta_fe isCuspidalAlong_form_of_tempered_of_entire_eulerTwists exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 hasWhittakerMultOne_of_isCosetEigenfunction exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3 exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3 CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq finite_setOf_isBadPlace_of_continuous continuous_and_isGaugeMajorised3_of_eq_mul_prod exists_rootSize_bound_of_isGL3PsiWhittakerFn hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane continuous_isCuspidalAlong_isModerateGrowth3_dualForm exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad det_upperUnipotent3 fnTwist3 twistedCentralChar3 continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists"
namespace MirabolicMajorantDual
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {F : Type} [Field F] [NumberField F]

private theorem componentAt3_transposeInv3 (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) :
    componentAt3 (𝓞 F) F v (transposeInv3 g) = transposeInv3 (componentAt3 (𝓞 F) F v g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.finAdeleEval (𝓞 F) F v) (AdelicLevel.adeleFin (𝓞 F) F
      (((g⁻¹ : AdelicGL 3 (𝓞 F) F) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)) j i)) =
    (((componentAt3 (𝓞 F) F v g)⁻¹ : GL (Fin 3) (v.adicCompletion F)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) j i
  rw [← map_inv]
  rfl

private theorem archPlaceComponent3_transposeInv3 (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) :
    archPlaceComponent3 F w (transposeInv3 g) = transposeInv3 (archPlaceComponent3 F w g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.archEval F w) (AdelicLevel.adeleArch (𝓞 F) F
      (((g⁻¹ : AdelicGL 3 (𝓞 F) F) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)) j i)) =
    (((archPlaceComponent3 F w g)⁻¹ : GL (Fin 3) w.Completion) : Matrix (Fin 3) (Fin 3) w.Completion) j i
  rw [← map_inv]
  rfl

private theorem componentAt3_longWeyl3 (v : HeightOneSpectrum (𝓞 F)) :
    componentAt3 (𝓞 F) F v longWeyl3 = longWeyl3 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.finAdeleEval (𝓞 F) F v) (AdelicLevel.adeleFin (𝓞 F) F
      (((longWeyl3 : AdelicGL 3 (𝓞 F) F) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)) i j)) =
    ((longWeyl3 : GL (Fin 3) (v.adicCompletion F)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j
  fin_cases i <;> fin_cases j <;> simp [longWeyl3]

private theorem archPlaceComponent3_longWeyl3 (w : InfinitePlace F) :
    archPlaceComponent3 F w longWeyl3 = longWeyl3 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.archEval F w) (AdelicLevel.adeleArch (𝓞 F) F
      (((longWeyl3 : AdelicGL 3 (𝓞 F) F) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)) i j)) =
    ((longWeyl3 : GL (Fin 3) w.Completion) : Matrix (Fin 3) (Fin 3) w.Completion) i j
  fin_cases i <;> fin_cases j <;> simp [longWeyl3]

private theorem finRoot₁_dualArg (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) :
    finRoot₁ F v (longWeyl3 * transposeInv3 g) = finRoot₂ F v g := by
  unfold finRoot₁ finRoot₂
  rw [map_mul, componentAt3_longWeyl3, componentAt3_transposeInv3]
  exact root₁_dual _

private theorem finRoot₂_dualArg (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) :
    finRoot₂ F v (longWeyl3 * transposeInv3 g) = finRoot₁ F v g := by
  unfold finRoot₁ finRoot₂
  rw [map_mul, componentAt3_longWeyl3, componentAt3_transposeInv3]
  exact root₂_dual _

private theorem archRoot₁_dualArg (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) :
    archRoot₁ F w (longWeyl3 * transposeInv3 g) = archRoot₂ F w g := by
  unfold archRoot₁ archRoot₂
  rw [map_mul, archPlaceComponent3_longWeyl3, archPlaceComponent3_transposeInv3]
  exact archRoot₁_dual _

private theorem archRoot₂_dualArg (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) :
    archRoot₂ F w (longWeyl3 * transposeInv3 g) = archRoot₁ F w g := by
  unfold archRoot₁ archRoot₂
  rw [map_mul, archPlaceComponent3_longWeyl3, archPlaceComponent3_transposeInv3]
  exact archRoot₂_dual _

private theorem rootSizeProd_dualArg (g : AdelicGL 3 (𝓞 F) F) :
    rootSizeProd F (longWeyl3 * transposeInv3 g) = rootSizeProd F g := by
  unfold rootSizeProd
  congr 1
  · exact finprod_congr fun v => by rw [finRoot₁_dualArg, finRoot₂_dualArg, mul_comm]
  · exact Finset.prod_congr rfl fun w _ => by rw [archRoot₁_dualArg, archRoot₂_dualArg, mul_comm]

private theorem archRootSum_dualArg (g : AdelicGL 3 (𝓞 F) F) :
    archRootSum F (longWeyl3 * transposeInv3 g) = archRootSum F g := by
  unfold archRootSum
  exact Finset.sum_congr rfl fun w _ => by rw [archRoot₁_dualArg, archRoot₂_dualArg, add_comm]

private theorem inRootLevel_dualArg_iff (T : Finset (HeightOneSpectrum (𝓞 F))) (B : ℝ) (g : AdelicGL 3 (𝓞 F) F) :
    InRootLevel F T B (longWeyl3 * transposeInv3 g) ↔ InRootLevel F T B g := by
  unfold InRootLevel
  simp only [finRoot₁_dualArg, finRoot₂_dualArg]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun v hv => (h₁ v hv).symm, fun v hv => (h₂ v hv).symm⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun v hv => (h₁ v hv).symm, fun v hv => (h₂ v hv).symm⟩

private theorem isGaugeMajorised3_dual {W : AdelicGL 3 (𝓞 F) F → ℂ} (hW : IsGaugeMajorised3 F W) :
    IsGaugeMajorised3 F (dualWhittakerFn3 W) := by
  obtain ⟨t, T, B, hW⟩ := hW
  refine ⟨t, T, B, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hW N
  refine ⟨C, fun g => ?_⟩
  have h := hC (longWeyl3 * transposeInv3 g)
  rw [inRootLevel_dualArg_iff, rootSizeProd_dualArg, archRootSum_dualArg] at h
  exact h

end LanglandsTunnell.CubicInduction.MirabolicMajorantDual

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.addCharLevel TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt signEpsilon LDatum LDatum.archFactor LDatum.archFactorDual RankinSelberg.primeFibre RankinSelberg.mem_primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3 CubicInduction.CubicInductionData CubicLambda.eulerCoeff CubicLambda.lambdaArch HeckeTate.heckeDatum TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.exists_hasConductorExponentAt_of_continuous CubicInduction.CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace CubicInduction.exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg CubicInduction.exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq CubicInduction.finite_setOf_isBadPlace_of_continuous CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod CubicInduction.exists_rootSize_bound_of_isGL3PsiWhittakerFn CubicInduction.hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong CubicInduction.hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane CubicInduction.continuous_isCuspidalAlong_isModerateGrowth3_dualForm RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange Converse.chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le CubicInduction.continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul CubicInduction.exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch CubicInduction.inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le CubicInduction.inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul CubicInduction.isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det CubicInduction.isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul CubicInduction.not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate_apply gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace HasWhittakerMultOne transposeInv3 whittaker3 IsCuspidalAlongP21 IsCuspidalAlongP12 inducedCoeff psiLoc IsKFinite dualForm AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe localMaximalCompact3 componentAt3 archComponent3 LocalGL3 varpi varpi_ne_zero cNormQ IsRightInvariant IsInducedSphericalAt IsRamifiedIn IsTwistRamifiedAbove IsBadPlace inducedLevelAt archPlaceComponent3 IsModerateGrowth3 congruenceK1 mem_localMaximalCompact3_of_mem_congruenceK1 HasSphericalTorusValuesAt lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 longWeyl3 dualWhittakerFn3 weylPrime3 CubicInductionData IsCubicInductionDataOn matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace nonempty_automorphyDatum31_of_zeta_fe isCuspidalAlong_form_of_tempered_of_entire_eulerTwists exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 hasWhittakerMultOne_of_isCosetEigenfunction exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3 exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3 CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq finite_setOf_isBadPlace_of_continuous continuous_and_isGaugeMajorised3_of_eq_mul_prod exists_rootSize_bound_of_isGL3PsiWhittakerFn hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane continuous_isCuspidalAlong_isModerateGrowth3_dualForm exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad det_upperUnipotent3 fnTwist3 twistedCentralChar3 continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists"
namespace DualConjuncts
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Generic

variable {A : Type*} [CommRing A] [TopologicalSpace A]

private theorem continuous_transposeInv3 : Continuous (transposeInv3 : GL (Fin 3) A → GL (Fin 3) A) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 3) A => (((g⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 3) A => (((g : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ
    exact Units.continuous_val.matrix_transpose

variable [IsTopologicalRing A]

private theorem continuous_dualWhittakerFn3 {R : Type*} [TopologicalSpace R] {W : GL (Fin 3) A → R}
    (hW : Continuous W) : Continuous (dualWhittakerFn3 W) := by
  show Continuous fun g : GL (Fin 3) A => W (longWeyl3 * transposeInv3 g)
  exact hW.comp ((continuous_const_mul (longWeyl3 : GL (Fin 3) A)).comp continuous_transposeInv3)

end Generic

end LanglandsTunnell.CubicInduction.DualConjuncts

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.addCharLevel TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt signEpsilon LDatum LDatum.archFactor LDatum.archFactorDual RankinSelberg.primeFibre RankinSelberg.mem_primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3 CubicInduction.CubicInductionData CubicLambda.eulerCoeff CubicLambda.lambdaArch HeckeTate.heckeDatum TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.exists_hasConductorExponentAt_of_continuous CubicInduction.CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace CubicInduction.exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg CubicInduction.exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq CubicInduction.finite_setOf_isBadPlace_of_continuous CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod CubicInduction.exists_rootSize_bound_of_isGL3PsiWhittakerFn CubicInduction.hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong CubicInduction.hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane CubicInduction.continuous_isCuspidalAlong_isModerateGrowth3_dualForm RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange Converse.chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le CubicInduction.continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul CubicInduction.exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch CubicInduction.inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le CubicInduction.inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul CubicInduction.isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det CubicInduction.isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul CubicInduction.not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate_apply gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace HasWhittakerMultOne transposeInv3 whittaker3 IsCuspidalAlongP21 IsCuspidalAlongP12 inducedCoeff psiLoc IsKFinite dualForm AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe localMaximalCompact3 componentAt3 archComponent3 LocalGL3 varpi varpi_ne_zero cNormQ IsRightInvariant IsInducedSphericalAt IsRamifiedIn IsTwistRamifiedAbove IsBadPlace inducedLevelAt archPlaceComponent3 IsModerateGrowth3 congruenceK1 mem_localMaximalCompact3_of_mem_congruenceK1 HasSphericalTorusValuesAt lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 longWeyl3 dualWhittakerFn3 weylPrime3 CubicInductionData IsCubicInductionDataOn matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN localToAdelic3 exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace nonempty_automorphyDatum31_of_zeta_fe isCuspidalAlong_form_of_tempered_of_entire_eulerTwists exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 hasWhittakerMultOne_of_isCosetEigenfunction exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3 exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3 CubicInductionData.dualWhittaker_eq_dualWhittakerFn3 exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq finite_setOf_isBadPlace_of_continuous continuous_and_isGaugeMajorised3_of_eq_mul_prod exists_rootSize_bound_of_isGL3PsiWhittakerFn hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane continuous_isCuspidalAlong_isModerateGrowth3_dualForm exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad det_upperUnipotent3 fnTwist3 twistedCentralChar3 continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists"
namespace InductionExistence
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Points

private noncomputable def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

private theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, archMat3, AdelicLevel.adeleArch_apply]

private theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, archMat3, AdelicLevel.adeleFin_apply]

private theorem archMat3_one : archMat3 1 = 1 :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

private theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

private noncomputable def archEmbed3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun g :=
    { val := archMat3 g
      inv := archMat3 ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix _ _ _)
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

private theorem archComponent3_archEmbed3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archEmbed3 g) = g :=
  Units.ext (by
    show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) = g
    exact mapMatrix_arch_archMat3 _)

private theorem componentAt3_archEmbed3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ v (archEmbed3 g) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v) (AdelicLevel.adeleFin (𝓞 ℚ) ℚ
      (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)) =
    ((1 : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
  simp only [archMat3, Matrix.of_apply, AdelicLevel.adeleFin_apply, Units.val_one]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem componentAt3_localToAdelic3_self (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v h) = h := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v) (AdelicLevel.adeleFin (𝓞 ℚ) ℚ
      (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v
        (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) i j)) =
    (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
  simp only [finMatN, Matrix.of_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_self]

private theorem componentAt3_localToAdelic3_of_ne {u v : HeightOneSpectrum (𝓞 ℚ)} (huv : u ≠ v)
    (h : LocalGL3 v) : componentAt3 (𝓞 ℚ) ℚ u (localToAdelic3 v h) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ u) (AdelicLevel.adeleFin (𝓞 ℚ) ℚ
      (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v
        (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) i j)) =
    ((1 : GL (Fin 3) (u.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (u.adicCompletion ℚ)) i j
  simp only [finMatN, Matrix.of_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_of_ne (Fin 3) (𝓞 ℚ) ℚ v (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j huv,
    Units.val_one]

private theorem archComponent3_localToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v h) = 1 :=
  Units.ext (by
    show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v
          (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) = 1
    exact mapMatrix_arch_finMatN _ _ _ _)

private theorem exists_point (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (h : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v)
    (gA : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g = gA ∧ (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g = h v) ∧
      ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨archEmbed3 gA, archComponent3_archEmbed3 gA, fun v hv => by simp at hv,
      fun v _ => componentAt3_archEmbed3 v gA⟩
  | insert a S haS ih =>
    obtain ⟨g, hga, hgS, hgoff⟩ := ih
    refine ⟨g * localToAdelic3 a (h a), ?_, ?_, ?_⟩
    · rw [map_mul, hga, archComponent3_localToAdelic3, mul_one]
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hvS
      · rw [map_mul, hgoff _ haS, componentAt3_localToAdelic3_self, one_mul]
      · have hva : v ≠ a := fun e => haS (e ▸ hvS)
        rw [map_mul, hgS v hvS, componentAt3_localToAdelic3_of_ne hva, mul_one]
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, hgoff v hv.2, componentAt3_localToAdelic3_of_ne hv.1, mul_one]

end Points

section Rechoice

private theorem forall_mem_gl3CyclicSubspace_of_mem {F : Type*} [CommRing F] {R : Type*} [CommRing R]
    {W W' : GL (Fin 3) F → R} (hW : ∀ G ∈ gl3CyclicSubspace W, G ≠ 0 → W ∈ gl3CyclicSubspace G)
    (hmem : W' ∈ gl3CyclicSubspace W) :
    ∀ G ∈ gl3CyclicSubspace W', G ≠ 0 → W' ∈ gl3CyclicSubspace G := by
  have hle : ∀ {X Y : GL (Fin 3) F → R}, Y ∈ gl3CyclicSubspace X → gl3CyclicSubspace Y ≤ gl3CyclicSubspace X :=
    fun {X Y} hY => Submodule.span_le.mpr (by
      rintro _ ⟨h, rfl⟩
      exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace X h hY)
  intro G hG hG0
  exact hle (hW G (hle hmem hG) hG0) hmem

private theorem exists_isOpen_forall_mul_eq_of_mem_gl3CyclicSubspace {F : Type*} [CommRing F]
    [TopologicalSpace (GL (Fin 3) F)] [ContinuousMul (GL (Fin 3) F)] {R : Type*} [CommRing R]
    {W W' : GL (Fin 3) F → R}
    (hW : ∃ U : Subgroup (GL (Fin 3) F), IsOpen (U : Set (GL (Fin 3) F)) ∧ ∀ k ∈ U, ∀ g, W (g * k) = W g)
    (hmem : W' ∈ gl3CyclicSubspace W) :
    ∃ U : Subgroup (GL (Fin 3) F), IsOpen (U : Set (GL (Fin 3) F)) ∧ ∀ k ∈ U, ∀ g, W' (g * k) = W' g := by
  refine Submodule.span_induction (p := fun f _ => ∃ U : Subgroup (GL (Fin 3) F),
      IsOpen (U : Set (GL (Fin 3) F)) ∧ ∀ k ∈ U, ∀ g, f (g * k) = f g) ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨h, rfl⟩
    obtain ⟨U, hUo, hU⟩ := hW
    refine ⟨U.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, fun k hk g => ?_⟩
    · show IsOpen ((fun k : GL (Fin 3) F => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (U : Set (GL (Fin 3) F)))
      exact hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ U := Subgroup.mem_comap.mp hk
      have e : g * h * (h⁻¹ * k * h⁻¹⁻¹) = g * k * h := by group
      have h1 := hU _ hk' (g * h)
      rw [e] at h1
      simpa only [gl3AmbientRightTranslate_apply] using h1
  · refine ⟨⊤, ?_, fun k _ g => rfl⟩
    rw [Subgroup.coe_top]
    exact isOpen_univ
  · intro f₁ f₂ _ _ h₁ h₂
    obtain ⟨U₁, hU₁o, hU₁⟩ := h₁
    obtain ⟨U₂, hU₂o, hU₂⟩ := h₂
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk g => ?_⟩
    · rw [Subgroup.coe_inf]
      exact hU₁o.inter hU₂o
    · simp only [Pi.add_apply, hU₁ k (Subgroup.mem_inf.mp hk).1 g, hU₂ k (Subgroup.mem_inf.mp hk).2 g]
  · intro c f _ hf
    obtain ⟨U, hUo, hU⟩ := hf
    exact ⟨U, hUo, fun k hk g => by simp only [Pi.smul_apply, hU k hk g]⟩

private theorem rechooseE
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψc : Continuous ψ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (X₀ : CubicInductionData)
    (hX₀ : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X₀)
    (hc₁ : Continuous X₀.form) (hc₂ : Continuous X₀.whittaker) (hc₃ : Continuous X₀.dualWhittaker)
    (hm₁ : IsGaugeMajorised3 ℚ X₀.whittaker) (hm₂ : IsGaugeMajorised3 ℚ X₀.dualWhittaker)
    (hgen : ∀ v ∈ S, ∀ G ∈ gl3CyclicSubspace (X₀.whittakerLoc v), G ≠ 0 →
      X₀.whittakerLoc v ∈ gl3CyclicSubspace G)
    (hsm : ∀ v ∈ S, ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, X₀.whittakerLoc v (g * k) = X₀.whittakerLoc v g)
    (hvec : ∀ v ∈ S, ¬ IsRamifiedIn K v → ∃ W ∈ gl3CyclicSubspace (X₀.whittakerLoc v), W ≠ 0 ∧
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, W (g * k) = W g) ∧
      (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W))
    (R : Finset (HeightOneSpectrum (𝓞 ℚ))) (hR : ∀ v ∈ R, v ∈ S ∧ ¬ IsRamifiedIn K v) :
    ∃ Y : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
        (S : Set (HeightOneSpectrum (𝓞 ℚ))) Y ∧
      (Continuous Y.form ∧ Continuous Y.whittaker ∧ Continuous Y.dualWhittaker ∧
        IsGaugeMajorised3 ℚ Y.whittaker ∧ IsGaugeMajorised3 ℚ Y.dualWhittaker) ∧
      (∀ u, u ∉ R → Y.whittakerLoc u = X₀.whittakerLoc u) ∧
      Y.whittakerArch = X₀.whittakerArch ∧
      ∀ v ∈ R, (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g,
          Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) ∧ Y.whittakerLoc v ≠ 0 ∧
        (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
          Y.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (Y.whittakerLoc v)) ∧
        (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
          ∀ k ∈ Uv, ∀ g : LocalGL3 v, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) ∧
        (∀ W ∈ gl3CyclicSubspace (Y.whittakerLoc v), W ≠ 0 →
          Y.whittakerLoc v ∈ gl3CyclicSubspace W) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    exact ⟨X₀, hX₀, ⟨hc₁, hc₂, hc₃, hm₁, hm₂⟩, fun u _ => rfl, rfl, fun v hv => by simp at hv⟩
  | insert a R haR ih =>
    obtain ⟨Y, hYon, hYreg, hYloc, hYarch, hYR⟩ := ih (fun v hv => hR v (Finset.mem_insert_of_mem hv))
    obtain ⟨haS, haram⟩ := hR a (Finset.mem_insert_self a R)
    obtain ⟨W', hW'mem, hW'ne, hW'inv, hW'gate⟩ := hvec a haS haram
    have hYa : Y.whittakerLoc a = X₀.whittakerLoc a := hYloc a haR
    obtain ⟨Y', hY'on, hY'a, hY'other, hY'arch, -, hY'c₁, hY'c₂, hY'c₃, hY'm₁, hY'm₂⟩ :=
      exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace K ψ hψc μ D U gen
        (S : Set (HeightOneSpectrum (𝓞 ℚ))) Y hYon hYreg.1 hYreg.2.1 hYreg.2.2.1 hYreg.2.2.2.1 hYreg.2.2.2.2
        a (Finset.mem_coe.mpr haS) (by rw [hYa]; exact hgen a haS) W'
        (by rw [hYa]; exact hW'mem)
    refine ⟨Y', hY'on, ⟨hY'c₁, hY'c₂, hY'c₃, hY'm₁, hY'm₂⟩, ?_, hY'arch.trans hYarch, ?_⟩
    · intro u hu
      rw [Finset.mem_insert, not_or] at hu
      rw [hY'other u hu.1, hYloc u hu.2]
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hvR
      · rw [hY'a]
        exact ⟨hW'inv, hW'ne, hW'gate, exists_isOpen_forall_mul_eq_of_mem_gl3CyclicSubspace (hsm _ haS) hW'mem,
          forall_mem_gl3CyclicSubspace_of_mem (hgen _ haS) hW'mem⟩
      · have hva : v ≠ a := fun e => haR (e ▸ hvR)
        rw [hY'other v hva]
        exact hYR v hvR

end Rechoice

section RechoiceP

private theorem central_of_mem_gl3CyclicSubspace {F : Type*} [CommRing F] {R : Type*} [CommRing R]
    {W W' : GL (Fin 3) F → R} (χ : Fˣ → R)
    (hW : ∀ (t : Fˣ) (h : GL (Fin 3) F), W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = χ t * W h)
    (hmem : W' ∈ gl3CyclicSubspace W) :
    ∀ (t : Fˣ) (h : GL (Fin 3) F), W' (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = χ t * W' h := by
  refine Submodule.span_induction (p := fun f _ => ∀ (t : Fˣ) (h : GL (Fin 3) F),
      f (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = χ t * f h) ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨g, rfl⟩ t h
    simp only [gl3AmbientRightTranslate_apply, mul_assoc]
    exact hW t (h * g)
  · intro t h
    simp
  · intro f₁ f₂ _ _ h₁ h₂ t h
    simp only [Pi.add_apply, h₁ t h, h₂ t h, mul_add]
  · intro c f _ hf t h
    simp only [Pi.smul_apply, hf t h, smul_eq_mul]
    ring

private theorem admissible_of_mem_gl3CyclicSubspace {F : Type*} [CommRing F] [TopologicalSpace (GL (Fin 3) F)]
    {R : Type*} [CommRing R] {W W' : GL (Fin 3) F → R}
    (hW : ∀ Uv : Subgroup (GL (Fin 3) F), IsOpen (Uv : Set (GL (Fin 3) F)) →
      ∃ B : Finset (GL (Fin 3) F → R), ∀ G ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : GL (Fin 3) F, G (g * k) = G g) → G ∈ Submodule.span R (B : Set (GL (Fin 3) F → R)))
    (hmem : W' ∈ gl3CyclicSubspace W) :
    ∀ Uv : Subgroup (GL (Fin 3) F), IsOpen (Uv : Set (GL (Fin 3) F)) →
      ∃ B : Finset (GL (Fin 3) F → R), ∀ G ∈ gl3CyclicSubspace W',
        (∀ k ∈ Uv, ∀ g : GL (Fin 3) F, G (g * k) = G g) → G ∈ Submodule.span R (B : Set (GL (Fin 3) F → R)) := by
  have hle : gl3CyclicSubspace W' ≤ gl3CyclicSubspace W :=
    Submodule.span_le.mpr (by
      rintro _ ⟨h, rfl⟩
      exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h hmem)
  intro Uv hUv
  obtain ⟨B, hB⟩ := hW Uv hUv
  exact ⟨B, fun G hG hfix => hB G (hle hG) hfix⟩

private theorem rechooseP
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψc : Continuous ψ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (X₀ : CubicInductionData)
    (hX₀ : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X₀)
    (hc₁ : Continuous X₀.form) (hc₂ : Continuous X₀.whittaker) (hc₃ : Continuous X₀.dualWhittaker)
    (hm₁ : IsGaugeMajorised3 ℚ X₀.whittaker) (hm₂ : IsGaugeMajorised3 ℚ X₀.dualWhittaker)
    (hgen : ∀ v ∈ S, ∀ G ∈ gl3CyclicSubspace (X₀.whittakerLoc v), G ≠ 0 →
      X₀.whittakerLoc v ∈ gl3CyclicSubspace G)
    (hsm : ∀ v ∈ S, ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, X₀.whittakerLoc v (g * k) = X₀.whittakerLoc v g)
    (P : (v : HeightOneSpectrum (𝓞 ℚ)) → (LocalGL3 v → ℂ) → Prop)
    (R : Finset (HeightOneSpectrum (𝓞 ℚ))) (hR : ∀ v ∈ R, v ∈ S)
    (hvec : ∀ v ∈ R, ∃ W ∈ gl3CyclicSubspace (X₀.whittakerLoc v), W ≠ 0 ∧ P v W) :
    ∃ Y : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
        (S : Set (HeightOneSpectrum (𝓞 ℚ))) Y ∧
      (Continuous Y.form ∧ Continuous Y.whittaker ∧ Continuous Y.dualWhittaker ∧
        IsGaugeMajorised3 ℚ Y.whittaker ∧ IsGaugeMajorised3 ℚ Y.dualWhittaker) ∧
      (∀ u, u ∉ R → Y.whittakerLoc u = X₀.whittakerLoc u) ∧
      Y.whittakerArch = X₀.whittakerArch ∧
      Y.centralChar = X₀.centralChar ∧
      ∀ v ∈ R, Y.whittakerLoc v ≠ 0 ∧ P v (Y.whittakerLoc v) ∧
        (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
          ∀ k ∈ Uv, ∀ g : LocalGL3 v, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) ∧
        (∀ W ∈ gl3CyclicSubspace (Y.whittakerLoc v), W ≠ 0 →
          Y.whittakerLoc v ∈ gl3CyclicSubspace W) ∧
        Y.whittakerLoc v ∈ gl3CyclicSubspace (X₀.whittakerLoc v) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    exact ⟨X₀, hX₀, ⟨hc₁, hc₂, hc₃, hm₁, hm₂⟩, fun u _ => rfl, rfl, rfl, fun v hv => by simp at hv⟩
  | insert a R haR ih =>
    obtain ⟨Y, hYon, hYreg, hYloc, hYarch, hYcc, hYR⟩ :=
      ih (fun v hv => hR v (Finset.mem_insert_of_mem hv)) (fun v hv => hvec v (Finset.mem_insert_of_mem hv))
    have haS : a ∈ S := hR a (Finset.mem_insert_self a R)
    obtain ⟨W', hW'mem, hW'ne, hW'P⟩ := hvec a (Finset.mem_insert_self a R)
    have hYa : Y.whittakerLoc a = X₀.whittakerLoc a := hYloc a haR
    obtain ⟨Y', hY'on, hY'a, hY'other, hY'arch, hY'cc, hY'c₁, hY'c₂, hY'c₃, hY'm₁, hY'm₂⟩ :=
      exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace K ψ hψc μ D U gen
        (S : Set (HeightOneSpectrum (𝓞 ℚ))) Y hYon hYreg.1 hYreg.2.1 hYreg.2.2.1 hYreg.2.2.2.1 hYreg.2.2.2.2
        a (Finset.mem_coe.mpr haS) (by rw [hYa]; exact hgen a haS) W'
        (by rw [hYa]; exact hW'mem)
    refine ⟨Y', hY'on, ⟨hY'c₁, hY'c₂, hY'c₃, hY'm₁, hY'm₂⟩, ?_, hY'arch.trans hYarch, hY'cc.trans hYcc, ?_⟩
    · intro u hu
      rw [Finset.mem_insert, not_or] at hu
      rw [hY'other u hu.1, hYloc u hu.2]
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hvR
      · rw [hY'a]
        exact ⟨hW'ne, hW'P, exists_isOpen_forall_mul_eq_of_mem_gl3CyclicSubspace (hsm _ haS) hW'mem,
          forall_mem_gl3CyclicSubspace_of_mem (hgen _ haS) hW'mem, hW'mem⟩
      · have hva : v ≠ a := fun e => haR (e ▸ hvR)
        rw [hY'other v hva]
        exact hYR v hvR

end RechoiceP

section Furniture

private theorem psiLoc_ball_and_ne_one (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∃ k : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → psiLoc ψ v x = 1) ∧ psiLoc ψ v ≠ 1 := by
  obtain ⟨ψv, nψ, θr, θc, hball, hne, -, hprod, -, -, -⟩ := exists_localComponents_of_isGlobalAddChar ℚ ψ hψ
  have hloc : ∀ x : v.adicCompletion ℚ, psiLoc ψ v x = ψv v x := by
    intro x
    have h := hprod (StandardAddChar.finAdeleSingleAt ℚ v x)
    rw [finprod_eq_single (fun w => ψv w (StandardAddChar.finAdeleSingleAt ℚ v x w)) v (fun w hw => by
      simp only [StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v x hw, AddChar.map_zero_eq_one]),
      StandardAddChar.finAdeleSingleAt_apply_self] at h
    rw [← h]
    rfl
  refine ⟨⟨nψ v, fun x hx => by rw [hloc]; exact hball v x hx⟩, fun h1 => ?_⟩
  obtain ⟨x, -, hx⟩ := hne v
  exact hx (by rw [← hloc, h1, AddChar.one_apply])

private theorem psiLoc_level_zero (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hlev : TateLocal.addCharLevel (psiLoc ψ v) = 0) :
    (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1) ∧
      ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1 := by
  obtain ⟨hk, hne⟩ := psiLoc_ball_and_ne_one ψ hψ v
  obtain ⟨h0, x, hx, hx1⟩ := TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v (psiLoc ψ v) hk hne
  rw [hlev] at h0 hx
  refine ⟨fun y hy => h0 y (by rwa [WithZero.exp_zero]), x * varpi v, ?_, ?_⟩
  · rw [map_mul, AdelicLevel.valued_uniformizerUnit ℚ v]
    calc Valued.v x * WithZero.exp (-1 : ℤ)
        ≤ WithZero.exp (0 + 1) * WithZero.exp (-1 : ℤ) := by gcongr
      _ = 1 := by rw [← WithZero.exp_add, show (0 + 1 : ℤ) + -1 = 0 by norm_num, WithZero.exp_zero]
  · rw [mul_comm x, ← mul_assoc, inv_mul_cancel₀ (varpi_ne_zero v), one_mul]
    exact hx1

private theorem isLocallyConstant_of_forall_mem_higherUnitsAt
    (v : HeightOneSpectrum (𝓞 ℚ)) (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ u ∈ TateLocal.higherUnitsAt ℚ v n, χv u = 1) : IsLocallyConstant ⇑χv := by
  refine (IsLocallyConstant.iff_eventually_eq ⇑χv).mpr fun x => ?_
  have hx0 : (x : v.adicCompletion ℚ) ≠ 0 := x.ne_zero
  have ht0 : (x : v.adicCompletion ℚ) * varpi v ^ n ≠ 0 := mul_ne_zero hx0 (pow_ne_zero _ (varpi_ne_zero v))
  have hO : IsOpen ((fun y : (v.adicCompletion ℚ)ˣ => (y : v.adicCompletion ℚ) - x) ⁻¹'
      {z | Valued.v z ≤ Valued.v ((x : v.adicCompletion ℚ) * varpi v ^ n)}) :=
    (NumberField.AdelicLevel.isOpen_setOf_valued_le v _ ht0).preimage (Units.continuous_val.sub continuous_const)
  refine Filter.eventually_of_mem (hO.mem_nhds (by simp)) fun y hy => ?_
  have hy' : Valued.v ((y : v.adicCompletion ℚ) - x) ≤ Valued.v ((x : v.adicCompletion ℚ) * varpi v ^ n) := hy
  have hϖn : Valued.v (varpi v ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, show Valued.v (varpi v) = WithZero.exp (-1 : ℤ) from
      NumberField.AdelicLevel.valued_uniformizerUnit (K := ℚ) (v := v), ← WithZero.exp_nsmul]
    congr 1
    simp
  have hvx : Valued.v (x : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hsub : ((x⁻¹ * y : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1 =
      (x : v.adicCompletion ℚ)⁻¹ * ((y : v.adicCompletion ℚ) - x) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ hx0]
  have hle : Valued.v (((x⁻¹ * y : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [hsub, map_mul, map_inv₀, ← hϖn]
    calc (Valued.v (x : v.adicCompletion ℚ))⁻¹ * Valued.v ((y : v.adicCompletion ℚ) - x)
        ≤ (Valued.v (x : v.adicCompletion ℚ))⁻¹ * Valued.v ((x : v.adicCompletion ℚ) * varpi v ^ n) := by
          gcongr
      _ = Valued.v (varpi v ^ n) := by rw [map_mul, ← mul_assoc, inv_mul_cancel₀ hvx, one_mul]
  have hu : x⁻¹ * y ∈ TateLocal.higherUnitsAt ℚ v n := by
    rw [TateLocal.mem_higherUnitsAt_iff]
    refine ⟨?_, Or.inr hle⟩
    have hlt : Valued.v (((x⁻¹ * y : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) < 1 :=
      lt_of_le_of_lt hle (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    have h1 := Valuation.map_one_add_of_lt _ hlt
    rwa [add_sub_cancel] at h1
  have hyx : y = x * (x⁻¹ * y) := by rw [mul_inv_cancel_left]
  rw [hyx, map_mul, h _ hu, mul_one]

private theorem conductor_floor (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : Continuous ω)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ c : ℕ, ∀ a : ℕ, 1 ≤ a → c ≤ a →
      ∀ u ∈ TateLocal.higherUnitsAt ℚ v (2 * a - 1), localChar ω v u = 1 := by
  obtain ⟨c, hc⟩ := TateLocal.exists_hasConductorExponentAt_of_continuous ℚ v (localChar ω v)
    (continuous_localChar ω hω v)
  refine ⟨c, fun a ha hca u hu => hc.1 u ?_⟩
  rw [TateLocal.mem_higherUnitsAt_iff] at hu ⊢
  refine ⟨hu.1, ?_⟩
  rcases Nat.eq_zero_or_pos c with h0 | hcpos
  · exact Or.inl h0
  · rcases hu.2 with h | h
    · omega
    · exact Or.inr (h.trans (WithZero.exp_le_exp.mpr (by omega)))

private theorem norm_localChar (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hu : IsUnitaryChar (𝓞 ℚ) ℚ ω)
    (v : HeightOneSpectrum (𝓞 ℚ)) (z : (v.adicCompletion ℚ)ˣ) : ‖((localChar ω v z : ℂˣ) : ℂ)‖ = 1 := by
  simp only [localChar, MonoidHom.comp_apply]
  exact hu _

private theorem isGlobalAddChar_inv (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) :
    IsGlobalAddChar ℚ ψ⁻¹ where
  principalInvariant := fun x => by
    rw [AddChar.inv_apply, ← (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).map_neg]
    exact hψ.principalInvariant (-x)
  continuous := by
    change Continuous fun a => ψ⁻¹ a
    simp only [AddChar.inv_apply]
    exact hψ.continuous.comp continuous_neg
  nontrivial := fun h => hψ.nontrivial (inv_eq_one.mp h)

private theorem primeFibre_finite
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (p : HeightOneSpectrum (𝓞 ℚ)) : (RankinSelberg.primeFibre ℚ K p).Finite := by
  have hinj : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 K)) := by
    intro a b hab
    apply Rat.ringOfIntegersEquiv.injective
    apply RingHom.injective_int ((algebraMap (𝓞 ℚ) (𝓞 K)).comp Rat.ringOfIntegersEquiv.symm.toRingHom)
    show algebraMap (𝓞 ℚ) (𝓞 K) (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv a)) =
      algebraMap (𝓞 ℚ) (𝓞 K) (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv b))
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    exact hab
  haveI : FaithfulSMul (𝓞 ℚ) (𝓞 K) := (faithfulSMul_iff_algebraMap_injective (𝓞 ℚ) (𝓞 K)).mpr hinj
  haveI : Module.IsTorsionFree (𝓞 ℚ) (𝓞 K) := inferInstance
  have hfin := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)
  have hsub : HeightOneSpectrum.asIdeal '' RankinSelberg.primeFibre ℚ K p ⊆ p.asIdeal.primesOver (𝓞 K) := by
    rintro _ ⟨𝔓, h𝔓, rfl⟩
    rw [RankinSelberg.mem_primeFibre] at h𝔓
    exact ⟨𝔓.isPrime, ⟨by rw [← h𝔓]; rfl⟩⟩
  exact (hfin.subset hsub).of_finite_image HeightOneSpectrum.asIdeal_injective.injOn

private theorem apply_eq_one_of_finPart_eq_one (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχ : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ w 0 0)
    (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hx : RatIdele.finPart x = 1) : χ x = 1 := by
  set w₀ : InfinitePlace ℚ := Rat.infinitePlace
  let π : AdeleRing (𝓞 ℚ) ℚ →* w₀.Completion :=
    { toFun := fun z => z.1 w₀
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let y : (w₀.Completion)ˣ := Units.map π x
  have hxy : x = archUnitHom w₀ y := by
    refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
    · rw [Subsingleton.elim w w₀]
      have h1 : ((archUnitHom w₀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 w₀ = (y : w₀.Completion) := by
        rw [archUnitHom_apply, AdelicVolume.archCentralUnit_fst_self]
      exact (show (x : AdeleRing (𝓞 ℚ) ℚ).1 w₀ = (y : w₀.Completion) from rfl).trans h1.symm
    · rw [archUnitHom_apply, AdelicVolume.archCentralUnit_snd]
      exact Units.val_eq_one.mpr hx
  have h := hχ w₀ (IsTotallyReal.isReal w₀) y
  rw [mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h
  rw [hxy, archUnitHom_apply, ← archLocalChar_apply]
  exact Units.val_eq_one.mp h

private theorem isArchCompAt_mul_comp_idelicNorm_iff
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (χ₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ₀ : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ₀ w 0 0)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K) (u : ℂ) (n : ℤ) :
    IsArchCompAt K (μ * χ₀.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w u n ↔
      IsArchCompAt K μ w u n := by
  set η := χ₀.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm with hηdef
  have hη0 : IsArchCompAt K η w 0 0 := by
    have hR : (w.comap (algebraMap ℚ K)).IsReal := IsTotallyReal.isReal _
    obtain hw | hw := w.isReal_or_isComplex
    · exact (LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange ℚ K χ₀ w 0).1 hw 0
        (hχ₀ _ hR)
    · exact (LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange ℚ K χ₀ w 0).2.1 hw hR 0
        (hχ₀ _ hR)
  have hη1 : ∀ x : (w.Completion)ˣ, ((archLocalChar η w x : ℂˣ) : ℂ) = 1 := fun x => by
    have h := hη0 x
    rwa [mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h
  have e : ∀ x : (w.Completion)ˣ,
      ((archLocalChar (μ * η) w x : ℂˣ) : ℂ) = (archLocalChar μ w x : ℂ) := fun x => by
    have h2 : ((archLocalChar (μ * η) w x : ℂˣ) : ℂ) = (archLocalChar μ w x : ℂ) * (archLocalChar η w x : ℂ) := by
      simp only [archLocalChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul]
    rw [h2, hη1 x, mul_one]
  refine forall_congr' fun x => ?_
  rw [e x]

private theorem inertiaDeg_pos_of_mem_primeFibre
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (p : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 K)) (h : 𝔓 ∈ RankinSelberg.primeFibre ℚ K p) :
    0 < (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  have hu : 𝔓.under (𝓞 ℚ) = p := h
  rw [hu]
  haveI : 𝔓.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩
  haveI : p.asIdeal.IsMaximal := p.isMaximal
  haveI : Algebra.FiniteType (𝓞 ℚ) (𝓞 K) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 ℚ) (𝓞 K)
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Algebra.IsIntegral.finite
  exact Ideal.inertiaDeg'_pos p.asIdeal 𝔓.asIdeal

private theorem norm_eq_one_of_root
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμu : IsUnitaryChar (𝓞 K) K μ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : ¬ IsTwistRamifiedAbove K μ p) (z : ℂ)
    (hz : 1 - RankinSelberg.inducedE1 ℚ (inducedCoeff K μ) p * z
      + RankinSelberg.inducedE2 ℚ (inducedCoeff K μ) p * z ^ 2
      - RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) p * z ^ 3 = 0) :
    ‖z‖ = 1 := by
  classical
  rw [← LanglandsTunnell.RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three
      K hdeg.le (inducedCoeff K μ) p z, RankinSelberg.inducedEulerPoly,
    finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite K p), Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at hz
  obtain ⟨𝔓, h𝔓, h0⟩ := hz
  rw [Set.Finite.mem_toFinset] at h𝔓
  have hunr : IsUnramifiedCharAt μ 𝔓 := by
    by_contra hr
    exact hp ⟨𝔓, h𝔓, hr⟩
  have hc : ‖inducedCoeff K μ 𝔓‖ = 1 := by
    rw [inducedCoeff, if_pos hunr]
    exact hμu _
  have hf := inertiaDeg_pos_of_mem_primeFibre K p 𝔓 h𝔓
  simp only [RankinSelberg.inducedFactor, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X] at h0
  have h1 : inducedCoeff K μ 𝔓 * z ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) = 1 := (sub_eq_zero.mp h0).symm
  have h2 := congrArg norm h1
  rw [norm_mul, hc, one_mul, norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hf.ne').mp h2

end Furniture

section Central

private theorem globalPointsGL_upperUnipotent3 (x y z : ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (upperUnipotent3 x y z) =
      upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) ℚ) i j) =
    ((upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
      (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j
  rw [upperUnipotent3_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem whittaker3_central (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = ((ω z : ℂˣ) : ℂ) * Φ g)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ Φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = ((ω z : ℂˣ) : ℂ) * whittaker3 pins ψ Φ g := by
  letI := pins.nS
  have hzc : centralScalarGL 3 (𝓞 ℚ) ℚ z ∈ Subgroup.center (AdelicGL 3 (𝓞 ℚ) ℚ) := by
    change Matrix.GeneralLinearGroup.scalar (Fin 3) z ∈ Subgroup.center (AdelicGL 3 (𝓞 ℚ) ℚ)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨z, rfl⟩
  have hc : ∀ x y t : AdeleRing (𝓞 ℚ) ℚ, upperUnipotent3 x y t * (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) =
      centralScalarGL 3 (𝓞 ℚ) ℚ z * (upperUnipotent3 x y t * g) := fun x y t => by
    rw [← mul_assoc, Subgroup.mem_center_iff.mp hzc, mul_assoc]
  simp only [whittaker3, hc, hcen, mul_assoc, MeasureTheory.integral_const_mul]

private noncomputable def ideleAt (v : HeightOneSpectrum (𝓞 ℚ)) : (v.adicCompletion ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ)).comp
    (AdelicLevel.localUnit (𝓞 ℚ) ℚ v)

private theorem localChar_eq_ideleAt (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (t : (v.adicCompletion ℚ)ˣ) : localChar ω v t = ω (ideleAt v t) := rfl

private theorem centralScalarGL_ideleAt (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    centralScalarGL 3 (𝓞 ℚ) ℚ (ideleAt v t) = localToAdelic3 v (Matrix.GeneralLinearGroup.scalar (Fin 3) t) := by
  apply Units.ext
  change Matrix.scalar (Fin 3) ((ideleAt v t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) =
    finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (Matrix.scalar (Fin 3) (t : v.adicCompletion ℚ)))
  have hval : ((ideleAt v t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) =
      AdelicLevel.finIncl (𝓞 ℚ) ℚ (AdelicLevel.localUnit (𝓞 ℚ) ℚ v t : FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · rw [mapMatrix_arch_finMatN]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply, hval,
        AdelicLevel.finIncl_apply_fst]
    · simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply, hij]
      rfl
  · rw [mapMatrix_fin_finMatN]
    refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMatN_self]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
          hval, AdelicLevel.finIncl_apply_snd, AdelicLevel.localUnit_apply_self]
      · simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
          hij]
        rfl
    · rw [mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
          hval, AdelicLevel.finIncl_apply_snd, AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw]
      · simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
          hij]
        rfl

private theorem local_central (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hWcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hfac : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W g = Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ S, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g))
    (gA : GL (Fin 3) (InfiniteAdeleRing ℚ)) (hA : Warch gA ≠ 0) (h1 : ∀ v ∈ S, Wloc v 1 = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S) (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v) :
    Wloc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((localChar ω v t : ℂˣ) : ℂ) * Wloc v h := by
  classical

  set g : AdelicGL 3 (𝓞 ℚ) ℚ := archEmbed3 gA * localToAdelic3 v h with hg
  have hga : archComponent3 (𝓞 ℚ) ℚ g = gA := by
    rw [hg, map_mul, archComponent3_archEmbed3, archComponent3_localToAdelic3, mul_one]
  have hgv : componentAt3 (𝓞 ℚ) ℚ v g = h := by
    rw [hg, map_mul, componentAt3_archEmbed3, componentAt3_localToAdelic3_self, one_mul]
  have hgw : ∀ w, w ≠ v → componentAt3 (𝓞 ℚ) ℚ w g = 1 := fun w hw => by
    rw [hg, map_mul, componentAt3_archEmbed3, componentAt3_localToAdelic3_of_ne hw, one_mul]
  have hza : archComponent3 (𝓞 ℚ) ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (ideleAt v t) * g) = gA := by
    rw [map_mul, centralScalarGL_ideleAt, archComponent3_localToAdelic3, one_mul, hga]
  have hzv : componentAt3 (𝓞 ℚ) ℚ v (centralScalarGL 3 (𝓞 ℚ) ℚ (ideleAt v t) * g) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) t * h := by
    rw [map_mul, centralScalarGL_ideleAt, componentAt3_localToAdelic3_self, hgv]
  have hzw : ∀ w, w ≠ v → componentAt3 (𝓞 ℚ) ℚ w (centralScalarGL 3 (𝓞 ℚ) ℚ (ideleAt v t) * g) = 1 :=
    fun w hw => by
    rw [map_mul, centralScalarGL_ideleAt, componentAt3_localToAdelic3_of_ne hw, one_mul, hgw w hw]

  have hprod : ∀ (p : AdelicGL 3 (𝓞 ℚ) ℚ) (hv' : LocalGL3 v), componentAt3 (𝓞 ℚ) ℚ v p = hv' →
      (∀ w, w ≠ v → componentAt3 (𝓞 ℚ) ℚ w p = 1) →
      ∏ w ∈ S, Wloc w (componentAt3 (𝓞 ℚ) ℚ w p) = Wloc v hv' := by
    intro p hv' hpv hpw
    rw [Finset.prod_eq_single_of_mem v hv (fun w hwS hw => by rw [hpw w hw, h1 w hwS]), hpv]
  have hoff : ∀ p : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ w, w ≠ v → componentAt3 (𝓞 ℚ) ℚ w p = 1) →
      ∀ w, w ∉ S → componentAt3 (𝓞 ℚ) ℚ w p ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
    intro p hpw w hw
    rw [hpw w (fun hwv => hw (hwv ▸ hv))]
    exact one_mem _
  have h₁ : W g = Warch gA * Wloc v h := by
    rw [hfac g (hoff g hgw), hga, hprod g h hgv hgw]
  have h₂ : W (centralScalarGL 3 (𝓞 ℚ) ℚ (ideleAt v t) * g) =
      Warch gA * Wloc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) := by
    rw [hfac _ (hoff _ hzw), hza, hprod _ _ hzv hzw]
  have h₃ := hWcen (ideleAt v t) g
  rw [h₂, h₁, ← localChar_eq_ideleAt, mul_left_comm] at h₃
  exact mul_left_cancel₀ hA h₃

end Central

section LevelZero

open LanglandsTunnell.RankinSelberg in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

private theorem coreP
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ LanglandsTunnell.CubicLambda.eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (aQ : ℚ) (haQ : aQ ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) aQ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) aQ * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(aQ : ℝ)| ^ ((1 : ℝ) / 2)) •
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
        Warch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω (E z) : ℂˣ) : ℂ) * Warch g) ∧
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
                  ∏ w : InfinitePlace K, LanglandsTunnell.CubicLambda.lambdaArch K w) *
                (((ω (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|aQ| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), (S : Set (HeightOneSpectrum (𝓞 ℚ))) = {v | IsBadPlace K μ v} ∧
      ∃ X₀ : CubicInductionData,
        IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
          (S : Set (HeightOneSpectrum (𝓞 ℚ))) X₀ ∧
        Continuous X₀.form ∧ Continuous X₀.whittaker ∧ Continuous X₀.dualWhittaker ∧
        IsGaugeMajorised3 ℚ X₀.whittaker ∧ IsGaugeMajorised3 ℚ X₀.dualWhittaker ∧
        X₀.whittakerArch ≠ 0 ∧
        (∀ v ∈ S, X₀.whittakerLoc v 1 = 1) ∧
        (∀ v ∈ S, ∀ G ∈ gl3CyclicSubspace (X₀.whittakerLoc v), G ≠ 0 →
          X₀.whittakerLoc v ∈ gl3CyclicSubspace G) ∧
        (∀ v ∈ S, ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
          ∀ k ∈ Uv, ∀ g : LocalGL3 v, X₀.whittakerLoc v (g * k) = X₀.whittakerLoc v g) ∧
        (∀ v, v ∉ S → X₀.whittakerLoc v 1 = 1 ∧
          HasSphericalTorusValuesAt (inducedCoeff K μ) v (X₀.whittakerLoc v)) ∧
        (∀ v ∈ S, ¬ IsRamifiedIn K v → ∃ W ∈ gl3CyclicSubspace (X₀.whittakerLoc v), W ≠ 0 ∧
          (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, W (g * k) = W g) ∧
          (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
            W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W)) ∧
        X₀.whittakerArch = Warch ∧
        X₀.centralChar = ω ∧
        (∀ v ∈ S, ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
            ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace (X₀.whittakerLoc v),
              (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧
        (∀ v ∈ S,
          (∀ z : (v.adicCompletion ℚ)ˣ, ‖((localChar ω v z : ℂˣ) : ℂ)‖ = 1) ∧
          ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
            X₀.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
              ((localChar ω v t : ℂˣ) : ℂ) * X₀.whittakerLoc v h) ∧
        (∀ v ∈ S, IsRamifiedIn K v →
          ∃ (e N : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) e ∧
            (∀ M : ℕ, (∀ w ∈ primeFibre ℚ K v, ∃ aw : ℕ, aw ≤ M ∧
                LanglandsTunnell.TateLocal.HasConductorExponentAt K w (localChar μ w) aw) →
              (N : ℤ) ≤ 2 * ((∑ᶠ w ∈ primeFibre ℚ K v,
                  ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                    ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                        (2 * ((48 : ℤ) + e + M) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                      M + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
                ((48 : ℤ) + e + M))) ∧
            ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
              (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
                  (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(N : ℤ))) →
              ∀ g : LocalGL3 v, X₀.whittakerLoc v (g * k) = X₀.whittakerLoc v g) := by
  classical

  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) = {v | IsBadPlace K μ v} :=
    ⟨(LanglandsTunnell.CubicInduction.finite_setOf_isBadPlace_of_continuous
        K μ hμ.2.1).toFinset, Set.Finite.coe_toFinset _⟩
  have hmemS : ∀ v, v ∈ S ↔ IsBadPlace K μ v := fun v => by
    rw [← Finset.mem_coe, hS, Set.mem_setOf_eq]

  have hψl := fun v => psiLoc_level_zero ψ hψ v (hlev v)
  have hψne : ∀ v, psiLoc ψ v ≠ 1 := fun v => (psiLoc_ball_and_ne_one ψ hψ v).2

  have hωc : Continuous ω := hω.1.2.1
  have hωu : IsUnitaryChar (𝓞 ℚ) ℚ ω := hω.1.2.2
  choose cfl hcfl using fun v : HeightOneSpectrum (𝓞 ℚ) => conductor_floor ω hωc v

  have hfibfin : ∀ v : HeightOneSpectrum (𝓞 ℚ), (primeFibre ℚ K v).Finite := fun v => primeFibre_finite K v
  choose aω haω using fun v : HeightOneSpectrum (𝓞 ℚ) =>
    TateLocal.exists_hasConductorExponentAt_of_continuous ℚ v (localChar ω v) (continuous_localChar ω hωc v)
  let c : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun v =>
    48 + aω v + (hfibfin v).toFinset.sup fun w => LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w)
  have hc3 : ∀ v ∈ S, 3 ≤ c v := fun v _ => by
    show 3 ≤ 48 + aω v + _
    omega
  obtain ⟨χ₀, hχ₀, hχ₀c, hχ₀off, hχ₀ev⟩ :=
      LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
        S c hc3
  have hoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → IsUnramifiedCharAt χ₀ v :=
    fun v hv => hχ₀off v (fun h => hv ((hmemS v).mp h))
  have hcT : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar χ₀ v) (c v) ∧
        ∀ w ∈ primeFibre ℚ K v,
          LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) + 12 ≤ c v := by
    intro v hv
    refine ⟨hχ₀c v ((hmemS v).mpr hv), fun w hw => ?_⟩
    have hle : LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) ≤
        (hfibfin v).toFinset.sup fun w => LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) :=
      Finset.le_sup (f := fun w => LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w))
        ((hfibfin v).mem_toFinset.mpr hw)
    show _ + 12 ≤ 48 + aω v + _
    omega
  have hnsT := LanglandsTunnell.CubicInduction.not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists
      K μ hμ χ₀ hχ₀ hns
  obtain ⟨hμT, hcoefT, hbadT, hramT, hsumT⟩ :=
      LanglandsTunnell.CubicInduction.inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le
        K hdeg μ hμ χ₀ hχ₀ hoff c hcT
  set μT := μ * χ₀.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm with hμTdef
  have hmemST : ∀ v, v ∈ S ↔ IsBadPlace K μT v := fun v => (hmemS v).trans (hbadT v).symm

  let ωT : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ := ω * χ₀ ^ 3
  have hωT : IsAdmissibleTwist ℚ ωT ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μT p →
        IsUnramifiedCharAt ωT p ∧ LanglandsTunnell.CubicLambda.eulerCoeff ℚ ωT p = inducedE3 ℚ (inducedCoeff K μT) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μT w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μT w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ωT v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1)))
      := by
    have hE3 : ∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        inducedE3 ℚ (inducedCoeff K μT) p =
          ((χ₀ (uniformizerIdele ℚ p) : ℂˣ) : ℂ) ^ 3 * inducedE3 ℚ (inducedCoeff K μ) p :=
      fun p hp => LanglandsTunnell.CubicInduction.inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul K χ₀ p
        (inducedCoeff K μ) (inducedCoeff K μT) (hcoefT p hp)
    have harchT :
        ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
          (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
          (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μT w (uR w hw) ((aR w hw).val : ℤ)) →
          (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μT w (uC w hw) (kC w hw)) →
          ∀ v : InfinitePlace ℚ, v.IsReal →
            IsArchCompAt ℚ ωT v
              ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
              ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))) := by
      intro uR aR uC kC huR huC v hv
      set η := χ₀.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm with hηdef
      have hη0 : ∀ w : InfinitePlace K, IsArchCompAt K η w 0 0 := fun w => by
        have hR : (w.comap (algebraMap ℚ K)).IsReal := IsTotallyReal.isReal _
        obtain hw | hw := w.isReal_or_isComplex
        · exact (LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange ℚ K χ₀ w 0).1 hw 0
            (hχ₀ev _ hR)
        · exact (LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange ℚ K χ₀ w 0).2.1 hw hR 0
            (hχ₀ev _ hR)
      have hη1 : ∀ (w : InfinitePlace K) (x : (w.Completion)ˣ), ((archLocalChar η w x : ℂˣ) : ℂ) = 1 := fun w x => by
        have h := hη0 w x
        rwa [mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h
      have htr : ∀ (w : InfinitePlace K) (u : ℂ) (n : ℤ), IsArchCompAt K μT w u n → IsArchCompAt K μ w u n :=
        fun w u n h x => by
          have hx := h x
          have e : ((archLocalChar μT w x : ℂˣ) : ℂ) = (archLocalChar μ w x : ℂ) * (archLocalChar η w x : ℂ) := by
            rw [hμTdef]
            simp only [archLocalChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul]
          rw [e, hη1 w x, mul_one] at hx
          exact hx
      have hωv := hω.2.2 uR aR uC kC (fun w hw => htr w _ _ (huR w hw)) (fun w hw => htr w _ _ (huC w hw)) v hv
      intro x
      have hχv : ((archLocalChar χ₀ v x : ℂˣ) : ℂ) = 1 := by
        have h := hχ₀ev v hv x
        rwa [mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h
      have e : ((archLocalChar ωT v x : ℂˣ) : ℂ) = (archLocalChar ω v x : ℂ) * (archLocalChar χ₀ v x : ℂ) ^ 3 := by
        simp only [show ωT = ω * χ₀ ^ 3 from rfl, archLocalChar, MonoidHom.comp_apply, MonoidHom.mul_apply,
          MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
      rw [e, hχv, one_pow, mul_one]
      exact hωv x
    refine ⟨⟨fun u => ?_, ?_, fun x => ?_⟩, fun p hp => ?_, harchT⟩
    · show (ω * χ₀ ^ 3) _ = 1
      rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hω.1.1 u, hχ₀.1 u, one_pow, mul_one]
    · show Continuous fun x => (ω * χ₀ ^ 3) x
      simp only [MonoidHom.mul_apply, MonoidHom.pow_apply]
      exact hωc.mul (hχ₀.2.1.pow 3)
    · show ‖(((ω * χ₀ ^ 3) x : ℂˣ) : ℂ)‖ = 1
      rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow,
        hωu x, hχ₀.2.2 x, one_pow, mul_one]
    · have hpμ : ¬ IsBadPlace K μ p := fun h => hp ((hbadT p).mpr h)
      have h1 := (hω.2.1 p hpμ).1
      have h2 : IsUnramifiedCharAt χ₀ p := hoff p hpμ
      have hunr : IsUnramifiedCharAt ωT p := fun t ht ht' => by
        have e1 := h1 t ht ht'
        have e2 := h2 t ht ht'
        simp only [localChar, MonoidHom.comp_apply] at e1 e2
        show ((ω * χ₀ ^ 3).comp _) t = 1
        simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, e1, e2, one_pow, mul_one]
      refine ⟨hunr, ?_⟩
      have hval := (hω.2.1 p hpμ).2
      rw [LanglandsTunnell.CubicLambda.eulerCoeff, if_pos h1] at hval
      rw [LanglandsTunnell.CubicLambda.eulerCoeff, if_pos hunr, hE3 p hpμ, ← hval]
      show (((ω * χ₀ ^ 3) (uniformizerIdele ℚ p) : ℂˣ) : ℂ) = _
      rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
  have hωTc : Continuous ωT := hωT.1.2.1
  have hωTu : IsUnitaryChar (𝓞 ℚ) ℚ ωT := hωT.1.2.2
  choose cflT hcflT using fun v : HeightOneSpectrum (𝓞 ℚ) => conductor_floor ωT hωTc v

  have hWfinT_ex : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Wv : LocalGL3 v → ℂ, ¬ IsBadPlace K μT v →
      IsGL3PsiWhittakerFn (psiLoc ψ v) Wv ∧
      IsInducedSphericalAt (inducedCoeff K μT) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) Wv ∧
      Wv 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μT) v Wv := by
    intro v
    by_cases hv : IsBadPlace K μT v
    · exact ⟨fun _ => 0, fun h => (h hv).elim⟩
    · obtain ⟨Wv, hWv⟩ :=
        LanglandsTunnell.CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace
          K hdeg μT v hv ψ (hψl v).1 (hψl v).2
      exact ⟨Wv, fun _ => hWv⟩
  choose WfinT hWfinT using hWfinT_ex
  have hfinT : ∀ v, v ∉ S → IsGL3PsiWhittakerFn (psiLoc ψ v) (WfinT v) ∧
      IsInducedSphericalAt (inducedCoeff K μT) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (WfinT v) ∧
      WfinT v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μT) v (WfinT v) :=
    fun v hv => hWfinT v (fun hb => hv ((hmemST v).mpr hb))
  have hinv_finT : ∀ v, v ∉ S → IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (WfinT v) := by
    intro v hv
    obtain ⟨-, ⟨hU, -⟩, -⟩ := hfinT v hv
    exact hU

  obtain ⟨t₀T, ht₀T⟩ :=
      LanglandsTunnell.CubicInduction.exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar
        K hdeg μT hμT.2.2 ψ
  have hsph_finT : ∀ v, v ∉ S → ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1) → WfinT v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1 →
        ‖WfinT v h‖ ≤ 1 / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t₀T) :=
    fun v hv => ht₀T v (fun hb => hv ((hmemST v).mpr hb)) (hψl v).1 (hψl v).2 (WfinT v) (hfinT v hv)

  have hsatT : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μT v →
      (∀ w ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt μT w) ∧
        ∃ t : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ωT v) t ∧
          2 * (t : ℤ) + 12 ≤
            ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μT w
      := by
    intro v hvT
    have hv : IsBadPlace K μ v := (hbadT v).mp hvT
    refine ⟨hramT v hv, ?_⟩
    obtain ⟨t, ht⟩ := TateLocal.exists_hasConductorExponentAt_of_continuous ℚ v (localChar ωT v)
      (continuous_localChar ωT hωTc v)
    have hvS : v ∈ S := (hmemS v).mpr hv
    have h48 : 48 + aω v ≤ c v := by
      show 48 + aω v ≤ 48 + aω v + _
      omega
    have htc : t ≤ c v := by
      by_contra hlt
      obtain ⟨u, hu, hne⟩ := ht.2 (c v) (by omega)
      apply hne
      have h1 : localChar ω v u = 1 :=
        (haω v).1 u (TateLocal.higherUnitsAt_antitone (K := ℚ) (v := v) (show aω v ≤ c v by omega) hu)
      have h2 : localChar χ₀ v u = 1 := (hχ₀c v hvS).1 u hu
      simp only [localChar, MonoidHom.comp_apply] at h1 h2
      show ((ω * χ₀ ^ 3).comp _) u = 1
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, h1, h2, one_pow, mul_one]
    refine ⟨t, ht, ?_⟩
    have hsum := hsumT v hv
    omega

  have huRT : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μT w (uR w hw) ((aR w hw).val : ℤ) := fun w hw => by
    rw [hμTdef]
    exact (isArchCompAt_mul_comp_idelicNorm_iff K χ₀ hχ₀ev μ w _ _).2 (huR w hw)
  have huCT : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μT w (uC w hw) (kC w hw) := fun w hw => by
    rw [hμTdef]
    exact (isArchCompAt_mul_comp_idelicNorm_iff K χ₀ hχ₀ev μ w _ _).2 (huC w hw)

  have hχE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, χ₀ (E u) = 1 := fun u =>
    apply_eq_one_of_finPart_eq_one χ₀ hχ₀ev (E u) (hE u).2
  have hωE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, ωT (E u) = ω (E u) := fun u => by
    show (ω * χ₀ ^ 3) (E u) = ω (E u)
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hχE u, one_pow, mul_one]
  have hAF : ∀ (uR' : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR' : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
      (uC' : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC' : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
      (LanglandsTunnell.HeckeTate.heckeDatum K μT uR' aR' uC' kC').archFactor =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR' aR' uC' kC').archFactor := fun _ _ _ _ =>
    funext fun s => by simp only [LanglandsTunnell.LDatum.archFactor, LanglandsTunnell.HeckeTate.heckeDatum]
  have hAFd : ∀ (uR' : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR' : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
      (uC' : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC' : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
      (LanglandsTunnell.HeckeTate.heckeDatum K μT uR' aR' uC' kC').archFactorDual =
        (LanglandsTunnell.HeckeTate.heckeDatum K μ uR' aR' uC' kC').archFactorDual := fun _ _ _ _ =>
    funext fun s => by
      simp only [LanglandsTunnell.LDatum.archFactorDual, LanglandsTunnell.HeckeTate.heckeDatum]
  obtain ⟨hWne, hKfin, harch, a₀, hA⟩ :=
    LanglandsTunnell.CubicInduction.exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch
        K hdeg μT hμT hnsT ψ hψ S hlev WfinT hfinT ωT hωT hmemST
      (LanglandsTunnell.CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad
          K hdeg μT hμT S hmemST ωT hωT hsatT)
      uR aR uC kC huRT huCT E hE aQ haQ aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul Warch
      (by
        refine ⟨hWarch.1, hWarch.2.1, hWarch.2.2.1, hWarch.2.2.2.1, fun z g => ?_, fun σ hσ t e hte gInf => ?_,
          hWarch.2.2.2.2.2.2⟩
        · rw [hωE z]
          exact hWarch.2.2.2.2.1 z g
        · rw [hAF, hAFd, hωE aInf]
          exact hWarch.2.2.2.2.2.1 σ hσ t e hte gInf)
  obtain ⟨gA, hgA⟩ : ∃ x, Warch x ≠ 0 := Function.ne_iff.mp hWne
  let a : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun v => max (a₀ v) (max 1 (cflT v))
  have ha₀ : ∀ v ∈ S, a₀ v ≤ a v := fun v _ => le_max_left _ _
  have ha1 : ∀ v ∈ S, 1 ≤ a v := fun v _ =>
    show 1 ≤ max (a₀ v) (max 1 (cflT v)) from (le_max_left 1 (cflT v)).trans (le_max_right _ _)
  have hac : ∀ v, cflT v ≤ a v := fun v =>
    show cflT v ≤ max (a₀ v) (max 1 (cflT v)) from (le_max_right 1 (cflT v)).trans (le_max_right _ _)
  obtain ⟨Wloc, W, hWfinT', hWS, hfac, hWc, hWlaw, hWcen, hequiv, hvan, hinvW, heig1, heig2, hFE⟩ := hA a ha₀

  obtain ⟨-, hWg⟩ := LanglandsTunnell.CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod
      Warch Wloc S W hfac
    (fun v hv => by rw [hWfinT' v hv]; exact hinv_finT v hv)
    ⟨t₀T, fun v hv h => by rw [hWfinT' v hv]; exact hsph_finT v hv h⟩
    (fun v hv => ⟨(hWS v hv).2.2.1, (hWS v hv).2.2.2.1⟩)
    harch
  obtain ⟨hsumW, hgrW, hcontW, -, hintW, -⟩ :=
    summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 W hWc hWg
  obtain ⟨hsumWd, -, hcontWd, -, -, hint2Wd⟩ :=
    summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 (dualWhittakerFn3 W)
      (DualConjuncts.continuous_dualWhittakerFn3 hWc) (MirabolicMajorantDual.isGaugeMajorised3_dual hWg)

  let e₁ : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun p => RankinSelberg.inducedE1 ℚ (inducedCoeff K μT) p
  let e₂ : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun p => RankinSelberg.inducedE2 ℚ (inducedCoeff K μT) p
  let lam1 : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun p => cNormQ p * e₁ p
  let lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun p => cNormQ p * e₂ p
  have hvol : (((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
      (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne).ne'
  obtain ⟨A⟩ := nonempty_automorphyDatum31_of_zeta_fe ψ hψ S (fun v _ => hlev v) a ha1 ωT hωT.1
    (fun v hv u hu => hcflT v (a v) (ha1 v hv) (hac v) u hu) W hWc hWlaw hWcen hequiv hvan hsumW hgrW hcontW
    hsumWd hcontWd (fun g _ => hintW g) (fun g _ => hint2Wd (weylPrime3 * transposeInv3 g)) lam1 lam2 hinvW heig1
    heig2 D U gen _ (inv_mul_cancel₀ hvol) (hFE _ (inv_mul_cancel₀ hvol))

  obtain ⟨hP21, hP12⟩ := isCuspidalAlong_form_of_tempered_of_entire_eulerTwists ψ S a ωT hωT.1 W lam1 lam2 D U gen A
    e₁ e₂ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun p hp z hz => by
      have hgood : ¬ IsBadPlace K μT p := fun hb => hp ((hmemST p).mpr hb)
      rw [(hωT.2.1 p hgood).2] at hz
      exact norm_eq_one_of_root K hdeg μT hμT.2.2 p (fun h => hgood (Or.inr h)) z hz)
    (LanglandsTunnell.CubicInduction.exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg
        K hdeg μT hμT hnsT ωT (fun p hp => (hωT.2.1 p hp).2) S)

  obtain ⟨formT, WlocT', -, hfcT, hautT, hcenT, hP21T', hP12T', hmgT, hWfinT'', hatST, hfacT'⟩ :=
    exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong ψ hψ S a ωT W lam1 lam2 D U gen A hP21
      hP12 Warch Wloc (fun g T hST _ hT => hfac g T hST hT) (fun v hv => (hWS v hv).1) hWne
  have hWlocT' : ∀ v, v ∉ S → WlocT' v = WfinT v := fun v hv => (hWfinT'' v hv).trans (hWfinT' v hv)

  let Wfin : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ := fun v g =>
    (localChar χ₀⁻¹ v (Matrix.GeneralLinearGroup.det g) : ℂ) * WfinT v g
  have hfin : ∀ v, v ∉ S → IsGL3PsiWhittakerFn (psiLoc ψ v) (Wfin v) ∧
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wfin v) ∧
      Wfin v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (Wfin v) := by
    intro v hv
    have hgood : ¬ IsBadPlace K μ v := fun h => hv ((hmemS v).mpr h)
    have hunr : IsUnramifiedCharAt χ₀ v := hoff v hgood
    have hunr' : IsUnramifiedCharAt χ₀⁻¹ v := fun t ht ht' => by
      show (χ₀⁻¹.comp _) t = 1
      rw [MonoidHom.inv_comp, MonoidHom.inv_apply, inv_eq_one]
      exact hunr t ht ht'
    have hc' : ∀ w ∈ primeFibre ℚ K v, inducedCoeff K μ w =
        ((χ₀⁻¹ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * inducedCoeff K μT w := by
      intro w hw
      rw [hcoefT v hgood w hw, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_pow, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), one_mul]
    have hT3 :=
        LanglandsTunnell.CubicInduction.isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
          K χ₀⁻¹ v hunr' (inducedCoeff K μT) (inducedCoeff K μ) hc' (WfinT v)
    refine ⟨fun x y z g => ?_, hT3.1.mp (hfinT v hv).2.1, ?_, hT3.2.mp (hfinT v hv).2.2.2⟩
    · show (localChar χ₀⁻¹ v (Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z * g)) : ℂ) * WfinT v _ =
        psiLoc ψ v (x + y) * ((localChar χ₀⁻¹ v (Matrix.GeneralLinearGroup.det g) : ℂ) * WfinT v g)
      rw [map_mul, det_upperUnipotent3, one_mul, (hfinT v hv).1 x y z g]
      ring
    · show (localChar χ₀⁻¹ v (Matrix.GeneralLinearGroup.det 1) : ℂ) * WfinT v 1 = 1
      rw [map_one, map_one, Units.val_one, one_mul, (hfinT v hv).2.2.1]

  have hinv_fin : ∀ v, v ∉ S → IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wfin v) :=
    fun v hv => (hfin v hv).2.1.1
  obtain ⟨t₀, hsph_fin⟩ : ∃ t₀ : ℕ, ∀ v, v ∉ S → ∀ h : LocalGL3 v,
        (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1) → Wfin v h = 0) ∧
        (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1 →
          ‖Wfin v h‖ ≤ 1 / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t₀) := by
    refine ⟨t₀T, fun v hv h => ?_⟩
    have hn : ∀ d : (v.adicCompletion ℚ)ˣ, ‖((localChar χ₀⁻¹ v d : ℂˣ) : ℂ)‖ = 1 := fun d => by
      show ‖(((χ₀⁻¹.comp _) d : ℂˣ) : ℂ)‖ = 1
      rw [MonoidHom.comp_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hχ₀.2.2, inv_one]
    refine ⟨fun hnot => ?_, fun hle => ?_⟩
    · show (localChar χ₀⁻¹ v (Matrix.GeneralLinearGroup.det h) : ℂ) * WfinT v h = 0
      rw [(hsph_finT v hv h).1 hnot, mul_zero]
    · show ‖(localChar χ₀⁻¹ v (Matrix.GeneralLinearGroup.det h) : ℂ) * WfinT v h‖ ≤ _
      rw [norm_mul, hn, one_mul]
      exact (hsph_finT v hv h).2 hle
  obtain ⟨form, Wloc', hfc, haut, hcen, hP21', hP12', hmg, hWfin'', hatS, hfac'⟩ :
      ∃ (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ),
        Continuous form ∧
        (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = form g) ∧
        (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
          form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * form g) ∧
        IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) form ∧
        IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) form ∧
        IsModerateGrowth3 ℚ form ∧
        (∀ v, v ∉ S → Wloc v = Wfin v) ∧
        (∀ v ∈ S, IsGL3PsiWhittakerFn (psiLoc ψ v) (Wloc v) ∧ Wloc v 1 = 1 ∧
          HasWhittakerMultOne (psiLoc ψ v) (Wloc v) ∧
          (∀ F ∈ gl3CyclicSubspace (Wloc v), F ≠ 0 → Wloc v ∈ gl3CyclicSubspace F) ∧
          (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, Wloc v (g * k) = Wloc v g) ∧
          ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
            ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (Wloc v),
              (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
          (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
          whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ form g =
            Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g) := by
    have hχi : IsAdmissibleTwist ℚ χ₀⁻¹ := by
      refine ⟨fun u => ?_, ?_, fun x => ?_⟩
      · rw [MonoidHom.inv_apply, hχ₀.1 u, inv_one]
      · show Continuous fun x => χ₀⁻¹ x
        simp only [MonoidHom.inv_apply]
        exact hχ₀.2.1.inv
      · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hχ₀.2.2, inv_one]
    have hevi : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ₀⁻¹ w 0 0 := fun w hw x => by
      have h := hχ₀ev w hw x
      rw [mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h ⊢
      simp only [archLocalChar, MonoidHom.comp_apply] at h
      show (((χ₀⁻¹.comp _) x : ℂˣ) : ℂ) = 1
      rw [MonoidHom.comp_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h, inv_one]
    have hunrS : ∀ v, v ∉ S → IsUnramifiedCharAt χ₀⁻¹ v := fun v hv t ht ht' => by
      show (χ₀⁻¹.comp _) t = 1
      rw [MonoidHom.inv_comp, MonoidHom.inv_apply, inv_eq_one]
      exact hoff v (fun h => hv ((hmemS v).mpr h)) t ht ht'
    have hlc : ∀ v ∈ S, IsLocallyConstant ⇑(localChar χ₀⁻¹ v) := fun v hv =>
      isLocallyConstant_of_forall_mem_higherUnitsAt v (localChar χ₀⁻¹ v) (c v)
        (by show 1 ≤ 48 + aω v + _; omega) fun u hu => by
          show (χ₀⁻¹.comp _) u = 1
          rw [MonoidHom.inv_comp, MonoidHom.inv_apply, inv_eq_one]
          exact (hχ₀c v hv).1 u hu
    have hωeq : twistedCentralChar3 (𝓞 ℚ) ℚ ωT χ₀⁻¹ = ω := by
      show ωT * χ₀⁻¹ ^ 3 = ω
      ext z
      simp only [show ωT = ω * χ₀ ^ 3 from rfl, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply,
        inv_pow, mul_inv_cancel_right]
    obtain ⟨hTc, hTaut, hTcen, hTP21, hTP12, hTmg, hTwh⟩ :=
      LanglandsTunnell.CubicInduction.continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul
          ψ D U gen ωT formT hfcT hautT hcenT hP21T' hP12T' hmgT χ₀⁻¹ hχi
    refine ⟨fnTwist3 (𝓞 ℚ) ℚ χ₀⁻¹ formT,
      fun v g => (localChar χ₀⁻¹ v (Matrix.GeneralLinearGroup.det g) : ℂ) * WlocT' v g,
      hTc, hTaut, fun z g => by rw [hTcen z g, hωeq], hTP21, hTP12, hTmg, fun v hv => ?_, fun v hv => ?_,
      fun g T hST hT => ?_⟩
    · funext g
      show _ * WlocT' v g = _ * WfinT v g
      rw [hWlocT' v hv]
    · exact LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det
        ψ v (localChar χ₀⁻¹ v) (hlc v hv) (WlocT' v) (hatST v hv) _ (fun g => rfl)
    · rw [hTwh g, hfacT' g T hST hT,
        LanglandsTunnell.Converse.chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero
          χ₀⁻¹ hχi hevi T (fun v hv => hunrS v (fun h => hv (hST h))) g hT]
      show (∏ v ∈ T, ((localChar χ₀⁻¹ v (Matrix.GeneralLinearGroup.det (componentAt3 (𝓞 ℚ) ℚ v g)) : ℂˣ) : ℂ)) *
          (Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, WlocT' v (componentAt3 (𝓞 ℚ) ℚ v g)) =
        Warch (archComponent3 (𝓞 ℚ) ℚ g) *
          ∏ v ∈ T, ((localChar χ₀⁻¹ v (Matrix.GeneralLinearGroup.det (componentAt3 (𝓞 ℚ) ℚ v g)) : ℂ) *
            WlocT' v (componentAt3 (𝓞 ℚ) ℚ v g))
      rw [Finset.prod_mul_distrib]
      ring
  have hWloc' : ∀ v, v ∉ S → Wloc' v = Wfin v := hWfin''
  have hsph' : ∀ v, ¬ IsBadPlace K μ v →
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wloc' v) := by
    intro v hv
    have hvS : v ∉ S := fun h => hv ((hmemS v).mp h)
    rw [hWloc' v hvS]
    exact (hfin v hvS).2.1

  set W' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ form
    with hW'_def
  have hW'cen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W' (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = ((ω z : ℂˣ) : ℂ) * W' g :=
    whittaker3_central _ ψ form ω hcen
  have hloccen : ∀ v ∈ S, ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      Wloc' v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((localChar ω v t : ℂˣ) : ℂ) * Wloc' v h :=
    fun v hv t h => local_central S W' ω hW'cen Warch Wloc' (fun g hg => hfac' g S (Finset.Subset.refl S) hg)
      gA hgA (fun w hw => (hatS w hw).2.1) v hv t h
  obtain ⟨hW'c, hW'g⟩ := LanglandsTunnell.CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod
      Warch Wloc' S W' hfac'
    (fun v hv => by rw [hWloc' v hv]; exact hinv_fin v hv)
    ⟨t₀, fun v hv h => by rw [hWloc' v hv]; exact hsph_fin v hv h⟩
    (fun v hv => ⟨(hatS v hv).2.2.2.2.1, LanglandsTunnell.CubicInduction.exists_rootSize_bound_of_isGL3PsiWhittakerFn
        ψ v (hψne v) (Wloc' v) (hatS v hv).1
      (hatS v hv).2.2.2.2.1 (hatS v hv).2.2.2.2.2 (localChar ω v) (norm_localChar ω hωu v) (hloccen v hv)⟩)
    harch
  obtain ⟨hsumW', -, -, hhpW', -, -⟩ :=
    summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 W' hW'c hW'g
  have hW'law : IsGL3PsiWhittakerFn ψ W' :=
    LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq
        D U gen ψ hψ.principalInvariant form
      (fun x y z g => by rw [← globalPointsGL_upperUnipotent3]; exact haut _ g)
  have hexp := LanglandsTunnell.CubicInduction.hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong
      D U gen ψ hψ form hfc haut hP21' hP12' hsumW'

  obtain ⟨hfdc, hautd, hcend, hP21d, hP12d, hmgd⟩ :=
      LanglandsTunnell.CubicInduction.continuous_isCuspidalAlong_isModerateGrowth3_dualForm
        D U gen ω form hfc haut hcen hP21' hP12' hmg
  have hψinv := isGlobalAddChar_inv ψ hψ
  set Wd : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
    whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ (dualForm form) with hWd_def
  have hdual : Wd = dualWhittakerFn3 W' :=
    LanglandsTunnell.CubicInduction.CubicInductionData.dualWhittaker_eq_dualWhittakerFn3
        ψ D U gen ⟨form, W', Wloc', Warch, ω, Wd⟩ haut (fun _ => rfl) hW'law
      hexp (fun _ => rfl) hfc
  have hWdc : Continuous Wd := by
    rw [hdual]
    exact DualConjuncts.continuous_dualWhittakerFn3 hW'c
  have hWdg : IsGaugeMajorised3 ℚ Wd := by
    rw [hdual]
    exact MirabolicMajorantDual.isGaugeMajorised3_dual hW'g
  obtain ⟨hsumWd', -, -, hhpWd', -, -⟩ :=
    summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 Wd hWdc hWdg
  have hWdlaw : IsGL3PsiWhittakerFn ψ⁻¹ Wd :=
    LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq
        D U gen ψ⁻¹ hψinv.principalInvariant (dualForm form)
      (fun x y z g => by rw [← globalPointsGL_upperUnipotent3]; exact hautd _ g)
  have hexpd := LanglandsTunnell.CubicInduction.hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong
      D U gen ψ⁻¹ hψinv (dualForm form) hfdc hautd hP21d hP12d hsumWd'
  obtain ⟨hmom, hmomd⟩ :=
      LanglandsTunnell.CubicInduction.hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
        D U gen ψ form hexp hexpd hhpW' hhpWd'

  have hmult : ∀ v, HasWhittakerMultOne (psiLoc ψ v) (Wloc' v) := by
    intro v
    by_cases hv : v ∈ S
    · exact (hatS v hv).2.2.1
    · rw [hWloc' v hv]
      obtain ⟨hlaw, ⟨hU, hT1, hT2, hZ⟩, h1, -⟩ := hfin v hv
      exact hasWhittakerMultOne_of_isCosetEigenfunction v (psiLoc ψ v) _ _ _ (Wfin v) hU hT1 hT2 hZ hlaw (hlev v)
        (hψne v) h1

  have hX₀ : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) ⟨form, W', Wloc', Warch, ω, Wd⟩ :=
      { automorphic := haut
        central := hcen
        centralChar_ideleClass := hω.1.1
        cuspidalP21 := hP21'
        cuspidalP12 := hP12'
        whittaker_eq := fun _ => rfl
        whittaker_law := hW'law
        expansion := hexp
        whittakerLoc_law := fun v => by
          show IsGL3PsiWhittakerFn (psiLoc ψ v) (Wloc' v)
          by_cases hv : v ∈ S
          · exact (hatS v hv).1
          · rw [hWloc' v hv]
            exact (hfin v hv).1
        factorizable := fun g T hST hT => hfac' g T (fun v hv => hST v (Finset.mem_coe.mpr hv)) hT
        spherical := fun v hv => hsph' v (fun hb => hv (Finset.mem_coe.mpr ((hmemS v).mpr hb)))
        levelInvariant := fun v hv _ k hk g => by
          show Wloc' v (g * k) = Wloc' v g
          have hvS : v ∉ S := fun h => hv (Finset.mem_coe.mpr h)
          rw [hWloc' v hvS]
          exact hinv_fin v hvS g k (mem_localMaximalCompact3_of_mem_congruenceK1 (𝓞 ℚ) ℚ v hk)
        multOne := hmult
        moderateGrowth := hmg
        kFinite := hKfin
        iotaMoments := hmom
        whittakerHalfPlane := hhpW'
        dualWhittaker_eq := fun _ => rfl
        dualWhittaker_law := hWdlaw
        dual_expansion := hexpd
        dual_iotaMoments := hmomd
        dual_whittakerHalfPlane := hhpWd' }

  have hatS4 : ∀ w ∈ S, Wloc' w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (Wloc' w), F ≠ 0 → Wloc' w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, Wloc' w (g * k) = Wloc' w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (Wloc' w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)) :=
    fun w hw => ⟨(hatS w hw).2.1, (hatS w hw).2.2.2.1, (hatS w hw).2.2.2.2.1, (hatS w hw).2.2.2.2.2⟩
  have hcentS : ∀ w ∈ S, (∀ z : (w.adicCompletion ℚ)ˣ, ‖((localChar ω w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        Wloc' w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((localChar ω w t : ℂˣ) : ℂ) * Wloc' w h :=
    fun w hw => ⟨norm_localChar ω hωu w, hloccen w hw⟩
  have hSiff : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S := fun w => (hmemS w).symm
  have hωcond : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v → ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) a :=
    fun v hv => exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3 K hdeg μ hμ ω hω.1 hω.2.1 v hv

  have hvec := exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn K hdeg ψ hψ μ hμ uR aR uC kC
    huR huC hlev hns D U gen S hSiff ⟨form, W', Wloc', Warch, ω, Wd⟩ hX₀ hfc hW'c hWdc hW'g hWdg hWne hatS4 hcentS hωcond E hE
    aQ haQ aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hWarch.2.2

  have hωcondR : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ a : ℕ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) a ∧
      (a : ℤ) ≤ ∑ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v,
        (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w :=
    fun v => exists_hasConductorExponentAt_le_finsum_pinnedExp_of_eulerCoeff_eq_inducedE3 K hdeg μ hμ ω hω.1 hω.2.1 v
  have hLR := exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound K hdeg ψ hψ μ hμ uR aR
    uC kC huR huC hlev hns D U gen S hSiff ⟨form, W', Wloc', Warch, ω, Wd⟩ hX₀ hfc hW'c hWdc hW'g hWdg hWne hatS4 hcentS hωcond hωcondR
    E hE aQ haQ aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hWarch.2.2

  obtain ⟨Y, hYon, hYreg, hYloc, hYarch, hYcc, hYR⟩ := rechooseP K ψ hψ.continuous μ D U gen S
    ⟨form, W', Wloc', Warch, ω, Wd⟩ hX₀ hfc hW'c hWdc hW'g hWdg
    (fun v hv => (hatS v hv).2.2.2.1) (fun v hv => (hatS v hv).2.2.2.2.1)
    (fun v W => (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 → W 1 = 1) ∧
      ∃ N : ℕ,
        (∀ M : ℕ, (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v, ∃ aw : ℕ, aw ≤ M ∧
            LanglandsTunnell.TateLocal.HasConductorExponentAt K w (localChar μ w) aw) →
          (N : ℤ) ≤ 2 * ((∑ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v,
              ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                    (2 * ((48 : ℤ) + aω v + M) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                  M + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
            ((48 : ℤ) + aω v + M))) ∧
        ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
          (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
              (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(N : ℤ))) →
          ∀ g : LocalGL3 v, W (g * k) = W g)
    (S.filter fun v => IsRamifiedIn K v) (fun v hv => (Finset.mem_filter.mp hv).1)
    (fun v hv => by
      obtain ⟨hvS, hram⟩ := Finset.mem_filter.mp hv
      obtain ⟨W, hWmem, hWne', hW1, N, hN, hfix⟩ := hLR v hvS hram (aω v) (haω v)
      exact ⟨W, hWmem, hWne', hW1, N, hN, hfix⟩)
  have hR : ∀ v, v ∈ S.filter (fun v => IsRamifiedIn K v) ↔ v ∈ S ∧ IsRamifiedIn K v := fun v => Finset.mem_filter
  refine ⟨S, hS, Y, hYon, hYreg.1, hYreg.2.1, hYreg.2.2.1, hYreg.2.2.2.1, hYreg.2.2.2.2, ?_,
    fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv hram => ?_, ?_, ?_,
    fun v hv => ?_, fun v hv => ⟨norm_localChar ω hωu v, ?_⟩, fun v hv hram => ?_⟩
  · rw [hYarch]; exact hWne
  ·
    by_cases hram : IsRamifiedIn K v
    · exact (hYR v ((hR v).mpr ⟨hv, hram⟩)).2.1.1 (hlev v)
    · rw [hYloc v (fun h => hram ((hR v).mp h).2)]
      exact (hatS v hv).2.1
  ·
    by_cases hram : IsRamifiedIn K v
    · exact (hYR v ((hR v).mpr ⟨hv, hram⟩)).2.2.2.1
    · rw [hYloc v (fun h => hram ((hR v).mp h).2)]
      exact (hatS v hv).2.2.2.1
  ·
    by_cases hram : IsRamifiedIn K v
    · exact (hYR v ((hR v).mpr ⟨hv, hram⟩)).2.2.1
    · rw [hYloc v (fun h => hram ((hR v).mp h).2)]
      exact (hatS v hv).2.2.2.2.1
  ·
    show Y.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (Y.whittakerLoc v)
    rw [hYloc v (fun h => hv ((hR v).mp h).1)]
    show Wloc' v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (Wloc' v)
    rw [hWloc' v hv]
    exact ⟨(hfin v hv).2.2.1, (hfin v hv).2.2.2⟩
  ·
    rw [hYloc v (fun h => hram ((hR v).mp h).2)]
    exact hvec v ((show IsRamifiedIn K v ∨ IsTwistRamifiedAbove K μ v from (hmemS v).mp hv).resolve_left hram) hram
  · exact hYarch
  · exact hYcc
  ·
    by_cases hram : IsRamifiedIn K v
    · exact admissible_of_mem_gl3CyclicSubspace (hatS v hv).2.2.2.2.2 (hYR v ((hR v).mpr ⟨hv, hram⟩)).2.2.2.2
    · rw [hYloc v (fun h => hram ((hR v).mp h).2)]
      exact (hatS v hv).2.2.2.2.2
  ·
    by_cases hram : IsRamifiedIn K v
    · exact central_of_mem_gl3CyclicSubspace (fun t => ((localChar ω v t : ℂˣ) : ℂ)) (hloccen v hv)
        (hYR v ((hR v).mpr ⟨hv, hram⟩)).2.2.2.2
    · rw [hYloc v (fun h => hram ((hR v).mp h).2)]
      exact hloccen v hv
  ·
    obtain ⟨-, ⟨-, N, hN, hfix⟩, -⟩ := hYR v ((hR v).mpr ⟨hv, hram⟩)
    exact ⟨aω v, N, haω v, hN, hfix⟩

end LevelZero

end LanglandsTunnell.CubicInduction.InductionExistence

end FilingScope

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad.LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda"

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad.LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad.solution
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
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
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
        Warch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω (E z) : ℂˣ) : ℂ) * Warch g) ∧
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
                (((ω (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0) :
    ∀ (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
      (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ),
      ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), (S : Set (HeightOneSpectrum (𝓞 ℚ))) = {v | IsBadPlace K μ v} ∧
      ∃ X₀ : CubicInductionData,
        IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
          (S : Set (HeightOneSpectrum (𝓞 ℚ))) X₀ ∧
        Continuous X₀.form ∧ Continuous X₀.whittaker ∧ Continuous X₀.dualWhittaker ∧
        IsGaugeMajorised3 ℚ X₀.whittaker ∧ IsGaugeMajorised3 ℚ X₀.dualWhittaker ∧
        X₀.whittakerArch ≠ 0 ∧
        (∀ v ∈ S, X₀.whittakerLoc v 1 = 1) ∧
        (∀ v ∈ S, ∀ G ∈ gl3CyclicSubspace (X₀.whittakerLoc v), G ≠ 0 →
          X₀.whittakerLoc v ∈ gl3CyclicSubspace G) ∧
        (∀ v ∈ S, ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
          ∀ k ∈ Uv, ∀ g : LocalGL3 v, X₀.whittakerLoc v (g * k) = X₀.whittakerLoc v g) ∧
        (∀ v, v ∉ S → X₀.whittakerLoc v 1 = 1 ∧
          HasSphericalTorusValuesAt (inducedCoeff K μ) v (X₀.whittakerLoc v)) ∧
        (∀ v ∈ S, ¬ IsRamifiedIn K v → ∃ W ∈ gl3CyclicSubspace (X₀.whittakerLoc v), W ≠ 0 ∧
          (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, W (g * k) = W g) ∧
          (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
            W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W)) ∧
        X₀.whittakerArch = Warch ∧

        X₀.centralChar = ω ∧
        (∀ v ∈ S, ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
            ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace (X₀.whittakerLoc v),
              (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧
        (∀ v ∈ S,
          (∀ z : (v.adicCompletion ℚ)ˣ, ‖((localChar ω v z : ℂˣ) : ℂ)‖ = 1) ∧
          ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
            X₀.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
              ((localChar ω v t : ℂˣ) : ℂ) * X₀.whittakerLoc v h) ∧
        (∀ v ∈ S, IsRamifiedIn K v →
          ∃ (e N : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) e ∧
            (∀ M : ℕ, (∀ w ∈ primeFibre ℚ K v, ∃ aw : ℕ, aw ≤ M ∧
                LanglandsTunnell.TateLocal.HasConductorExponentAt K w (localChar μ w) aw) →
              (N : ℤ) ≤ 2 * ((∑ᶠ w ∈ primeFibre ℚ K v,
                  ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                    ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                        (2 * ((48 : ℤ) + e + M) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                      M + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
                ((48 : ℤ) + e + M))) ∧
            ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
              (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
                  (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(N : ℤ))) →
              ∀ g : LocalGL3 v, X₀.whittakerLoc v (g * k) = X₀.whittakerLoc v g) := by
  intro D U gen
  exact LanglandsTunnell.CubicInduction.InductionExistence.coreP K _hdeg ψ _hψ hlev μ _hμ _hns uR aR uC kC huR huC ω hω
    E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul Warch hWarch D U gen

end S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad (solution)
