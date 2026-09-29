-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cb71e3c8-c4dd-583b-bc74-4f4f32f0ee23

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_normalisedNewvector_of_isLocalWhittakerDatum_of_localFE32_of_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_localPackage_psiLocal_inv_comp_mul_diagonal_of_localPackage_psiLocal_of_gauge
import Theorems.Thm_AutomorphicForm_psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder"
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.torusChar3_one FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO"
p2m_attr_erase "simp" "ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda LanglandsTunnell UnramifiedWhittaker

noncomputable section

namespace TorusGlue3

open LanglandsTunnell LanglandsTunnell.CubicInduction

section Points

noncomputable def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, archMat3, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, archMat3, AdelicLevel.adeleFin_apply]

theorem archMat3_one : archMat3 1 = 1 :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

noncomputable def archEmbed3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun g :=
    { val := archMat3 g
      inv := archMat3 ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix _ _ _)
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

theorem archComponent3_archEmbed3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archEmbed3 g) = g :=
  Units.ext (by
    show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) = g
    exact mapMatrix_arch_archMat3 _)

theorem componentAt3_archEmbed3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ v (archEmbed3 g) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v) (AdelicLevel.adeleFin (𝓞 ℚ) ℚ
      (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)) =
    ((1 : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
  simp only [archMat3, Matrix.of_apply, AdelicLevel.adeleFin_apply, Units.val_one]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem componentAt3_localToAdelic3_self (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v h) = h := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v) (AdelicLevel.adeleFin (𝓞 ℚ) ℚ
      (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v
        (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) i j)) =
    (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
  simp only [finMatN, Matrix.of_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_self]

theorem componentAt3_localToAdelic3_of_ne {u v : HeightOneSpectrum (𝓞 ℚ)} (huv : u ≠ v)
    (h : LocalGL3 v) : componentAt3 (𝓞 ℚ) ℚ u (localToAdelic3 v h) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ u) (AdelicLevel.adeleFin (𝓞 ℚ) ℚ
      (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v
        (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) i j)) =
    ((1 : GL (Fin 3) (u.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (u.adicCompletion ℚ)) i j
  simp only [finMatN, Matrix.of_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_of_ne (Fin 3) (𝓞 ℚ) ℚ v (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j huv,
    Units.val_one]

theorem archComponent3_localToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v h) = 1 :=
  Units.ext (by
    show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v
          (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) = 1
    exact mapMatrix_arch_finMatN _ _ _ _)

theorem exists_point (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (h : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v)
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

theorem isGL3PsiWhittakerFn_of_mem {F : Type} [CommRing F] {ψ : AddChar F ℂ} {W₀ : GL (Fin 3) F → ℂ}
    (hW₀ : IsGL3PsiWhittakerFn ψ W₀) {W : GL (Fin 3) F → ℂ} (hW : W ∈ gl3CyclicSubspace W₀) :
    IsGL3PsiWhittakerFn ψ W := by
  refine Submodule.span_induction (p := fun W _ => IsGL3PsiWhittakerFn ψ W) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ x y z g
    simp only [gl3AmbientRightTranslate_apply, mul_assoc]
    exact hW₀ x y z (g * h)
  · intro x y z g; simp
  · intro f₁ f₂ _ _ h₁ h₂ x y z g
    simp only [Pi.add_apply, h₁ x y z g, h₂ x y z g, mul_add]
  · intro c f _ h x y z g
    simp only [Pi.smul_apply, smul_eq_mul, h x y z g]
    ring

end TorusGlue3

end

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hne : X.whittakerArch ≠ 0)
    (hatS : ∀ w ∈ S, X.whittakerLoc w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w), F ≠ 0 → X.whittakerLoc w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hωcond : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v → ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar X.centralChar v) a)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
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
    (hArch :
      (Continuous X.whittakerArch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf X.whittakerArch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        X.whittakerArch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((X.centralChar (E z) : ℂˣ) : ℂ) * X.whittakerArch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 =
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
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => X.whittakerArch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => X.whittakerArch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((X.centralChar (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul X.whittakerArch (σ.comp E) s 1 ≠ 0)
 :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), IsTwistRamifiedAbove K μ v → ¬ IsRamifiedIn K v →
      ∃ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 ∧
        (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, W (g * k) = W g) ∧
        (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
          W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W) := by
  intro v hram hK
  classical
  have hvbad : IsBadPlace K μ v := Or.inr hram
  have hvS : v ∈ S := (hS v).1 hvbad
  obtain ⟨h1, hirr, hsm, hadm⟩ := hatS v hvS

  obtain ⟨gInf, σA, hσA, hte, hnv⟩ :=
    exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn K hdeg ψ hψ μ hμ uR aR uC kC huR huC hlev hns D U gen S hS X hX hcont hcontW hcontW' hW hW' hne hatS hcent hωcond E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hArch
  obtain ⟨ε, hε, h31⟩ :=
    exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn K hdeg ψ hψ μ hμ uR aR uC kC huR huC hlev hns D U gen S hS X hX hcont hcontW hcontW' hW hW' hne hatS hcent hωcond E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hArch v hvS hK
      ⟨gInf, σA, hσA, hte, hnv⟩

  have hsc : ∀ (t : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
      Matrix.GeneralLinearGroup.scalar (Fin 3) t * g = g * Matrix.GeneralLinearGroup.scalar (Fin 3) t := by
    intro t g
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    have h : ((Matrix.GeneralLinearGroup.scalar (Fin 3) t : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        (t : v.adicCompletion ℚ) • (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

  have hsign : psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ ∨
      psiLoc ψ v = NumberField.StandardAddChar.psiLocal ℚ v :=
    AutomorphicForm.psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero ψ hψ hlev v

  have hF0 : X.form ≠ 0 := by
    obtain ⟨gA, hgA⟩ : ∃ x, X.whittakerArch x ≠ 0 := Function.ne_iff.mp hne
    have hcomp : ∀ u, componentAt3 (𝓞 ℚ) ℚ u (TorusGlue3.archEmbed3 gA) = 1 := fun u =>
      TorusGlue3.componentAt3_archEmbed3 u gA
    have h := hX.factorizable (TorusGlue3.archEmbed3 gA) S (fun u hu => Finset.mem_coe.mp hu)
      (fun u _ => by rw [hcomp u]; exact one_mem _)
    rw [TorusGlue3.archComponent3_archEmbed3] at h
    have hprodS : ∏ u ∈ S, X.whittakerLoc u (componentAt3 (𝓞 ℚ) ℚ u (TorusGlue3.archEmbed3 gA)) = 1 :=
      Finset.prod_eq_one fun u hu => by rw [hcomp u]; exact (hatS u hu).1
    rw [hprodS, mul_one] at h
    intro hform
    have h2 := hX.whittaker_eq (TorusGlue3.archEmbed3 gA)
    rw [h, hform] at h2
    apply hgA
    rw [h2]
    simp [whittaker3]
  have hWgX :  ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
  (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → X.whittakerLoc v h = 0) ∧
  (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
    ‖X.whittakerLoc v h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t) :=
    exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero_of_isCubicInductionDataOn K
      (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ (S : Set (HeightOneSpectrum (𝓞 ℚ))) X hX hF0 hW S
      (fun p hp hps => hp (Finset.mem_coe.mp hps)) v
  obtain ⟨W₀, d, ε₀, hε₀, h₀, hω₀, hWg₀, h31₀, htrans, hdT, hdT2, hdN⟩ :
      ∃ (W₀ : LocalGL3 v → ℂ) (d : LocalGL3 v) (ε₀ : ℂ), ε₀ ≠ 0 ∧
        IsLocalWhittakerDatum v (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W₀ ∧
        (∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
          W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((localChar X.centralChar v t : ℂˣ) : ℂ) * W₀ h) ∧
        ( ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W₀ h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W₀ h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t)) ∧
        ( ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W₀ 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W₀ 1 s g =
            ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W₀) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W₀ 1 (1 - s) g =
            ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε₀ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((inducedLevelAt K μ v : ℂ) * (1 / 2 - s))) * P s))) ∧
        (∀ W ∈ gl3CyclicSubspace W₀, (fun g : LocalGL3 v => W (d * g * d⁻¹)) ∈ gl3CyclicSubspace (X.whittakerLoc v)) ∧
        (∀ n : ℕ, d * iotaTorusLocal v n = iotaTorusLocal v n * d) ∧
        (∀ k₁ k₂ : ℕ, d * twoRowPointLocal v k₁ k₂ = twoRowPointLocal v k₁ k₂ * d) ∧
        (∀ c : ℕ, ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, d * k * d⁻¹ ∈ congruenceK1 (𝓞 ℚ) ℚ v c) := by
    rcases hsign with hinv | hstd
    ·
      refine ⟨X.whittakerLoc v, 1, ε, hε, ?_, (hcent v hvS).2, hWgX, h31, ?_, fun n => by simp, fun k₁ k₂ => by simp,
        fun c k hk => by simpa using hk⟩
      · rw [← hinv]
        exact ⟨hX.whittakerLoc_law v, h1, hX.multOne v, hirr, hsm, hadm⟩
      · intro W hW
        simpa using hW
    ·
      let ϖ : v.adicCompletionIntegers ℚ := ⟨varpi v,
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
          rw [NumberField.AdelicLevel.valued_uniformizerUnit]
          exact le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num)))⟩
      have hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) :=
        NumberField.AdelicLevel.valued_uniformizerUnit ℚ v
      have hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0 := varpi_ne_zero v
      obtain ⟨W₀, d, hLWD, hcen₀, hWg', ⟨ε₀, hε₀, -, h31'⟩, htr, hdT', hdT2', hdN', -, -, -, -⟩ :=
        localPackage_psiLocal_inv_comp_mul_diagonal_of_localPackage_psiLocal_of_gauge v (psiLoc ψ v) hstd (X.whittakerLoc v)
          (hX.whittakerLoc_law v) h1 (hX.multOne v) hirr hsm hadm hWgX (localChar X.centralChar v) (hcent v hvS).1
          (hcent v hvS).2 hπ hϖ (inducedEulerPoly ℚ (inducedCoeff K μ) v) (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v) ε hε
          (inducedLevelAt K μ v) h31
      exact ⟨W₀, d, ε₀, hε₀, hLWD, hcen₀, hWg', h31', htr, hdT', hdT2', hdN'⟩

  have hZ :  ∀ (g : LocalGL3 v) (d : (v.adicCompletion ℚ)ˣ), Valued.v (d : v.adicCompletion ℚ) = 1 →
      Valued.v ((d : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(inducedLevelAt K μ v : ℤ)) →
      W₀ (g * Matrix.GeneralLinearGroup.scalar (Fin 3) d) = W₀ g := by
    obtain ⟨a₀, hac, hcond⟩ := hωcond v hK
    intro g d' hd1 hd2
    have hmemc : d' ∈ higherUnitsAt ℚ v (inducedLevelAt K μ v) := by
      rcases Nat.eq_zero_or_pos (inducedLevelAt K μ v) with hc | hc
      · exact ⟨hd1, Or.inl hc⟩
      · exact ⟨hd1, Or.inr hd2⟩
    have hχ : localChar X.centralChar v d' = 1 := hcond.1 d' (higherUnitsAt_antitone ℚ v hac hmemc)
    rw [← hsc d' g, hω₀ d' g, hχ, Units.val_one, one_mul]

  have hdat :
          ∀ {ϖ : v.adicCompletionIntegers ℚ}
            (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0),
            Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) →
            ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
            (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
            (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
              W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
            (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
              k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
            (hW₂1 : W₂ 1 = 1)
            (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
              W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
                a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
            (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
              torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m)
            (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
            (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
              W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
            (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
              k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
            (hW₂d1 : W₂d 1 = 1)
            (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
              W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
                (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂) * W₂d g)
            (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
              torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * (a₁ + a₂) / (a₁ * a₂))
                ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂)) m),
            letI := localGLBorel ℚ v
            haveI := borelSpace_localGLBorel ℚ v
            ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
              (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
            ∀ W ∈ gl3CyclicSubspace W₀,
            ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
              (∀ s : ℂ, σ₂ < s.re →
                Integrable
                  (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                    (W (iotaGL g) * W₂ g) *
                      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                          v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
                  (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
              (∀ s : ℂ, σ₃ < (1 - s).re →
                Integrable
                  (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                    (dualWhittakerFn3 W (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                          (-(inducedLevelAt K μ v : ℤ)))) * W₂d g) *
                      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                          v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
                  (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
              (∀ s : ℂ, σ₂ < s.re →
                RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
                    (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
                    s (fun g => W (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
                  p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
              (∀ s : ℂ, σ₃ < (1 - s).re →
                RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
                    (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
                    (1 - s) (fun g => dualWhittakerFn3 W (iotaGL g * iotaGL
                        (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                        (-(inducedLevelAt K μ v : ℤ))))) W₂d *
                    qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
                  pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) ∧
              (∀ s : ℂ,
                pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
                    (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval (a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                        s))) *
                    (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval (a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                        s))) =
                  p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))
                      *
                    (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                        2))) *
                    (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                        2))) *
                    ε₀ ^ 2) := by
    intro ϖ₁ hπ₁ hϖ₁ a₁ a₂ ha' W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT
    exact forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge v _ rfl W₀ h₀.1
      h₀.2.2.1 h₀.2.2.2.1 h₀.2.2.2.2.1 h₀.2.2.2.2.2 hWg₀ (localChar X.centralChar v) (hcent v hvS).1 hω₀ hπ₁ hϖ₁
      (inducedEulerPoly ℚ (inducedCoeff K μ) v) (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v) ε₀ (inducedLevelAt K μ v) h31₀
      a₁ a₂ ha' W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT

  obtain ⟨W, hWmem, hWK, hW1, hRS⟩ :=
    exists_normalisedNewvector_of_isLocalWhittakerDatum_of_localFE32_of_ne_zero K hdeg μ hμ v hram hK W₀ h₀ hZ ε₀ hε₀ hdat
  have hWlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W :=
    TorusGlue3.isGL3PsiWhittakerFn_of_mem h₀.1 hWmem

  have hTor : HasSphericalTorusValuesAt (inducedCoeff K μ) v W :=
    hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume K hdeg.le μ v (inducedLevelAt K μ v) W
      hWlaw hWK hW1 hRS

  refine ⟨fun g => W (d * g * d⁻¹), htrans W hWmem, ?_, ?_, ?_⟩
  · intro h0
    have := congrFun h0 1
    simp only [mul_one, mul_inv_cancel, Pi.zero_apply] at this
    exact one_ne_zero (hW1 ▸ this)
  · intro k hk g
    show W (d * (g * k) * d⁻¹) = W (d * g * d⁻¹)
    have e1 : d * (g * k) * d⁻¹ = (d * g * d⁻¹) * (d * k * d⁻¹) := by group
    rw [e1, hWK _ (hdN _ k hk)]
  · intro _hlev0
    have hd1 : W (d * 1 * d⁻¹) = 1 := by rw [mul_one, mul_inv_cancel, hW1]
    refine ⟨hd1, fun n => ?_, fun k₁ k₂ hk => ?_⟩
    · show W (d * iotaTorusLocal v n * d⁻¹) = _
      rw [hdT n, mul_assoc, mul_inv_cancel, mul_one]
      exact hTor.1 n
    · show W (d * twoRowPointLocal v k₁ (k₂ + 1) * d⁻¹) = _
      rw [hdT2 k₁ (k₂ + 1), mul_assoc, mul_inv_cancel, mul_one]
      exact hTor.2 k₁ k₂ hk

end S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn (solution)
