-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0ad67e13-24c9-5fe2-9427-a6f720cabf22

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

import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_CubicInduction_sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three
import Theorems.Thm_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder"
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl"
p2m_attr_erase "simp" "groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.addCharLevel TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff signEpsilon HeckeTate.heckeDatum CubicInduction.exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel CubicInduction.exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel CubicInduction.sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3 CubicInduction.localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq CubicInduction.sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn CubicInduction.psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "CubicInductionData IsCubicInductionDataOn IsGL3PsiWhittakerFn gl3CyclicSubspace transposeInv3 whittaker3 inducedCoeff psiLoc AdelicGL componentAt3 archComponent3 LocalGL3 IsRamifiedIn IsBadPlace inducedLevelAt HasSphericalTorusValuesAt dualWhittakerFn3 weylPrime3 archRoot₁ archRoot₂ archRootSum IsGaugeMajorised3 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne finMatN mapMatrix_arch_finMatN localToAdelic3 exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3 localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar"
namespace GammaIdGlue
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn.LanglandsTunnell.CubicInduction"

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

end LanglandsTunnell.CubicInduction.GammaIdGlue

end

open LanglandsTunnell.CubicInduction.GammaIdGlue in
open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn.LanglandsTunnell in
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

    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S) (hram : ¬ IsRamifiedIn K v)
    (harch : ∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧ (-1 : ℂ) ^ e = 1) ∧
      ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0) :
    ∃ ε : ℂ, ε ≠ 0 ∧
    (∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) 1 s g =
            ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (X.whittakerLoc v) 1 (1 - s) g =
            ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((inducedLevelAt K μ v : ℂ) * (1 / 2 - s))) * P s))) := by
  classical

  obtain ⟨hSint, hSint'⟩ := LanglandsTunnell.CubicInduction.sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3 K hdeg ψ hψ μ hμ uR aR uC kC huR huC hlev hns D U gen S hS X hX
    hcont hcontW hcontW' hW hW' hne hatS hcent hωcond E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hArch

  have hvol : ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
      (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne).ne'
  set c : ℂ := (((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ))⁻¹ with hc_def
  have hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1 := by
    rw [hc_def, inv_mul_cancel₀ hvol]

  have hexp : X.form ≠ 0 ∧ ∀ w, ¬ IsBadPlace K μ w →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0 →
        X.whittakerLoc w 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) w (X.whittakerLoc w) := by

    obtain ⟨gA, hgA⟩ : ∃ x, X.whittakerArch x ≠ 0 := Function.ne_iff.mp hne
    obtain ⟨g₀, hg₀A, -, hg₀off⟩ := exists_point ∅ (fun _ => 1) gA
    have hcomp : ∀ u : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ u g₀ = 1 := fun u => hg₀off u (by simp)
    have hfacT : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)), S ⊆ T →
        X.whittaker g₀ = X.whittakerArch gA * ∏ u ∈ T, X.whittakerLoc u 1 := by
      intro T hST
      have h := hX.factorizable g₀ T (fun u hu => hST (Finset.mem_coe.mp hu))
        (fun u _ => by rw [hcomp u]; exact one_mem _)
      rw [hg₀A] at h
      simpa [hcomp] using h
    have hprodS : ∏ u ∈ S, X.whittakerLoc u 1 = 1 := Finset.prod_eq_one fun u hu => (hatS u hu).1
    have hWg₀ : X.whittaker g₀ = X.whittakerArch gA := by rw [hfacT S subset_rfl, hprodS, mul_one]

    have hone : ∀ w, w ∉ S → X.whittakerLoc w 1 = 1 := by
      intro w hw
      have h := hfacT (insert w S) (Finset.subset_insert w S)
      rw [Finset.prod_insert hw, hprodS, mul_one, hWg₀] at h
      exact (mul_eq_left₀ hgA).mp h.symm
    refine ⟨?_, fun w hw hlw => ?_⟩
    ·
      intro hform
      have h := hX.whittaker_eq g₀
      rw [hWg₀, hform] at h
      apply hgA
      rw [h]
      simp [whittaker3]
    · have hwS : w ∉ S := fun h => hw ((hS w).mpr h)
      obtain ⟨-, -, hψlev⟩ := LanglandsTunnell.CubicInduction.psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar ψ hψ w
      obtain ⟨hψ0, hψ1⟩ := hψlev hlw
      have key := LanglandsTunnell.CubicInduction.sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn w (psiLoc ψ w) (X.whittakerLoc w)
        (inducedE1 ℚ (inducedCoeff K μ) w) (inducedE2 ℚ (inducedCoeff K μ) w) (inducedE3 ℚ (inducedCoeff K μ) w)
        (hX.spherical w (by exact_mod_cast hwS)) (hX.whittakerLoc_law w) hψ0 hψ1
      refine ⟨hone w hwS, fun n => ?_, fun k₁ k₂ hk => ?_⟩
      · rw [key.1 n, hone w hwS, one_mul]
      · rw [key.2 k₁ k₂ hk, hone w hwS, one_mul]

  have hbad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ w ∈ T, IsBadPlace K μ w → ∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      (∀ w ∈ T, IsBadPlace K μ w → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc w), W ≠ 0 →
        X.whittakerLoc w ∈ gl3CyclicSubspace W) := by
    intro T
    refine ⟨fun w _ hb => (hatS w ((hS w).mp hb)).2.2.1, fun w _ hb => (hatS w ((hS w).mp hb)).2.1⟩
  have hlev' : ∀ w : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ w →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0 := fun w _ => hlev w
  have h1' : ∀ w ∈ S, w ≠ v → X.whittakerLoc w 1 = 1 := fun w hw _ => (hatS w hw).1
  have hadm' : ∀ w ∈ S, ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
      ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
        (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)) :=
    fun w hw => (hatS w hw).2.2.2

  have hEX := LanglandsTunnell.CubicInduction.exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel K hdeg ψ hψ μ hμ hlev' hns D U gen S hS X hX hcont hW hW' hcontW hcontW' c hc hexp hbad
    E hE ν_mul v hv h1' hadm' hcent hSint hSint'
  have hcond1 : ∃ c₀ : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) c₀ :=
    ⟨0, (LanglandsTunnell.TateLocal.hasConductorExponentAt_zero_iff ℚ v).mpr fun u _ => by simp⟩
  have harch1 : ∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧
        (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) ∧
      ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0 := by
    obtain ⟨gInf, σ, hσ, ⟨t, e, hte, he⟩, hnz⟩ := harch
    exact ⟨gInf, σ, hσ, ⟨t, e, hte, by rw [MonoidHom.one_apply, Units.val_one, he]⟩, hnz⟩
  obtain ⟨R₁, R₂, m, hR₁, hR₂, hFE⟩ := hEX 1 hcond1 harch1

  have hψS : ∀ w ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0 := fun w _ => hlev w
  obtain ⟨ε, hε, hB⟩ := LanglandsTunnell.CubicInduction.exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel K hdeg ψ hψ μ hμ hlev' hns D U gen S hS X hX hcont hW hW' hcontW hcontW' c hc hexp hbad
    v hv h1' hadm' hcent hψS hSint hSint' hram (hlev v) E hE ν_mul harch1 R₁ R₂ m hR₁ hR₂ hFE

  have hE0 : (inducedEulerPoly ℚ (inducedCoeff K μ) v) ≠ 0 := by
    intro h
    have h0 := eval_inducedEulerPoly_eq_of_finrank_le_three K hdeg.le (inducedCoeff K μ) v (0 : ℂ)
    rw [h] at h0
    simp at h0
  have hEd0 : (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v) ≠ 0 := by
    intro h
    have h0 := eval_inducedEulerPoly_eq_of_finrank_le_three K hdeg.le (inducedCoeff K μ⁻¹) v (0 : ℂ)
    rw [h] at h0
    simp at h0
  refine ⟨ε, hε, ?_⟩
  exact LanglandsTunnell.CubicInduction.localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq v (X.whittakerLoc v) _ _ ε (inducedLevelAt K μ v) hE0 hEd0 R₁ R₂ m ⟨hR₁, hR₂, hFE⟩ hB

end S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn (solution)
