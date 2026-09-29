-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.hasCubicInductionForm_arch_torusValues_localPackage_bad
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/dc020c2f-52b6-5b0b-8e97-c3866f131433

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem"
p2m_attr_erase "instance" "Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions Deep.NTSupply.instNormalRayClassSubgroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension FLT.SpectralSide.instCompactSpaceMatrix IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap WhittakerBlock.sigmaCompactSpace_adelicGL3 ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP"
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z"
p2m_attr_erase "simp" "AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply"
p2m_attr_erase "simp" "SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right AutomorphicForm.cpowChar_apply_val AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WhittakerModel.archFnAt_zero AutomorphicForm.WhittakerModel.localFnAt_zero AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply MeasureTheory.L2.kernelIntegralLM_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one ArtinL.Abelian.coeff_zero IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf AutomorphicForm.gl3LFactorPoly_def AutomorphicForm.JPSSGL3Factored.mk.injEq AutomorphicForm.coeff_three_gl3LFactorPoly AutomorphicForm.coeff_one_gl3LFactorPoly AutomorphicForm.coeff_zero_gl3LFactorPoly AutomorphicForm.JPSSGL3Factored.mk.sizeOf_spec AutomorphicForm.JPSSConverseFactored.mk.sizeOf_spec AutomorphicForm.coeff_two_gl3LFactorPoly AutomorphicForm.JPSSConverseFactored.mk.injEq AutomorphicForm.coeff_zero_heckeLFactorPoly AutomorphicForm.coeff_two_heckeLFactorPoly AutomorphicForm.heckeLFactorPoly_def AutomorphicForm.HeckeEigensystem.localLFactor_def AutomorphicForm.coeff_one_heckeLFactorPoly AutomorphicForm.satakePow_two"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad.LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker"

section FilingScope

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.addCharLevel TateLocal.HasConductorExponentAt signEpsilon HeckeTate.heckeDatum CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate_apply gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace HasWhittakerMultOne transposeInv3 whittaker3 inducedCoeff psiLoc IsKFinite CubicInductionForm AdelicGL localMaximalCompact3 componentAt3 archComponent3 LocalGL3 IsRamifiedIn IsBadPlace inducedLevelAt congruenceK1 mem_localMaximalCompact3_of_mem_congruenceK1 HasSphericalTorusValuesAt archRoot₁ archRoot₂ archRootSum IsGaugeMajorised3 matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne finMatN mapMatrix_arch_finMatN localToAdelic3 dualWhittakerFn3 weylPrime3 archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove CubicInductionData IsCubicInductionDataOn IsCubicInductionDataOn.exists_cubicInductionForm_toData_eq CubicInductionData.dualWhittaker CubicInductionData.whittaker CubicInductionData.form CubicInductionData.centralChar CubicInductionData.whittakerArch CubicInductionData.whittakerLoc exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace"
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

section RechoiceB

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

private theorem rechooseB
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
      Y.centralChar = X₀.centralChar ∧
      ∀ v ∈ R, (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g,
          Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) ∧ Y.whittakerLoc v ≠ 0 ∧
        (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
          Y.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (Y.whittakerLoc v)) ∧
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
    obtain ⟨Y, hYon, hYreg, hYloc, hYarch, hYcc, hYR⟩ := ih (fun v hv => hR v (Finset.mem_insert_of_mem hv))
    obtain ⟨haS, haram⟩ := hR a (Finset.mem_insert_self a R)
    obtain ⟨W', hW'mem, hW'ne, hW'inv, hW'gate⟩ := hvec a haS haram
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
        exact ⟨hW'inv, hW'ne, hW'gate, exists_isOpen_forall_mul_eq_of_mem_gl3CyclicSubspace (hsm _ haS) hW'mem,
          forall_mem_gl3CyclicSubspace_of_mem (hgen _ haS) hW'mem, hW'mem⟩
      · have hva : v ≠ a := fun e => haR (e ▸ hvR)
        rw [hY'other v hva]
        exact hYR v hvR

end RechoiceB

end LanglandsTunnell.CubicInduction.InductionExistence

end FilingScope

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad.LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem _root_.P2MW.S_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad.solution
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
      ∃ F : CubicInductionForm K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ,
        (F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
          LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
            F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (F.whittakerLoc v)) ∧
        Continuous F.form ∧ Continuous F.whittaker ∧ Continuous F.dualWhittaker ∧
        IsGaugeMajorised3 ℚ F.whittaker ∧ IsGaugeMajorised3 ℚ F.dualWhittaker ∧
        F.whittakerArch = Warch ∧
        F.centralChar = ω ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
          ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
            ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace (F.whittakerLoc v),
              (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
          (∀ z : (v.adicCompletion ℚ)ˣ, ‖((localChar ω v z : ℂˣ) : ℂ)‖ = 1) ∧
          ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
            F.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
              ((localChar ω v t : ℂˣ) : ℂ) * F.whittakerLoc v h) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → HasWhittakerMultOne (psiLoc ψ v) (F.whittakerLoc v)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → IsRamifiedIn K v →
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
              ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → ¬ IsRamifiedIn K v →
          psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ →
          ∃ W ∈ gl3CyclicSubspace (F.whittakerLoc v), IsGL3PsiWhittakerFn (psiLoc ψ v) W ∧ W ≠ 0 ∧
            (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, W (g * k) = W g) ∧
            W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W) := by
  intro D U gen
  classical
  obtain ⟨S, hS, X₀, hX₀, hc₁, hc₂, hc₃, hm₁, hm₂, harch, hone, hgen, hsm, hgood, hvec, hXarch, hXcc, hadm, hcenX,
      hlevX⟩ :=
    LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad K _hdeg ψ _hψ μ
      _hμ _hlev _hns hlev uR aR uC kC huR huC ω hω E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul Warch
      hWarch D U gen
  have hmemS : ∀ v, v ∈ S ↔ IsBadPlace K μ v := fun v => by
    rw [← Finset.mem_coe, hS, Set.mem_setOf_eq]
  obtain ⟨Y, hYon, hYreg, hYloc, hYarch, hYcc, hYR⟩ :=
    InductionExistence.rechooseB K ψ _hψ.continuous μ D U gen S X₀ hX₀ hc₁ hc₂ hc₃ hm₁ hm₂ hgen hsm hvec
      (S.filter fun v => ¬ IsRamifiedIn K v) (fun v hv => Finset.mem_filter.mp hv)

  have hlevel : ∀ v, ¬ IsRamifiedIn K v →
      ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g,
        Y.whittakerLoc v (g * k) = Y.whittakerLoc v g := by
    intro v hram
    by_cases hvS : v ∈ S
    · exact (hYR v (Finset.mem_filter.mpr ⟨hvS, hram⟩)).1
    · intro k hk g
      obtain ⟨hinv, -⟩ := hYon.spherical v (fun hv => hvS (Finset.mem_coe.mp hv))
      exact hinv g k (mem_localMaximalCompact3_of_mem_congruenceK1 (𝓞 ℚ) ℚ v hk)
  have hYbad : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      {v | IsBadPlace K μ v} Y := hS ▸ hYon
  obtain ⟨F, hF⟩ := IsCubicInductionDataOn.exists_cubicInductionForm_toData_eq hYbad hlevel
  have hform : F.form = Y.form := congrArg CubicInductionData.form hF
  have hW : F.whittaker = Y.whittaker := congrArg CubicInductionData.whittaker hF
  have hloc : F.whittakerLoc = Y.whittakerLoc := congrArg CubicInductionData.whittakerLoc hF
  have hWd : F.dualWhittaker = Y.dualWhittaker := congrArg CubicInductionData.dualWhittaker hF
  have hccF : F.centralChar = Y.centralChar := congrArg CubicInductionData.centralChar hF

  have harchY : Y.whittakerArch ≠ 0 := by rw [hYarch]; exact harch
  obtain ⟨gA, hgA⟩ : ∃ x, Y.whittakerArch x ≠ 0 := Function.ne_iff.mp harchY
  have hpt : ∀ v, ∃ x : LocalGL3 v, v ∈ S → Y.whittakerLoc v x ≠ 0 := by
    intro v
    by_cases hvS : v ∈ S
    · by_cases hvr : IsRamifiedIn K v
      · refine ⟨1, fun _ => ?_⟩
        rw [hYloc v (fun hv => (Finset.mem_filter.mp hv).2 hvr), hone v hvS]
        exact one_ne_zero
      · obtain ⟨-, hne, -⟩ := hYR v (Finset.mem_filter.mpr ⟨hvS, hvr⟩)
        obtain ⟨x, hx⟩ : ∃ x, Y.whittakerLoc v x ≠ 0 := Function.ne_iff.mp hne
        exact ⟨x, fun _ => hx⟩
    · exact ⟨1, fun hv => (hvS hv).elim⟩
  choose h hh using hpt
  obtain ⟨g, hga, hgS, hgoff⟩ := InductionExistence.exists_point S h gA
  have hfac := hYon.factorizable g S (fun v hv => Finset.mem_coe.mp hv)
    (fun v hv => by rw [hgoff v hv]; exact one_mem _)
  have hkey : Y.whittaker g ≠ 0 := by
    rw [hfac, hga]
    refine mul_ne_zero hgA (Finset.prod_ne_zero_iff.mpr fun v hv => ?_)
    rw [hgS v hv]
    exact hh v hv
  have hvS_of_bad : ∀ v, IsBadPlace K μ v → v ∈ S := fun v hbad => (hmemS v).mpr hbad
  refine ⟨F, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hkey
    rw [← hW, F.whittaker_eq g, h0]
    simp only [whittaker3, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]
  · intro v hram hlv
    by_cases hvS : v ∈ S
    · rw [hloc]
      exact (hYR v (Finset.mem_filter.mpr ⟨hvS, hram⟩)).2.2.1 hlv
    · rw [hloc, hYloc v (fun hv => hvS (Finset.mem_filter.mp hv).1)]
      exact hgood v hvS
  · rw [hform]
    exact hYreg.1
  · rw [hW]
    exact hYreg.2.1
  · rw [hWd]
    exact hYreg.2.2.1
  · rw [hW]
    exact hYreg.2.2.2.1
  · rw [hWd]
    exact hYreg.2.2.2.2
  · have hA : F.whittakerArch = Y.whittakerArch := congrArg CubicInductionData.whittakerArch hF
    exact hA.trans (hYarch.trans hXarch)
  ·
    exact hccF.trans (hYcc.trans hXcc)
  ·
    intro v hbad Uv hUv
    have hvS := hvS_of_bad v hbad
    by_cases hram : IsRamifiedIn K v
    · rw [hloc, hYloc v (fun hv => (Finset.mem_filter.mp hv).2 hram)]
      exact hadm v hvS Uv hUv
    · rw [hloc]
      exact InductionExistence.admissible_of_mem_gl3CyclicSubspace (hadm v hvS)
        (hYR v (Finset.mem_filter.mpr ⟨hvS, hram⟩)).2.2.2.2.2 Uv hUv
  ·
    intro v hbad
    have hvS := hvS_of_bad v hbad
    refine ⟨(hcenX v hvS).1, ?_⟩
    by_cases hram : IsRamifiedIn K v
    · rw [hloc, hYloc v (fun hv => (Finset.mem_filter.mp hv).2 hram)]
      exact (hcenX v hvS).2
    · rw [hloc]
      exact InductionExistence.central_of_mem_gl3CyclicSubspace (fun t => ((localChar ω v t : ℂˣ) : ℂ))
        (hcenX v hvS).2 (hYR v (Finset.mem_filter.mpr ⟨hvS, hram⟩)).2.2.2.2.2
  ·
    intro v _
    exact F.multOne v
  ·
    intro v hbad hram
    have hvS := hvS_of_bad v hbad
    rw [hloc, hYloc v (fun hv => (Finset.mem_filter.mp hv).2 hram)]
    exact hlevX v hvS hram
  ·
    intro v hbad hram _hψv
    have hvS := hvS_of_bad v hbad
    obtain ⟨h1, htor⟩ := (hYR v (Finset.mem_filter.mpr ⟨hvS, hram⟩)).2.2.1 (hlev v)
    refine ⟨F.whittakerLoc v, ?_, F.whittakerLoc_law v, ?_, F.levelInvariant v hram, ?_, ?_⟩
    · refine Submodule.subset_span ⟨1, ?_⟩
      funext x
      simp [gl3AmbientRightTranslate_apply]
    · rw [hloc]
      exact (hYR v (Finset.mem_filter.mpr ⟨hvS, hram⟩)).2.1
    · rw [hloc]; exact h1
    · rw [hloc]; exact htor
  · intro _
    refine ⟨fun v _ hbad => ?_, fun v _ hbad => ?_⟩
    · have hvS := hvS_of_bad v hbad
      by_cases hram : IsRamifiedIn K v
      · rw [hloc, hYloc v (fun hv => (Finset.mem_filter.mp hv).2 hram)]
        exact hsm v hvS
      · rw [hloc]
        exact (hYR v (Finset.mem_filter.mpr ⟨hvS, hram⟩)).2.2.2.1
    · have hvS := hvS_of_bad v hbad
      by_cases hram : IsRamifiedIn K v
      · rw [hloc, hYloc v (fun hv => (Finset.mem_filter.mp hv).2 hram)]
        exact hgen v hvS
      · rw [hloc]
        exact (hYR v (Finset.mem_filter.mpr ⟨hvS, hram⟩)).2.2.2.2.1

end S_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad (solution)
