-- Prove2me | solution 1 for LanglandsTunnell.exists_forall_isNicePinned_twistedDatum_formalBaseChange_archOfParam_of_whittakerCoefficient_fibre_eq_archW_of_not_agreesAwayFromFinite_twist_of_isCasimirEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/cf557d31-c324-5c45-a346-7ed928a167bb

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_LanglandsTunnell_exists_isNicePinned_twistedDatum_formalBaseChange_archOfParam_superset_generic_of_whittaker_factorization_of_norm_eq_one_of_summable_of_localSpaceAt
import Theorems.Thm_LanglandsTunnell_exists_agreesAwayFromFinite_isArithGenuineCuspRealizable_twist_whittaker_link_localSpaceAt_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW
import Theorems.Thm_AutomorphicForm_summable_norm_a_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
import Theorems.Thm_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq
import Theorems.Thm_LanglandsTunnell_Converse_isNicePinned_twistedDatum_iff_of_forall_notMem_a_eq_b_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_forall_isNicePinned_twistedDatum_formalBaseChange_archOfParam_of_whittakerCoefficient_fibre_eq_archW_of_not_agreesAwayFromFinite_twist_of_isCasimirEigen
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SpectralSide.instCompactSpaceMatrix LocalGL2.Kirillov.fintype_Qm"
p2m_attr_erase "instance" "LocalGL2.Kirillov.fintype_Ch LocalGL2.Kirillov.addCommGroup_Ch LocalGL2.Kirillov.finite_Qm LocalGL2.Kirillov.addCommGroup_additive_Qm LocalGL2.Kirillov.decidableEq_Ch LocalGL2.Kirillov.finite_additive_Qm IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply"
p2m_attr_erase "simp" "IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun"
p2m_attr_erase "simp" "SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply LanglandsTunnell.CubicInduction.CubicInductionForm.mk.injEq LanglandsTunnell.CubicInduction.CubicInductionForm.mk.sizeOf_spec LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe LanglandsTunnell.CubicInduction.coe_diagUnitGL2"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.RankinSelberg.rsGlobalIntegral_zero_left LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"
p2m_attr_erase "simp" "AutomorphicForm.gl2Weyl_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.mem_sigmaCentralizer_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.CubicInductionData.mk.sizeOf_spec LanglandsTunnell.CubicInduction.CubicInductionData.mk.injEq FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply"
p2m_attr_erase "simp" "NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply LocalGL2.Kirillov.zG_coe LocalGL2.Kirillov.wG_coe LocalGL2.Kirillov.dg_coe LocalGL2.Kirillov.rT_apply LocalGL2.Kirillov.rT_one Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star AutomorphicForm.mem_inducedSectionSubmodule_iff LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul MeasureTheory.L2.kernelIntegralLM_apply"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ArtinL.Abelian.coeff_zero IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf AutomorphicForm.gl3LFactorPoly_def AutomorphicForm.JPSSGL3Factored.mk.injEq AutomorphicForm.coeff_three_gl3LFactorPoly AutomorphicForm.coeff_one_gl3LFactorPoly AutomorphicForm.coeff_zero_gl3LFactorPoly AutomorphicForm.JPSSGL3Factored.mk.sizeOf_spec AutomorphicForm.JPSSConverseFactored.mk.sizeOf_spec AutomorphicForm.coeff_two_gl3LFactorPoly AutomorphicForm.JPSSConverseFactored.mk.injEq AutomorphicForm.coeff_zero_heckeLFactorPoly AutomorphicForm.coeff_two_heckeLFactorPoly AutomorphicForm.heckeLFactorPoly_def AutomorphicForm.HeckeEigensystem.localLFactor_def AutomorphicForm.coeff_one_heckeLFactorPoly AutomorphicForm.satakePow_two AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice"
p2m_attr_erase "simp" "AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

namespace Ws23
namespace N4R
open AutomorphicForm

theorem agrees_symm {F : Type} [Field F] [NumberField F] {X Y : HeckeEigensystem F ℂ}
    (h : X.AgreesAwayFromFinite Y) : Y.AgreesAwayFromFinite X := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨((hS v hv).1).symm, ((hS v hv).2).symm⟩⟩

theorem agrees_trans {F : Type} [Field F] [NumberField F] {X Y Z : HeckeEigensystem F ℂ}
    (h : X.AgreesAwayFromFinite Y) (h' : Y.AgreesAwayFromFinite Z) : X.AgreesAwayFromFinite Z := by
  classical
  obtain ⟨S, hS⟩ := h
  obtain ⟨S', hS'⟩ := h'
  refine ⟨S ∪ S', fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  exact ⟨(hS v hv.1).1.trans (hS' v hv.2).1, (hS v hv.1).2.trans (hS' v hv.2).2⟩

theorem agrees_twist {F : Type} [Field F] [NumberField F] {X Y : HeckeEigensystem F ℂ}
    (h : X.AgreesAwayFromFinite Y) (χ : HeightOneSpectrum (𝓞 F) → ℂ) :
    (X.twist χ).AgreesAwayFromFinite (Y.twist χ) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun v hv => ?_⟩
  simp [HeckeEigensystem.twist_a, HeckeEigensystem.twist_b, (hS v hv).1, (hS v hv).2]

theorem not_agrees_twist_of_not_agrees {Φ : HeckeEigensystem ℚ ℂ} (χ c₀ : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (hc₀ : ∀ v, c₀ v ≠ 0)
    (hnd : ¬ HeckeEigensystem.AgreesAwayFromFinite Φ (Φ.twist χ)) :
    ¬ HeckeEigensystem.AgreesAwayFromFinite (Φ.twist c₀) ((Φ.twist c₀).twist χ) := by
  rintro ⟨S, hS⟩
  apply hnd
  refine ⟨S, fun v hv => ?_⟩
  obtain ⟨ha, hb⟩ := hS v hv
  simp only [HeckeEigensystem.twist_a, HeckeEigensystem.twist_b] at ha hb ⊢
  refine ⟨?_, ?_⟩
  · have : c₀ v * Φ.a v = c₀ v * (χ v * Φ.a v) := by rw [ha]; ring
    exact mul_left_cancel₀ (hc₀ v) this
  · have h2 : c₀ v ^ 2 ≠ 0 := pow_ne_zero 2 (hc₀ v)
    have : c₀ v ^ 2 * Φ.b v = c₀ v ^ 2 * (χ v ^ 2 * Φ.b v) := by rw [hb]; ring
    exact mul_left_cancel₀ h2 this

theorem absNorm_rpow_neg_half_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) :
    (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  have h0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  exact_mod_cast (Real.rpow_pos_of_pos h0 (-(1 / 2 : ℝ))).ne'

end Ws23.N4R

theorem Ws23.N4R.formalBaseChange_twist_half_eq_of_eq_under
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ Φ' : HeckeEigensystem ℚ ℂ) (𝔓 : HeightOneSpectrum (𝓞 K))
    (h : Φ'.a (𝔓.under (𝓞 ℚ)) = Φ.a (𝔓.under (𝓞 ℚ)) ∧ Φ'.b (𝔓.under (𝓞 ℚ)) = Φ.b (𝔓.under (𝓞 ℚ))) :
    (formalBaseChange ℚ K (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))).a 𝔓 =
      ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).a 𝔓 ∧
    (formalBaseChange ℚ K (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))).b 𝔓 =
      ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b 𝔓 := by
  obtain ⟨h1, h2⟩ := LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq ℚ K Φ' (1 / 2 : ℝ) 𝔓
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · simp only [HeckeEigensystem.twist_a, AutomorphicForm.formalBaseChange_a, h.1, h.2]
  · simp only [HeckeEigensystem.twist_b, AutomorphicForm.formalBaseChange_b, h.2]

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc' : 0 < c') (hd₁' : 0 < d₁') (hd' : d₁' < d₂')
    (hcov' : CoversModCentre ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂'))
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (hcuspK : ∃ Ψ : HeckeEigensystem K ℂ, Ψ.AgreesAwayFromFinite (formalBaseChange ℚ K Φ) ∧
      IsArithGenuineCuspRealizable K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        Ψ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (_hχ2 : ∀ v ∉ S₀, χ v * χ v = 1)
    (_hlink : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₀ →
      (χ v = 1 ↔ ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) = v →
        (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 2))
    (_hnd : ¬ HeckeEigensystem.AgreesAwayFromFinite Φ (Φ.twist χ))
    (P : RealArchParam) (archCQ : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dRQ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dCQ : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archCQ w hw))
    (hWFQ : ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂')
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂')
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archCQ dRQ dCQ g * z))
    (hWT : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (dRQ w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * (dRQ w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dRQ w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dRQ w hw).W g ≠ 0)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)))
    (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1))
    (hP0 : (RealArchParam.centralExponent P).re = 0) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
      (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (A Ad : (↥S → ℤ) → ℂ),
      (∀ v ∈ S, Continuous ⇑(epsS v)) ∧
      IsAdmissibleTwist K ω ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ω v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) = ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal),
        IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent ((archOfParamR K P w hw).centralSign.val : ℤ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex),
        IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist) ∧
      (∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C) ∧
      (∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0) ∧
      A ≠ 0 ∧
      (∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
        (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
          localChar μ v u * epsS v u = 1) →
        ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
          (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
          (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
          (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
          (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
          (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
          IsNicePinned
            (twistedDatum K ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) S (archOfParamR K P) (archOfParamC K P) μ uR aR uC kC)
            (sPart K S A μ) (sPartDual K S Ad μ)
            (pinnedRootNumber K ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) μ S (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
            (finiteConductor K μ S)) := by
  classical

  obtain ⟨Φ', S, hagr, hΦa, hb, hlink⟩ :=
    LanglandsTunnell.exists_agreesAwayFromFinite_isArithGenuineCuspRealizable_twist_whittaker_link_localSpaceAt_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
      c' u' d₁' d₂' T' hc' hd₁' hd' hcov' Φ P archCQ dRQ dCQ hWFQ hWT hDE hnv hgen htype hP0

  have ha := AutomorphicForm.summable_norm_a_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
    (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) hΦa S hb

  obtain ⟨Tq₀, ω, hω, hωT₀, hωR, hωC⟩ :=
    LanglandsTunnell.exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW
      K c' u' d₁' d₂' T' hc' hd₁' hd' hcov' Φ P archCQ dRQ dCQ hWFQ hP0

  obtain ⟨Sagr, hSagr⟩ := hagr
  have hagr' : Φ'.AgreesAwayFromFinite Φ := ⟨Sagr, hSagr⟩
  have htab : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Sagr →
      (formalBaseChange ℚ K (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))).a 𝔓 =
        ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).a 𝔓 ∧
      (formalBaseChange ℚ K (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))).b 𝔓 =
        ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b 𝔓 :=
    fun 𝔓 h𝔓 => Ws23.N4R.formalBaseChange_twist_half_eq_of_eq_under K Φ Φ' 𝔓 (hSagr _ h𝔓)
  have hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq₀ ∪ Sagr →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))).b 𝔓 := by
    intro 𝔓 h
    rw [Finset.mem_union, not_or] at h
    exact ⟨(hωT₀ 𝔓 h.1).1, (hωT₀ 𝔓 h.1).2.trans ((htab 𝔓 h.2).2).symm⟩

  have hnd' : ¬ HeckeEigensystem.AgreesAwayFromFinite Φ' (Φ'.twist χ) := fun h =>
    _hnd (Ws23.N4R.agrees_trans (Ws23.N4R.agrees_symm hagr')
      (Ws23.N4R.agrees_trans h (Ws23.N4R.agrees_twist hagr' χ)))
  have hnda := Ws23.N4R.not_agrees_twist_of_not_agrees (Φ := Φ') χ (fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    (fun v => Ws23.N4R.absNorm_rpow_neg_half_ne_zero v) hnd'

  obtain ⟨SK, epsS, A, Ad, hTq, -, -, -, -, -, hepsS, hbd, hsupp, hA0, hnice⟩ :=
    LanglandsTunnell.exists_isNicePinned_twistedDatum_formalBaseChange_archOfParam_superset_generic_of_whittaker_factorization_of_norm_eq_one_of_summable_of_localSpaceAt
      K hdeg (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) hΦa S hb ha P S (Finset.Subset.refl S) hlink S₀ χ _hχ2 _hlink hnda
      (Tq₀ ∪ Sagr) ω hω hωT

  have hXY : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      (formalBaseChange ℚ K (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))).a v =
        ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).a v ∧
      (formalBaseChange ℚ K (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))).b v =
        ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v :=
    fun v hv => htab v (fun h => hv (hTq v (Finset.mem_union_right _ h)))

  refine ⟨SK, epsS, ω, A, Ad, hepsS, hω, ?_, ?_, hωR, hωC, hbd, hsupp, hA0, ?_⟩
  · intro v hv
    exact (hωT₀ v (fun h => hv (hTq v (Finset.mem_union_left _ h)))).1
  · intro v hv
    exact (hωT₀ v (fun h => hv (hTq v (Finset.mem_union_left _ h)))).2
  · intro μ hμ hεμ uR aR uC kC hR hC
    exact (LanglandsTunnell.Converse.isNicePinned_twistedDatum_iff_of_forall_notMem_a_eq_b_eq K _ _ SK hXY
      (archOfParamR K P) (archOfParamC K P) μ uR aR uC kC _ _ _).mp (hnice μ hμ hεμ uR aR uC kC hR hC)

end S_LanglandsTunnell_exists_forall_isNicePinned_twistedDatum_formalBaseChange_archOfParam_of_whittakerCoefficient_fibre_eq_archW_of_not_agreesAwayFromFinite_twist_of_isCasimirEigen
end P2MW
export P2MW.S_LanglandsTunnell_exists_forall_isNicePinned_twistedDatum_formalBaseChange_archOfParam_of_whittakerCoefficient_fibre_eq_archW_of_not_agreesAwayFromFinite_twist_of_isCasimirEigen (solution)
