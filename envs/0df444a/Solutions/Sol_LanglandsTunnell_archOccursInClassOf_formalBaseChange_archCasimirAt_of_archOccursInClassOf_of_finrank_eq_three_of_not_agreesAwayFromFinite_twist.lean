-- Prove2me | solution 1 for LanglandsTunnell.archOccursInClassOf_formalBaseChange_archCasimirAt_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/dfd3a552-6949-5b72-8929-de0f6f407bab

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_archCasimirAt_iff_of_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
import Theorems.Thm_AutomorphicForm_coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isArithGenuineCuspRealizable_twist_rpow_absNorm
import Theorems.Thm_LanglandsTunnell_exists_realArchParam_archDatumR_whittakerCoefficient_fibre_eq_isCasimirEigen_of_archOccursInClassOf_rat
import Theorems.Thm_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
import Theorems.Thm_AutomorphicForm_not_agreesAwayFromFinite_twist_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_exists_forall_isNicePinned_twistedDatum_formalBaseChange_archOfParam_of_whittakerCoefficient_fibre_eq_archW_of_not_agreesAwayFromFinite_twist_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_archOfParam_of_forall_isNicePinned
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_twist_W_eq_abs_det_rpow_mul
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_twist_of_archOccursInClassOf_rat
import Theorems.Thm_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_archOccursInClassOf_formalBaseChange_archCasimirAt_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SpectralSide.instCompactSpaceMatrix LocalGL2.Kirillov.fintype_Qm"
p2m_attr_erase "instance" "LocalGL2.Kirillov.fintype_Ch LocalGL2.Kirillov.addCommGroup_Ch LocalGL2.Kirillov.finite_Qm LocalGL2.Kirillov.addCommGroup_additive_Qm LocalGL2.Kirillov.decidableEq_Ch LocalGL2.Kirillov.finite_additive_Qm IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.mem_borelSubgroup_iff"
p2m_attr_erase "simp" "AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.mem_inducedSectionSubmodule_iff LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec LanglandsTunnell.RankinSelberg.mem_primeFibre AutomorphicForm.WhittakerModel.archFnAt_zero AutomorphicForm.WhittakerModel.localFnAt_zero M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply LanglandsTunnell.CubicInduction.CubicInductionForm.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.CubicInductionForm.mk.sizeOf_spec LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe LanglandsTunnell.RankinSelberg.rsGlobalIntegral_zero_left LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral AutomorphicForm.gl2Weyl_val LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.CubicInductionData.mk.sizeOf_spec LanglandsTunnell.CubicInduction.CubicInductionData.mk.injEq FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply"
p2m_attr_erase "simp" "Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply LocalGL2.Kirillov.zG_coe LocalGL2.Kirillov.wG_coe LocalGL2.Kirillov.dg_coe LocalGL2.Kirillov.rT_apply LocalGL2.Kirillov.rT_one Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe"
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul MeasureTheory.L2.kernelIntegralLM_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ArtinL.Abelian.coeff_zero IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf AutomorphicForm.gl3LFactorPoly_def AutomorphicForm.JPSSGL3Factored.mk.injEq AutomorphicForm.coeff_three_gl3LFactorPoly AutomorphicForm.coeff_one_gl3LFactorPoly AutomorphicForm.coeff_zero_gl3LFactorPoly AutomorphicForm.JPSSGL3Factored.mk.sizeOf_spec AutomorphicForm.JPSSConverseFactored.mk.sizeOf_spec AutomorphicForm.coeff_two_gl3LFactorPoly AutomorphicForm.JPSSConverseFactored.mk.injEq AutomorphicForm.coeff_zero_heckeLFactorPoly AutomorphicForm.coeff_two_heckeLFactorPoly AutomorphicForm.heckeLFactorPoly_def"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.localLFactor_def AutomorphicForm.coeff_one_heckeLFactorPoly AutomorphicForm.satakePow_two AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.bcWeight_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

namespace Ws23
namespace S2R
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

theorem occ_of_agrees {F : Type} [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    {X Y : HeckeEigensystem F ℂ} (p : (AdelicGL2 (𝓞 F) F → ℂ) → Prop)
    (h : ArchOccursInClassOf F D X p) (hXY : X.AgreesAwayFromFinite Y) : ArchOccursInClassOf F D Y p := by
  obtain ⟨X', hX', R, hR, hp⟩ := h
  exact ⟨X', agrees_trans hX' hXY, R, hR, hp⟩

open LanglandsTunnell LanglandsTunnell.RealArchParam in
theorem centralExponent_twist_re_eq_zero (P : RealArchParam) (t : ℝ) (ht : t = -(centralExponent P).re / 2) :
    (centralExponent (P.twist (t : ℂ) 0)).re = 0 := by
  have : centralExponent (P.twist (t : ℂ) 0) = centralExponent P + 2 * (t : ℂ) := by
    cases P <;> simp [RealArchParam.twist, centralExponent] <;> ring
  rw [this, ht]; simp; ring

open LanglandsTunnell LanglandsTunnell.RealArchParam in
theorem laplaceEigenvalue_twist (P : RealArchParam) (t : ℝ) : laplaceEigenvalue (P.twist (t : ℂ) 0) = laplaceEigenvalue P := by
  cases P <;> simp [RealArchParam.twist, laplaceEigenvalue]

open LanglandsTunnell in
theorem k0_twist (P : RealArchParam) (t : ℝ) : (match (generalizing := false) (P.twist (t : ℂ) 0) with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) = (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) := by
  cases P <;> simp [RealArchParam.twist]

open LanglandsTunnell in
theorem hgen_twist (P : RealArchParam) (t : ℝ) (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))) : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P.twist (t : ℂ) 0 = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) := by
  cases P with
  | principal v₁ b₁ v₂ b₂ =>
    intro u₁ u₂ a₁ a₂ h p hp hu
    simp only [RealArchParam.twist, RealArchParam.principal.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    have hu' : v₁ - v₂ = (p : ℂ) := by linear_combination hu
    simpa using hgen v₁ v₂ b₁ b₂ rfl p hp hu'
  | discrete u₀ k hk =>
    intro u₁ u₂ a₁ a₂ h; simp [RealArchParam.twist] at h

open LanglandsTunnell in
theorem htype_twist (P : RealArchParam) (t : ℝ) (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)) : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P.twist (t : ℂ) 0 = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) := by
  cases P with
  | principal v₁ b₁ v₂ b₂ =>
    intro u₁ u₂ a₁ a₂ h
    simp only [RealArchParam.twist, RealArchParam.principal.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have := htype v₁ v₂ b₁ b₂ rfl
    have e : u₁ - u₂ = v₁ - v₂ := by rw [← h1, ← h3]; ring
    rwa [e]
  | discrete u₀ k hk =>
    intro u₁ u₂ a₁ a₂ h; simp [RealArchParam.twist] at h

theorem AutomorphicForm.SiegelCovering.pos_of_coversModCentre_iUnion_centreCutSiegelSet
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) : 0 < d₂ := by
  obtain ⟨γ, z, hmem⟩ := hcov 1
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨x, -, g, hg, -⟩ := hmem
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have h4 := (mem_centreCutSiegelSet_iff.mp hg).2.2.2 v₀
  exact lt_of_lt_of_le (NumberField.AdelicVolume.archDetNorm_pos v₀ g) h4.2

end Ws23.S2R

open AutomorphicForm in
theorem Ws23.S2R.not_agrees_twist_of_not_agrees {Φ : HeckeEigensystem ℚ ℂ} (χ c₀ : HeightOneSpectrum (𝓞 ℚ) → ℂ)
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

set_option maxHeartbeats 6400000 in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd' : d₁' < d₂')
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
    (_hnd : ¬ HeckeEigensystem.AgreesAwayFromFinite Φ (Φ.twist χ)) :
    ∀ w : InfinitePlace K, ∀ hw : w.IsReal, ∀ n : ℤ, ∀ lam : ℂ,
      ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
          (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
              HasArchCharacterAt₀ ℚ w' ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw') (norm_ringEquivRealOfIsReal hw'))) φ) ∧
            IsArchSmoothAt Rat.isReal_infinitePlace φ ∧ archCasimirAt Rat.isReal_infinitePlace φ = (lam) • φ) →
        ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
          (fun φ => HasArchCharacterAt₀ K w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ)   := by
  intro w hw n lam hQ
  classical

  have hQ1 : ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
      (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
            IsArchSmoothAt Rat.isReal_infinitePlace φ ∧ archCasimirAt Rat.isReal_infinitePlace φ = (lam) • φ) :=
    hQ.mono fun φ hφ => ⟨hφ.1 _ _, hφ.2.1, hφ.2.2⟩

  obtain ⟨P, archCQ, dRQ, dCQ, hWFQ, hWT, hCE, hnvQ, hgen, htype, hk0Q⟩ :=
    LanglandsTunnell.exists_realArchParam_archDatumR_whittakerCoefficient_fibre_eq_isCasimirEigen_of_archOccursInClassOf_rat c' u' d₁' d₂' T' hd' hcov' Φ (hQ.mono fun _ _ => trivial)
  obtain ⟨hWcQ, hWfinQ, hWsQ, hWΩQ⟩ :=
    LanglandsTunnell.Converse.continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen ℚ (fun _ _ => P) archCQ dRQ dCQ Rat.infinitePlace Rat.isReal_infinitePlace (hCE _ _)

  obtain ⟨lamQ, rigQ, smoQ⟩ :=
    AutomorphicForm.exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre ℚ c' u' d₁' d₂' T' hd' hcov' Φ Rat.infinitePlace Rat.isReal_infinitePlace
  obtain ⟨m, hm⟩ := LanglandsTunnell.exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq ℚ c' u' d₁' d₂' T' hd' hcov' Φ
    Rat.infinitePlace Rat.isReal_infinitePlace P _ hWcQ hWfinQ hWsQ hWΩQ hWFQ
  have hevQ : laplaceEigenvalue P = lamQ := rigQ m _ hm
  have hminQ := (smoQ _ hk0Q).mono fun φ hφ => (⟨hφ.1, hφ.2.1, by rw [hevQ]; exact hφ.2.2.2⟩ :
      HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧ IsArchSmoothAt Rat.isReal_infinitePlace φ ∧
        archCasimirAt Rat.isReal_infinitePlace φ = (laplaceEigenvalue P) • φ)
  have hT := (LanglandsTunnell.archOccursInClassOf_archCasimirAt_iff_of_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre ℚ c' u' d₁' d₂' T' hd' hcov' Φ
    Rat.infinitePlace Rat.isReal_infinitePlace P hminQ n lam).mp hQ1

  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = -(RealArchParam.centralExponent P).re / 2 := ⟨_, rfl⟩
  obtain ⟨D₁, hW₁, hCE₁f, hWT₁f, hnv₁f⟩ := LanglandsTunnell.Converse.ArchDatumR.exists_twist_W_eq_abs_det_rpow_mul P (dRQ Rat.infinitePlace Rat.isReal_infinitePlace) t
  have hCE₁ := hCE₁f (hCE _ _)
  have hWT₁ := hWT₁f _ (hWT _ _)
  have hnv₁ := hnv₁f (hnvQ _ _)
  have hP0₁ := Ws23.S2R.centralExponent_twist_re_eq_zero P t ht
  have hgen₁ := Ws23.S2R.hgen_twist P t hgen
  have htype₁ := Ws23.S2R.htype_twist P t htype
  have hWT₁' : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        ((fun (_ : InfinitePlace ℚ) (_ : _) => D₁) w' hw').W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) (P.twist (t : ℂ) 0) with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * ((fun (_ : InfinitePlace ℚ) (_ : _) => D₁) w' hw').W (x : Matrix (Fin 2) (Fin 2) ℝ)) := by
    intro w' hw'
    rw [Ws23.S2R.k0_twist P t]
    exact hWT₁

  obtain ⟨Φ', hΦ'agr, R', hR', -⟩ := hQ
  have hc' : 0 < c' := lt_of_not_ge fun h =>
    AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre ℚ c' u' d₁' d₂' T' h hd' hcov' Φ' ⟨R', hR'⟩
  have hd₂' : 0 < d₂' := Ws23.S2R.AutomorphicForm.SiegelCovering.pos_of_coversModCentre_iUnion_centreCutSiegelSet ℚ c' u' d₁' d₂' T' hcov'
  have hdp' : 0 < max d₁' (d₂' / 2) := lt_max_of_lt_right (half_pos hd₂')
  have hdp₂' : max d₁' (d₂' / 2) < d₂' := max_lt hd' (half_lt_self hd₂')
  have hle' : d₁' ≤ max d₁' (d₂' / 2) := le_max_left _ _
  obtain ⟨hcovp', htr'⟩ := AutomorphicForm.coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le ℚ c' u' d₁' d₂' (max d₁' (d₂' / 2)) T'
    hc' hdp' hdp₂' hle' hcov' Φ ⟨Φ', hΦ'agr, R', hR', trivial⟩
  have hWFQp := (htr' _).mp hWFQ
  have hWFQ₁ := LanglandsTunnell.archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_twist_of_archOccursInClassOf_rat c' u' (max d₁' (d₂' / 2)) d₂' T' hdp' Φ P archCQ dRQ dCQ t (fun _ _ => D₁)
    (fun w' hw' => by
      have : w' = Rat.infinitePlace := Subsingleton.elim _ _
      subst this
      exact hW₁) hWFQp

  obtain ⟨Ψ, hΨagr, hΨreal⟩ := hcuspK
  have hc : 0 < c := lt_of_not_ge fun h =>
    AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre K c u d₁ d₂ T h hd hcov Ψ hΨreal
  have hd₂ : 0 < d₂ := Ws23.S2R.AutomorphicForm.SiegelCovering.pos_of_coversModCentre_iUnion_centreCutSiegelSet K c u d₁ d₂ T hcov
  have hdp : 0 < max d₁ (d₂ / 2) := lt_max_of_lt_right (half_pos hd₂)
  have hdp₂ : max d₁ (d₂ / 2) < d₂ := max_lt hd (half_lt_self hd₂)
  have hle : d₁ ≤ max d₁ (d₂ / 2) := le_max_left _ _
  have hΘK : ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ) (fun _ => True) := by
    obtain ⟨R, hR⟩ := hΨreal
    exact ⟨Ψ, hΨagr, R, hR, trivial⟩
  obtain ⟨hcovp, htr⟩ := AutomorphicForm.coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le K c u d₁ d₂ (max d₁ (d₂ / 2)) T
    hc hdp hdp₂ hle hcov (formalBaseChange ℚ K Φ) hΘK
  obtain ⟨-, hΨrealp⟩ := AutomorphicForm.coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre K c u d₁ d₂ (max d₁ (d₂ / 2)) T
    hle hdp₂ hcov Ψ hΨreal

  have hΨ₁real := AutomorphicForm.isArithGenuineCuspRealizable_twist_rpow_absNorm K c u (max d₁ (d₂ / 2)) d₂ T hdp Ψ hΨrealp t
  have hBC := LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite ℚ K Φ t
  have hΨ₁agr : (Ψ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).AgreesAwayFromFinite
      (formalBaseChange ℚ K (Φ.twist (fun v : HeightOneSpectrum (𝓞 ℚ) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))) :=
    Ws23.S2R.agrees_trans (Ws23.S2R.agrees_twist hΨagr _) (Ws23.S2R.agrees_symm hBC)
  have hnonEisK := AutomorphicForm.not_agreesAwayFromFinite_twist_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre K c u (max d₁ (d₂ / 2)) d₂ T hdp₂ hcovp
    (formalBaseChange ℚ K (Φ.twist (fun v : HeightOneSpectrum (𝓞 ℚ) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))) ⟨_, hΨ₁agr, hΨ₁real⟩

  obtain ⟨S, epsS, ω, A, Ad, hepsS, hω, hωunr, hωb, hωR, hωC, hbd, hsupp, hA0, hnice⟩ :=
    LanglandsTunnell.exists_forall_isNicePinned_twistedDatum_formalBaseChange_archOfParam_of_whittakerCoefficient_fibre_eq_archW_of_not_agreesAwayFromFinite_twist_of_isCasimirEigen K hdeg c' u' (max d₁' (d₂' / 2)) d₂' T' hc' hdp' hdp₂' hcovp' c u (max d₁ (d₂ / 2)) d₂ T hdp₂ hcovp
      (Φ.twist (fun v : HeightOneSpectrum (𝓞 ℚ) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))) ⟨_, hΨ₁agr, hΨ₁real⟩
      S₀ χ _hχ2 _hlink
      (Ws23.S2R.not_agrees_twist_of_not_agrees χ _
        (fun v => by
          have h0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
          exact_mod_cast (Real.rpow_pos_of_pos h0 (-t)).ne')
        _hnd)
      (P.twist (t : ℂ) 0) archCQ (fun _ _ => D₁) dCQ hWFQ₁ hWT₁' (fun _ _ => hCE₁) (fun _ _ => hnv₁) hgen₁ htype₁ hP0₁

  obtain ⟨⟨dCK, hWFK⟩, hkK⟩ :=
    LanglandsTunnell.archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_archOfParam_of_forall_isNicePinned K c u (max d₁ (d₂ / 2)) d₂ T hc hdp
      (formalBaseChange ℚ K (Φ.twist (fun v : HeightOneSpectrum (𝓞 ℚ) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))) S (P.twist (t : ℂ) 0) epsS hepsS ω hω hωunr hωb hωR hωC A Ad hbd hsupp hA0 hnice
      (fun μ₁ μ₂ => hnonEisK _ _ μ₁ μ₂)
      D₁ hnv₁ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) hWT₁
  obtain ⟨hWcK, hWfinK, hWsK, hWΩK⟩ :=
    LanglandsTunnell.Converse.continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen K (archOfParamR K (P.twist (t : ℂ) 0)) (archOfParamC K (P.twist (t : ℂ) 0))
      (fun _ _ => D₁) dCK w hw hCE₁

  obtain ⟨lamK, rigK, smoK⟩ := AutomorphicForm.exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre K c u (max d₁ (d₂ / 2)) d₂ T hdp₂ hcovp (formalBaseChange ℚ K (Φ.twist (fun v : HeightOneSpectrum (𝓞 ℚ) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))) w hw
  obtain ⟨m', hm'⟩ := LanglandsTunnell.exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq K c u (max d₁ (d₂ / 2)) d₂ T hdp₂ hcovp (formalBaseChange ℚ K (Φ.twist (fun v : HeightOneSpectrum (𝓞 ℚ) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))) w hw (P.twist (t : ℂ) 0) _ hWcK hWfinK hWsK hWΩK hWFK
  have hevK : laplaceEigenvalue P = lamK := by
    rw [← Ws23.S2R.laplaceEigenvalue_twist P t]; exact rigK m' _ hm'
  have hminK := (smoK _ (hkK w hw)).mono fun φ hφ => (⟨hφ.1, hφ.2.1, by rw [hevK]; exact hφ.2.2.2⟩ :
      HasArchCharacterAt₀ K w ((archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (laplaceEigenvalue P) • φ)
  have occ₁ := (LanglandsTunnell.archOccursInClassOf_archCasimirAt_iff_of_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre K c u (max d₁ (d₂ / 2)) d₂ T hdp₂ hcovp (formalBaseChange ℚ K (Φ.twist (fun v : HeightOneSpectrum (𝓞 ℚ) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))) w hw P hminK n lam).mpr hT

  have occ₂ := Ws23.S2R.occ_of_agrees _ _ occ₁ hBC
  have occ₃ := (AutomorphicForm.archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm K c u (max d₁ (d₂ / 2)) d₂ T hdp (formalBaseChange ℚ K Φ) w hw n lam t).mpr occ₂
  exact (htr _).mpr occ₃

#print axioms solution

end S_LanglandsTunnell_archOccursInClassOf_formalBaseChange_archCasimirAt_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
end P2MW
export P2MW.S_LanglandsTunnell_archOccursInClassOf_formalBaseChange_archCasimirAt_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist (solution)
