-- Prove2me | solution 1 for LanglandsTunnell.archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/14c23960-59cf-5fb6-b829-4cf23a739a71

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_LanglandsTunnell_centralChar_archCentralUnit_eq_of_agreesAwayFromFinite_formalBaseChange_of_isReal
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_iff_archCasimirAt_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_formalBaseChange_archCasimirAt_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex M4aHerbrand.isMulCommutative_ideleClassGroup"
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal"
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SpectralSide.instCompactSpaceMatrix LocalGL2.Kirillov.fintype_Qm LocalGL2.Kirillov.fintype_Ch LocalGL2.Kirillov.addCommGroup_Ch LocalGL2.Kirillov.finite_Qm LocalGL2.Kirillov.addCommGroup_additive_Qm LocalGL2.Kirillov.decidableEq_Ch LocalGL2.Kirillov.finite_additive_Qm IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply"
p2m_attr_erase "simp" "IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.whittakerCoefficient_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"
p2m_attr_erase "simp" "LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.mem_sigmaCentralizer_iff LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.mem_primeFibre AutomorphicForm.WhittakerModel.archFnAt_zero AutomorphicForm.WhittakerModel.localFnAt_zero TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply LanglandsTunnell.CubicInduction.CubicInductionForm.mk.injEq LanglandsTunnell.CubicInduction.CubicInductionForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe LanglandsTunnell.RankinSelberg.rsGlobalIntegral_zero_left LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral AutomorphicForm.gl2Weyl_val LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.CubicInductionData.mk.sizeOf_spec LanglandsTunnell.CubicInduction.CubicInductionData.mk.injEq FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero"
p2m_attr_erase "simp" "algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply LocalGL2.Kirillov.zG_coe LocalGL2.Kirillov.wG_coe LocalGL2.Kirillov.dg_coe LocalGL2.Kirillov.rT_apply LocalGL2.Kirillov.rT_one Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one"
p2m_attr_erase "simp" "QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul MeasureTheory.L2.kernelIntegralLM_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ArtinL.Abelian.coeff_zero IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf AutomorphicForm.gl3LFactorPoly_def AutomorphicForm.JPSSGL3Factored.mk.injEq AutomorphicForm.coeff_three_gl3LFactorPoly AutomorphicForm.coeff_one_gl3LFactorPoly AutomorphicForm.coeff_zero_gl3LFactorPoly AutomorphicForm.JPSSGL3Factored.mk.sizeOf_spec AutomorphicForm.JPSSConverseFactored.mk.sizeOf_spec AutomorphicForm.coeff_two_gl3LFactorPoly AutomorphicForm.JPSSConverseFactored.mk.injEq AutomorphicForm.coeff_zero_heckeLFactorPoly AutomorphicForm.coeff_two_heckeLFactorPoly AutomorphicForm.heckeLFactorPoly_def AutomorphicForm.HeckeEigensystem.localLFactor_def"
p2m_attr_erase "simp" "AutomorphicForm.coeff_one_heckeLFactorPoly AutomorphicForm.satakePow_two EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.bcWeight_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open AutomorphicForm.TranslateSpanOccurrence

noncomputable section

namespace CubicAscentScoped

theorem forall_rat_iff {P : ∀ w : InfinitePlace ℚ, w.IsReal → Prop} :
    (∀ w : InfinitePlace ℚ, ∀ hw : w.IsReal, P w hw) ↔ P Rat.infinitePlace Rat.isReal_infinitePlace := by
  refine ⟨fun h => h _ _, fun h w hw => ?_⟩
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  exact h

theorem occ_congr {F : Type} [Field F] [NumberField F] {D : Set (AdelicGL2 (𝓞 F) F)}
    {Θ : HeckeEigensystem F ℂ} {P Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ∀ φ, P φ ↔ Q φ) :
    ArchOccursInClassOf F D Θ P ↔ ArchOccursInClassOf F D Θ Q :=
  ⟨fun hP => hP.mono fun φ hφ => (h φ).1 hφ, fun hQ => hQ.mono fun φ hφ => (h φ).2 hφ⟩

theorem archWeightCharℝ_one : archWeightCharℝ 1 = archWeightOneℝ := by
  ext k
  simp [archWeightCharℝ]

theorem archWeightCharℝ_one_comp {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsReal) :
    (archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
      (norm_ringEquivRealOfIsReal hw)) = archWeightOneAt hw := by
  rw [archWeightCharℝ_one]; rfl

private theorem _root_.CubicAscentScoped.central_transform {F : Type} [Field F] [NumberField F] {pins : CarrierPins F}
    {Θ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Θ)
    (z : (AdeleRing (𝓞 F) F)ˣ) (hz : z ∈ pins.Z) (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (centralScalar (𝓞 F) F z * g) = ((R.centralChar ⟨z, hz⟩ : ℂˣ) : ℂ) * R.toFun g := by
  letI := pins.mS
  exact (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).central_transform ⟨z, hz⟩ g

p2m_export "CubicAscentScoped" "central_transform"

theorem centralChar_eq_of_toFun {F : Type} [Field F] [NumberField F] {pins : CarrierPins F}
    {Θ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Θ)
    (z : (AdeleRing (𝓞 F) F)ˣ) (hz : z ∈ pins.Z) (c : ℂ)
    (h : ∀ g : AdelicGL2 (𝓞 F) F, R.toFun (centralScalar (𝓞 F) F z * g) = c * R.toFun g) :
    ((R.centralChar ⟨z, hz⟩ : ℂˣ) : ℂ) = c := by
  obtain ⟨g, hg⟩ := R.exists_ne_zero
  have := h g
  rw [central_transform R z hz g] at this
  exact mul_right_cancel₀ hg this

variable {F : Type} [Field F] [NumberField F]

theorem adelicArchGLInclAt_val_apply (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

theorem centralScalar_val_apply (z : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
  show (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem adelicArchGLInclAt_map_scalar {w : InfinitePlace F} (hw : w.IsReal) (t : ℝˣ) :
    adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) =
      centralScalar (𝓞 F) F (NumberField.AdelicVolume.archCentralUnit F w
        (Units.map ((ringEquivRealOfIsReal hw).symm.toRingHom : ℝ →* w.Completion) t)) := by
  classical
  apply Units.ext
  ext i j
  rw [adelicArchGLInclAt_val_apply, centralScalar_val_apply]
  have hM : ((Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
      (Matrix.GeneralLinearGroup.scalar (Fin 2) t) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j =
      if i = j then (ringEquivRealOfIsReal hw).symm (t : ℝ) else 0 := by
    show (ringEquivRealOfIsReal hw).symm.toRingHom ((Matrix.scalar (Fin 2) (t : ℝ)) i j) = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  refine Prod.ext (funext fun v => ?_) ?_
  · show archMatrixUpdate F w _ i j v = _
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, hM]
      split_ifs with hij
      · show _ = Function.update (1 : InfiniteAdeleRing F) v _ v
        rw [Function.update_self]; rfl
      · rfl
    · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]
      split_ifs with hij
      · subst hij
        rw [Matrix.one_apply_eq]
        show (1 : v.Completion) = Function.update (1 : InfiniteAdeleRing F) w _ v
        rw [Function.update_of_ne hv]; rfl
      · rw [Matrix.one_apply_ne hij]; rfl
  · show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j = _
    split_ifs with hij
    · subst hij; rw [Matrix.one_apply_eq]; rfl
    · rw [Matrix.one_apply_ne hij]; rfl

end CubicAscentScoped

end

open CubicAscentScoped

set_option maxHeartbeats 3200000 in
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
    ∀ w : InfinitePlace K, ∀ hw : w.IsReal,
      (∀ χ' : rowIsometrySubgroup₀ ℝ →* ℂˣ,
        ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
            (fun φ => ∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, HasArchCharacterAt₀ ℚ w'
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw')
                (norm_ringEquivRealOfIsReal hw'))) φ) →
          ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
            (fun φ => HasArchCharacterAt₀ K w
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ)) ∧
      (ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
          (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
              HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ∧
            IsArchHolomorphicAt Rat.infinitePlace Rat.isReal_infinitePlace φ) →
        ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
          (fun φ => HasArchCharacterAt₀ K w (archWeightOneAt hw) φ ∧ IsArchHolomorphicAt w hw φ)) ∧
      (ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
          (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
              HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ∧
            ¬ IsArchHolomorphicAt Rat.infinitePlace Rat.isReal_infinitePlace φ) →
        ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
          (fun φ => HasArchCharacterAt₀ K w (archWeightOneAt hw) φ ∧ ¬ IsArchHolomorphicAt w hw φ)) ∧
      (∀ χ' : rowIsometrySubgroup₀ ℝ →* ℂˣ,
        ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
            (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, HasArchCharacterAt₀ ℚ w'
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw')
                (norm_ringEquivRealOfIsReal hw'))) φ) ∧
              IsArchLowestWeightAt Rat.infinitePlace Rat.isReal_infinitePlace φ) →
          ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
            (fun φ => HasArchCharacterAt₀ K w
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchLowestWeightAt w hw φ)) := by
  intro w hw

  have hΘK : ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (formalBaseChange ℚ K Φ) (fun _ => True) := by
    obtain ⟨Ψ, hΨ, hΨr⟩ := hcuspK
    exact archOccursInClassOf_true_of_isArithGenuineCuspRealizable hΨ hΨr

  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ :=
    AutomorphicForm.archOccursInClassOf_iff_archCasimirAt_of_coversModCentre K c u d₁ d₂ T hd hcov
      (formalBaseChange ℚ K Φ) hΘK w hw
  have hQ := fun (hT : ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
      (fun _ => True)) =>
    AutomorphicForm.archOccursInClassOf_iff_archCasimirAt_of_coversModCentre ℚ c' u' d₁' d₂' T' hd' hcov' Φ
      hT Rat.infinitePlace Rat.isReal_infinitePlace

  have hL1 :=
    LanglandsTunnell.archOccursInClassOf_formalBaseChange_archCasimirAt_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
      K hdeg c' u' d₁' d₂' T' hd' hcov' c u d₁ d₂ T hd hcov Φ hcuspK S₀ χ _hχ2 _hlink _hnd w hw

  have h1Q : ∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ↔
        HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map
          (ringEquivRealOfIsReal Rat.isReal_infinitePlace)
          (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ := fun φ => by
    rw [archWeightCharℝ_one_comp]; exact forall_rat_iff
  have h1K : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      HasArchCharacterAt₀ K w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ ↔
        HasArchCharacterAt₀ K w (archWeightOneAt hw) φ := fun φ => by
    rw [archWeightCharℝ_one_comp]

  have hce_transfer : ∀ (Θ' : HeckeEigensystem ℚ ℂ) (hΘ' : Θ'.AgreesAwayFromFinite Φ)
      (R' : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂')
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        Θ'.toRawCentral)
      (hR' : IsGenuineCuspRealizationAt ℚ _ Θ'.toRawCentral R')
      (Ψ'' : HeckeEigensystem K ℂ) (hΨ'' : Ψ''.AgreesAwayFromFinite (formalBaseChange ℚ K Φ))
      (R'' : SmoothCuspRealizationAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        Ψ''.toRawCentral)
      (hR'' : IsGenuineCuspRealizationAt K _ Ψ''.toRawCentral R'') (t : ℝˣ) (g : AdelicGL2 (𝓞 K) K),
      R''.toFun (adelicArchGLInclAt K w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) =
        ((R'.centralChar ⟨AdelicVolume.archCentralUnit ℚ Rat.infinitePlace
            (Units.mapEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toMulEquiv t),
            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
          R''.toFun g := by
    intro Θ' hΘ' R' hR' Ψ'' hΨ'' R'' hR'' t g
    rw [adelicArchGLInclAt_map_scalar hw t, central_transform R'' _ (Subgroup.mem_top _) g]
    congr 1
    exact LanglandsTunnell.centralChar_archCentralUnit_eq_of_agreesAwayFromFinite_formalBaseChange_of_isReal
      K (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      Φ Θ' hΘ' R' hR' Ψ'' hΨ'' R'' hR'' w hw t
  have hceQ : ∀ (Θ' : HeckeEigensystem ℚ ℂ)
      (R' : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂')
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        Θ'.toRawCentral)
      (t : ℝˣ) (ct : ℂ),
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, R'.toFun (adelicArchGLInclAt ℚ Rat.infinitePlace
          (Matrix.GeneralLinearGroup.map
            (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ct * R'.toFun g) →
      ((R'.centralChar ⟨AdelicVolume.archCentralUnit ℚ Rat.infinitePlace
            (Units.mapEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toMulEquiv t),
            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = ct := by
    intro Θ' R' t ct h
    refine centralChar_eq_of_toFun R' _ (Subgroup.mem_top _) ct fun g ↦ ?_
    rw [← h g, adelicArchGLInclAt_map_scalar Rat.isReal_infinitePlace t]
    rfl
  refine ⟨fun χ' h => ?_, fun h => ?_, fun h => ?_, fun χ' h => ?_⟩
  ·
    obtain ⟨hQ1, -, -, -, -⟩ := hQ (h.mono fun _ _ => trivial)
    obtain ⟨n, rfl, lam, hE⟩ := (hQ1 χ').1 ((occ_congr fun φ => forall_rat_iff).1 h)
    have hEK := hL1 n lam ((occ_congr fun φ => and_congr forall_rat_iff Iff.rfl).2 hE)
    exact (hK1 (archWeightCharℝ n)).2 ⟨n, rfl, lam, hEK⟩
  ·
    obtain ⟨-, -, hQ3, -, -⟩ := hQ (h.mono fun _ _ => trivial)
    obtain ⟨Θ', hΘ', R', hR', h1, hsm, hcas, hce⟩ :=
      hQ3.1 ((occ_congr fun φ => and_congr (h1Q φ) Iff.rfl).1 h)
    obtain ⟨Ψ'', hΨ'', R'', hR'', h1'', hsm'', hcas''⟩ :=
      hL1 1 (1 / 4 : ℂ) ⟨Θ', hΘ', R', hR', forall_rat_iff.2 h1, hsm, hcas⟩
    have hce'' : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 K) K,
        R''.toFun (adelicArchGLInclAt K w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) * R''.toFun g := by
      intro t ht g
      rw [hce_transfer Θ' hΘ' R' hR' Ψ'' hΨ'' R'' hR'' t g, hceQ Θ' R' t _ (hce t ht)]
    exact (occ_congr fun φ => and_congr (h1K φ) Iff.rfl).1
      (hK3.2 ⟨Ψ'', hΨ'', R'', hR'', h1'', hsm'', hcas'', hce''⟩)
  ·

    obtain ⟨-, -, -, hQ4, -⟩ := hQ (h.mono fun _ _ => trivial)
    obtain ⟨⟨lam, Θ', hΘ', R', hR', h1, hsm, hcas⟩, hneg⟩ :=
      hQ4.1 ((occ_congr fun φ => and_congr (h1Q φ) Iff.rfl).1 h)
    have hEK := hL1 1 lam ⟨Θ', hΘ', R', hR', forall_rat_iff.2 h1, hsm, hcas⟩
    refine (occ_congr fun φ => and_congr (h1K φ) Iff.rfl).1 (hK4.2 ⟨⟨lam, hEK⟩, fun hbad => hneg ?_⟩)
    obtain ⟨Ψ₃, hΨ₃, R₃, hR₃, h1₃, hsm₃, hcas₃, hce₃⟩ := hbad
    have hlam : lam = 1 / 4 := hK5 1 1 lam (1 / 4 : ℂ) hEK ⟨Ψ₃, hΨ₃, R₃, hR₃, h1₃, hsm₃, hcas₃⟩
    subst hlam
    refine ⟨Θ', hΘ', R', hR', h1, hsm, hcas, fun t ht g => ?_⟩

    obtain ⟨g₃, hg₃⟩ := R₃.exists_ne_zero
    have h3 := hce_transfer Θ' hΘ' R' hR' Ψ₃ hΨ₃ R₃ hR₃ t g₃
    rw [hce₃ t ht g₃] at h3
    have hval := mul_right_cancel₀ hg₃ h3
    rw [adelicArchGLInclAt_map_scalar Rat.isReal_infinitePlace t, central_transform R' _ (Subgroup.mem_top _) g]
    congr 1
    exact hval.symm
  ·
    obtain ⟨hQ1, hQ2, -, -, -⟩ := hQ (h.mono fun _ _ => trivial)
    obtain ⟨n, rfl, -⟩ := (hQ1 χ').1 (h.mono fun φ hφ => forall_rat_iff.1 hφ.1)
    obtain ⟨Θ', hΘ', R', hR', hn, hsm, hcas⟩ :=
      (hQ2 n).1 ((occ_congr fun φ => and_congr forall_rat_iff Iff.rfl).1 h)
    exact (hK2 n).2 (hL1 n _ ⟨Θ', hΘ', R', hR', forall_rat_iff.2 hn, hsm, hcas⟩)

end S_LanglandsTunnell_archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
end P2MW
export P2MW.S_LanglandsTunnell_archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist (solution)
