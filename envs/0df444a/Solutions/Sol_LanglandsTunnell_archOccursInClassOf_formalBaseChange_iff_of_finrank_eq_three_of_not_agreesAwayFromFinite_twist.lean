-- Prove2me | solution 1 for LanglandsTunnell.archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7311d38f-0ac5-5766-b795-dba59def06ca

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_isArchHolomorphicAt_of_agreesAwayFromFinite_of_weightOne_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex M4aHerbrand.isMulCommutative_ideleClassGroup"
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal"
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SpectralSide.instCompactSpaceMatrix LocalGL2.Kirillov.fintype_Qm LocalGL2.Kirillov.fintype_Ch LocalGL2.Kirillov.addCommGroup_Ch LocalGL2.Kirillov.finite_Qm LocalGL2.Kirillov.addCommGroup_additive_Qm LocalGL2.Kirillov.decidableEq_Ch LocalGL2.Kirillov.finite_additive_Qm IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex"
p2m_attr_erase "simp" "AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight"
p2m_attr_erase "simp" "WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun"
p2m_attr_erase "simp" "AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.whittakerCoefficient_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.mem_sigmaCentralizer_iff LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.mem_primeFibre AutomorphicForm.WhittakerModel.archFnAt_zero AutomorphicForm.WhittakerModel.localFnAt_zero TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply LanglandsTunnell.CubicInduction.CubicInductionForm.mk.injEq LanglandsTunnell.CubicInduction.CubicInductionForm.mk.sizeOf_spec LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe LanglandsTunnell.RankinSelberg.rsGlobalIntegral_zero_left LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral AutomorphicForm.gl2Weyl_val LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.CubicInductionData.mk.sizeOf_spec LanglandsTunnell.CubicInduction.CubicInductionData.mk.injEq FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul"
p2m_attr_erase "simp" "LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply LocalGL2.Kirillov.zG_coe LocalGL2.Kirillov.wG_coe LocalGL2.Kirillov.dg_coe LocalGL2.Kirillov.rT_apply LocalGL2.Kirillov.rT_one Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul MeasureTheory.L2.kernelIntegralLM_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ArtinL.Abelian.coeff_zero IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype"
p2m_attr_erase "simp" "ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf AutomorphicForm.gl3LFactorPoly_def AutomorphicForm.JPSSGL3Factored.mk.injEq AutomorphicForm.coeff_three_gl3LFactorPoly AutomorphicForm.coeff_one_gl3LFactorPoly AutomorphicForm.coeff_zero_gl3LFactorPoly AutomorphicForm.JPSSGL3Factored.mk.sizeOf_spec AutomorphicForm.JPSSConverseFactored.mk.sizeOf_spec AutomorphicForm.coeff_two_gl3LFactorPoly AutomorphicForm.JPSSConverseFactored.mk.injEq AutomorphicForm.coeff_zero_heckeLFactorPoly AutomorphicForm.coeff_two_heckeLFactorPoly AutomorphicForm.heckeLFactorPoly_def AutomorphicForm.HeckeEigensystem.localLFactor_def AutomorphicForm.coeff_one_heckeLFactorPoly AutomorphicForm.satakePow_two EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.bcWeight_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion AutomorphicForm.TranslateSpanOccurrence IsDedekindDomain

namespace ArchClassCompatAssemblyScoped

theorem typeSet_descent (SQ SK LQ LK : ℤ → Prop)
    (asc : ∀ n, SQ n → SK n) (ascL : ∀ k, LQ k → LK k)
    (patQ : (∃ ε : ℤ, ∀ n, SQ n ↔ Even (n - ε)) ∨
      (∃ k : ℤ, 2 ≤ k ∧ ∀ n, SQ n ↔ (k ≤ |n| ∧ Even (n - k))))
    (patK : (∃ ε : ℤ, ∀ n, SK n ↔ Even (n - ε)) ∨
      (∃ k : ℤ, 2 ≤ k ∧ ∀ n, SK n ↔ (k ≤ |n| ∧ Even (n - k))))
    (lowQ : ∀ k : ℤ, 2 ≤ k → (LQ k ↔ ∀ n, SQ n ↔ (k ≤ |n| ∧ Even (n - k))))
    (lowK : ∀ k : ℤ, 2 ≤ k → (LK k ↔ ∀ n, SK n ↔ (k ≤ |n| ∧ Even (n - k)))) :
    ∀ n, SK n → SQ n := by
  intro n hn
  rcases patQ with ⟨ε, hε⟩ | ⟨k, hk2, hk⟩
  ·
    obtain ⟨m, hm1, hmε⟩ : ∃ m : ℤ, |m| ≤ 1 ∧ Even (m - ε) := by
      rcases Int.even_or_odd ε with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact ⟨0, by simp, ⟨-t, by rw [ht]; ring⟩⟩
      · exact ⟨1, by simp, ⟨-t, by rw [ht]; ring⟩⟩
    have hQm : SQ m := (hε m).2 hmε
    have hKm : SK m := asc m hQm
    rcases patK with ⟨ε', hε'⟩ | ⟨k', hk'2, hk'⟩
    ·
      have h1 : Even (m - ε') := (hε' m).1 hKm
      have h2 : Even (n - ε') := (hε' n).1 hn
      refine (hε n).2 ?_
      have : n - ε = (n - ε') - (m - ε') + (m - ε) := by ring
      rw [this]
      exact (h2.sub h1).add hmε
    ·
      exfalso
      have habs : k' ≤ |m| := ((hk' m).1 hKm).1
      omega
  ·
    have hLQ : LQ k := (lowQ k hk2).2 hk
    have hSK : ∀ m, SK m ↔ (k ≤ |m| ∧ Even (m - k)) := (lowK k hk2).1 (ascL k hLQ)
    exact (hk n).2 ((hSK n).1 hn)

theorem infinitePlace_rat_eq (w : InfinitePlace ℚ) : w = Rat.infinitePlace := by
  rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding Rat.infinitePlace,
    Subsingleton.elim w.embedding Rat.infinitePlace.embedding]

theorem forall_infinitePlace_rat_iff (Q : ∀ w' : InfinitePlace ℚ, w'.IsReal → Prop) :
    (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, Q w' hw') ↔
      Q Rat.infinitePlace Rat.isReal_infinitePlace := by
  refine ⟨fun h => h _ _, fun h w' hw' => ?_⟩
  obtain rfl := infinitePlace_rat_eq w'
  exact h

theorem occ_rat_forall_iff (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)
    (Q : ∀ w' : InfinitePlace ℚ, w'.IsReal → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) → Prop) :
    ArchOccursInClassOf ℚ D Φ (fun φ => ∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, Q w' hw' φ) ↔
      ArchOccursInClassOf ℚ D Φ (Q Rat.infinitePlace Rat.isReal_infinitePlace) :=
  ⟨fun h => h.mono fun _ hφ => hφ _ _,
   fun h => h.mono fun φ hφ => (forall_infinitePlace_rat_iff (fun w' hw' => Q w' hw' φ)).2 hφ⟩

theorem occ_rat_forall_and_iff (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)
    (Q : ∀ w' : InfinitePlace ℚ, w'.IsReal → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) → Prop)
    (L : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) → Prop) :
    ArchOccursInClassOf ℚ D Φ
        (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, Q w' hw' φ) ∧ L φ) ↔
      ArchOccursInClassOf ℚ D Φ (fun φ => Q Rat.infinitePlace Rat.isReal_infinitePlace φ ∧ L φ) :=
  ⟨fun h => h.mono fun _ hφ => ⟨hφ.1 _ _, hφ.2⟩,
   fun h => h.mono fun φ hφ =>
    ⟨(forall_infinitePlace_rat_iff (fun w' hw' => Q w' hw' φ)).2 hφ.1, hφ.2⟩⟩

theorem archWeightCharℝ_one : archWeightCharℝ 1 = archWeightOneℝ := by
  ext k : 1
  show (archWeightOneℝ k) ^ (1 : ℤ) = archWeightOneℝ k
  exact zpow_one _

theorem archWeightCharℝ_one_comp {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsReal) :
    (archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
      (norm_ringEquivRealOfIsReal hw)) = archWeightOneAt hw := by
  rw [archWeightCharℝ_one]
  rfl

abbrev TypAt (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  HasArchCharacterAt₀ F w
    (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ

theorem not_occ_hol_and_occ_not_hol (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal)
    (hhol : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w (archWeightOneAt hw) φ ∧ IsArchHolomorphicAt w hw φ))
    (hnhol : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w (archWeightOneAt hw) φ ∧ ¬ IsArchHolomorphicAt w hw φ)) :
    False := by
  obtain ⟨Θ₁, hΘ₁, R₁, hR₁, hR₁w1, hR₁hol⟩ := hhol
  obtain ⟨Θ₂, hΘ₂, R₂, hR₂, hR₂w1, hR₂nhol⟩ := hnhol
  exact hR₂nhol
    (LanglandsTunnell.isArchHolomorphicAt_of_agreesAwayFromFinite_of_weightOne_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ₁ Θ₂ (agrees_trans hΘ₁ (agrees_symm hΘ₂)) R₁ hR₁ R₂ hR₂ w hw
      hR₁w1 hR₁hol hR₂w1)

theorem occ_not_hol_of_occ_of_not_occ_hol (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal)
    (h1 : ArchOccursInClassOf F D Θ (fun φ => HasArchCharacterAt₀ F w (archWeightOneAt hw) φ))
    (hn : ¬ ArchOccursInClassOf F D Θ
      (fun φ => HasArchCharacterAt₀ F w (archWeightOneAt hw) φ ∧ IsArchHolomorphicAt w hw φ)) :
    ArchOccursInClassOf F D Θ
      (fun φ => HasArchCharacterAt₀ F w (archWeightOneAt hw) φ ∧ ¬ IsArchHolomorphicAt w hw φ) := by
  obtain ⟨Θ', hΘ', R', hR', hR'w1⟩ := h1
  by_cases hh : IsArchHolomorphicAt w hw R'.toFun
  · exact absurd ⟨Θ', hΘ', R', hR', hR'w1, hh⟩ hn
  · exact ⟨Θ', hΘ', R', hR', hR'w1, hh⟩

end ArchClassCompatAssemblyScoped

open ArchClassCompatAssemblyScoped

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
    (hΦ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂')
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      Φ)
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
        ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
            (fun φ => HasArchCharacterAt₀ K w
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ) ↔
          ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
            (fun φ => ∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, HasArchCharacterAt₀ ℚ w'
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw')
                (norm_ringEquivRealOfIsReal hw'))) φ)) ∧
      (ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
          (fun φ => HasArchCharacterAt₀ K w (archWeightOneAt hw) φ ∧ IsArchHolomorphicAt w hw φ) ↔
        ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
          (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
              HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ∧
            IsArchHolomorphicAt Rat.infinitePlace Rat.isReal_infinitePlace φ)) ∧
      (ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
          (fun φ => HasArchCharacterAt₀ K w (archWeightOneAt hw) φ ∧ ¬ IsArchHolomorphicAt w hw φ) ↔
        ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
          (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
              HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ∧
            ¬ IsArchHolomorphicAt Rat.infinitePlace Rat.isReal_infinitePlace φ)) := by
  intro w hw

  set DK : Set (AdelicGL2 (𝓞 K) K) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂ with hDK
  set DQ : Set (AdelicGL2 (𝓞 ℚ) ℚ) := ⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂' with hDQ

  have hoccK : ArchOccursInClassOf K DK (formalBaseChange ℚ K Φ) (fun _ => True) := by
    obtain ⟨Ψ, hΨ, hΨr⟩ := hcuspK
    exact archOccursInClassOf_true_of_isArithGenuineCuspRealizable hΨ hΨr
  have hoccQ : ArchOccursInClassOf ℚ DQ Φ (fun _ => True) :=
    archOccursInClassOf_true_of_isArithGenuineCuspRealizable (agrees_refl Φ) hΦ

  obtain ⟨asc1, asc2, asc3, asc4⟩ :=
    LanglandsTunnell.archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
      K hdeg c' u' d₁' d₂' T' hd' hcov' c u d₁ d₂ T hd hcov Φ hcuspK S₀ χ _hχ2 _hlink _hnd w hw

  obtain ⟨r0K, patK, lowK⟩ :=
    AutomorphicForm.archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre
      K c u d₁ d₂ T hd hcov (formalBaseChange ℚ K Φ) hoccK w hw
  obtain ⟨-, patQ, lowQ⟩ :=
    AutomorphicForm.archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre
      ℚ c' u' d₁' d₂' T' hd' hcov' Φ hoccQ Rat.infinitePlace Rat.isReal_infinitePlace

  let SK : ℤ → Prop := fun n =>
    ArchOccursInClassOf K DK (formalBaseChange ℚ K Φ) (fun φ => TypAt K w hw (archWeightCharℝ n) φ)
  let SQ : ℤ → Prop := fun n =>
    ArchOccursInClassOf ℚ DQ Φ (fun φ => ∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
      TypAt ℚ w' hw' (archWeightCharℝ n) φ)
  let LK : ℤ → Prop := fun k =>
    ArchOccursInClassOf K DK (formalBaseChange ℚ K Φ)
      (fun φ => TypAt K w hw (archWeightCharℝ k) φ ∧ IsArchLowestWeightAt w hw φ)
  let LQ : ℤ → Prop := fun k =>
    ArchOccursInClassOf ℚ DQ Φ (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
      TypAt ℚ w' hw' (archWeightCharℝ k) φ) ∧
        IsArchLowestWeightAt Rat.infinitePlace Rat.isReal_infinitePlace φ)

  have hSQ : ∀ n, SQ n ↔ ArchOccursInClassOf ℚ DQ Φ
      (fun φ => TypAt ℚ Rat.infinitePlace Rat.isReal_infinitePlace (archWeightCharℝ n) φ) :=
    fun n => occ_rat_forall_iff DQ Φ (fun w' hw' φ => TypAt ℚ w' hw' (archWeightCharℝ n) φ)
  have hLQ : ∀ k, LQ k ↔ ArchOccursInClassOf ℚ DQ Φ
      (fun φ => TypAt ℚ Rat.infinitePlace Rat.isReal_infinitePlace (archWeightCharℝ k) φ ∧
        IsArchLowestWeightAt Rat.infinitePlace Rat.isReal_infinitePlace φ) :=
    fun k => occ_rat_forall_and_iff DQ Φ (fun w' hw' φ => TypAt ℚ w' hw' (archWeightCharℝ k) φ)
      (IsArchLowestWeightAt Rat.infinitePlace Rat.isReal_infinitePlace)

  have hdesc : ∀ n, SK n → SQ n := by
    refine typeSet_descent SQ SK LQ LK (fun n hn => asc1 (archWeightCharℝ n) hn)
      (fun k hk => asc4 (archWeightCharℝ k) hk) ?_ ?_ ?_ ?_
    · rcases patQ with ⟨ε, hε⟩ | ⟨k, hk2, hk⟩
      · exact Or.inl ⟨ε, fun n => (hSQ n).trans (hε n)⟩
      · exact Or.inr ⟨k, hk2, fun n => (hSQ n).trans (hk n)⟩
    · exact patK
    · intro k hk2
      refine (hLQ k).trans (((lowQ k hk2)).trans ?_)
      exact forall_congr' fun n => iff_congr (hSQ n).symm Iff.rfl
    · exact lowK

  have hK1_of : ∀ {P : (AdelicGL2 (𝓞 K) K → ℂ) → Prop},
      ArchOccursInClassOf K DK (formalBaseChange ℚ K Φ)
        (fun φ => HasArchCharacterAt₀ K w (archWeightOneAt hw) φ ∧ P φ) → SK 1 :=
    fun h => h.mono fun φ hφ => by
      show HasArchCharacterAt₀ K w _ φ
      rw [archWeightCharℝ_one_comp]; exact hφ.1
  have hQ1_to : SQ 1 → ArchOccursInClassOf ℚ DQ Φ
      (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace (archWeightOneAt Rat.isReal_infinitePlace) φ) :=
    fun h => ((hSQ 1).1 h).mono fun φ hφ => by
      have hφ' : HasArchCharacterAt₀ ℚ Rat.infinitePlace _ φ := hφ
      rw [archWeightCharℝ_one_comp] at hφ'; exact hφ'

  have hQw1_iff : ∀ (L : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) → Prop),
      ArchOccursInClassOf ℚ DQ Φ (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
          HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ∧ L φ) ↔
        ArchOccursInClassOf ℚ DQ Φ (fun φ =>
          HasArchCharacterAt₀ ℚ Rat.infinitePlace (archWeightOneAt Rat.isReal_infinitePlace) φ ∧ L φ) :=
    fun L => occ_rat_forall_and_iff DQ Φ
      (fun w' hw' φ => HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) L
  refine ⟨fun χ' => ⟨fun hK => ?_, asc1 χ'⟩, ⟨fun hK => ?_, asc2⟩, ⟨fun hK => ?_, asc3⟩⟩
  ·
    obtain ⟨n, rfl⟩ := r0K χ' hK
    exact hdesc n hK
  ·
    have hQ1 := hQ1_to (hdesc 1 (hK1_of hK))
    by_contra hnQ
    have hnQ' : ¬ ArchOccursInClassOf ℚ DQ Φ (fun φ =>
        HasArchCharacterAt₀ ℚ Rat.infinitePlace (archWeightOneAt Rat.isReal_infinitePlace) φ ∧
          IsArchHolomorphicAt Rat.infinitePlace Rat.isReal_infinitePlace φ) :=
      fun h => hnQ ((hQw1_iff _).2 h)
    have hQnh := occ_not_hol_of_occ_of_not_occ_hol ℚ DQ Φ Rat.infinitePlace Rat.isReal_infinitePlace
      hQ1 hnQ'
    have hKnh := asc3 ((hQw1_iff _).2 hQnh)
    exact not_occ_hol_and_occ_not_hol K c u d₁ d₂ T hd hcov (formalBaseChange ℚ K Φ) w hw hK hKnh
  ·
    have hQ1 := hQ1_to (hdesc 1 (hK1_of hK))
    refine (hQw1_iff _).2
      (occ_not_hol_of_occ_of_not_occ_hol ℚ DQ Φ Rat.infinitePlace Rat.isReal_infinitePlace hQ1 ?_)
    intro hQhol
    have hKhol := asc2 ((hQw1_iff _).2 hQhol)
    exact not_occ_hol_and_occ_not_hol K c u d₁ d₂ T hd hcov (formalBaseChange ℚ K Φ) w hw hKhol hK

end S_LanglandsTunnell_archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
end P2MW
export P2MW.S_LanglandsTunnell_archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist (solution)
