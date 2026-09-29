-- Prove2me | solution 1 for ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/db74f34a-9c3c-5d0d-9b1a-1327a109a2dc

import Mathlib
import Theorems.Thm_ModularCurve_isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self
import Theorems.Thm_ModularCurve_finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL
import Theorems.Thm_ModularCurve_exists_iterate_diamond_eq_self_pic0_fbar
import Theorems.Thm_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint
import Theorems.Thm_ModularCurve_qExpFrobeniusPushforwardModL_ofAlgAut_diamondActionModL_smul
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_pullbackAlong_eq_pair_pushforwardAlongHom_of_isPurelyInseparable
import Theorems.Thm_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_perfect_of_divisible_coprime_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Pic0_exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self
import Theorems.Thm_AlgebraicCurve_Pic0_finite_and_card_torsion_le_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap ValuationSubring.instIsAlgClosedResidueField kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply RatFunc.denom_X_pow RatFunc.powerBasisAdjoinXPow_dim RatFunc.powerBasisAdjoinXPow_gen RatFunc.intDegree_X_pow RatFunc.num_X_pow AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I"
p2m_attr_erase "simp" "AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ValuationSubring.coe_toResidueValuationSubring AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero"
p2m_attr_erase "simp" "AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

namespace NoEig2S3

theorem map_mem_torsion {K F : Type*} [Field K] [Field F] [Algebra K F] (f : Pic0 K F →+ Pic0 K F) {n : ℕ}
    {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F n) : f x ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion] at hx ⊢
  rw [← map_zsmul, hx, map_zero]

theorem s3b
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (F Finv Fstar : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (n : ℕ) [NeZero n] (hn : (n : κ) ≠ 0)
    [HasPrincipalDivisors κ (Fbar p M H hpM κ)]
    (e : DivisorialWeilPairingData κ (Fbar p M H hpM κ) n)
    (x y : Pic0.torsion κ (Fbar p M H hpM κ) n)
    (hx : Fstar (x : Pic0 κ (Fbar p M H hpM κ)) ∈ Pic0.torsion κ (Fbar p M H hpM κ) n)
    (hy : F (y : Pic0 κ (Fbar p M H hpM κ)) ∈ Pic0.torsion κ (Fbar p M H hpM κ) n) :
    e.pair ⟨Fstar (x : Pic0 κ (Fbar p M H hpM κ)), hx⟩ y = e.pair x ⟨F (y : Pic0 κ (Fbar p M H hpM κ)), hy⟩ := by
  classical
  have hp : p.Prime := Fact.out

  have hT : ModularGroup.T ∈ ΓN p M H hpM := translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  haveI : (ΓN p M H hpM).FiniteIndex := inferInstance
  haveI : IsCurveOver κ (Fbar p M H hpM κ) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed κ (ΓN p M H hpM) hT

  set u := qExpFrobeniusModL κ (ΓN p M H hpM) p with hu
  have hui : u.toRingHom.IsIntegral := qExpFrobeniusModL_isIntegral κ (ΓN p M H hpM) p
  obtain ⟨j, -, hjt, hjfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed κ (ΓN p M H hpM) hT
  have hwit : ∃ x : Fbar p M H hpM κ, Transcendental κ x ∧
      FiniteDimensional (IntermediateField.adjoin κ ({x} : Set (Fbar p M H hpM κ))) (Fbar p M H hpM κ) := ⟨j, hjt, hjfd⟩
  obtain ⟨⟨hP, hfin, hFI, hN⟩, -⟩ := ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental κ (ΓN p M H hpM) hwit

  have hFpush : ∀ z, F z = Pic0.pushforwardAlongHom u hui hfin hN z := by
    intro z
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
    rw [hF, qExpFrobeniusPushforwardModL_mk hfin hFI hN, Pic0.pushforwardAlongHom_mk]
    congr 1

  have hFinv1 : ∀ z, F (Finv z) = z := fun z => by
    have := congrArg (fun f : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ) => f z) hFinv.1
    simpa using this
  have hFstar_pull : ∀ D : Divisor.degZero (K := κ) (F := Fbar p M H hpM κ),
      Fstar (Pic0.mk D) = Pic0.mk ⟨Divisor.pullbackAlong u hui (D : Divisor κ (Fbar p M H hpM κ)),
        Divisor.pullbackAlong_mem_degZero u hui hFI D.2⟩ := by
    intro D
    have h1 : qExpFrobeniusPullbackModL κ (ΓN p M H hpM) p (Pic0.mk D) =
        Pic0.mk ⟨Divisor.pullbackAlong u hui (D : Divisor κ (Fbar p M H hpM κ)), Divisor.pullbackAlong_mem_degZero u hui hFI D.2⟩ := by
      rw [qExpFrobeniusPullbackModL_mk hfin hFI hN]
      congr 1
    have h2 := ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental κ (ΓN p M H hpM) hwit
      (Finv (Pic0.mk D))
    rw [← hF, hFinv1] at h2
    rw [← h1, hFstar, h2, natCast_zsmul]

  have hpi : letI := algebraAlong u; IsPurelyInseparable (Fbar p M H hpM κ) (Fbar p M H hpM κ) := by
    letI := algebraAlong u
    haveI : ExpChar (Fbar p M H hpM κ) p := by
      haveI : CharP (Fbar p M H hpM κ) p := charP_of_injective_algebraMap (algebraMap κ (Fbar p M H hpM κ)).injective p
      exact ExpChar.prime hp
    rw [isPurelyInseparable_iff_pow_mem (Fbar p M H hpM κ) p]
    intro z
    refine ⟨1, ⟨qExpArithFrobC p κ (ΓN p M H hpM) • z, ?_⟩⟩
    show u (qExpArithFrobC p κ (ΓN p M H hpM) • z) = z ^ p ^ 1
    apply Subtype.ext
    rw [pow_one, coe_qExpFrobeniusModL, coe_qExpArithFrobC_smul, SubmonoidClass.coe_pow,
      pow_char_eq_coeffMap_frobenius_qExpand, coeffMap_qExpand]

  obtain ⟨D₀, hD₀⟩ := Pic0.mk_surjective (x : Pic0 κ (Fbar p M H hpM κ))
  have hx' := hx
  rw [← hD₀, hFstar_pull D₀] at hx'
  have hy₀ : F (y : Pic0 κ (Fbar p M H hpM κ)) ∈ Pic0.torsion κ (Fbar p M H hpM κ) n := hy
  rw [hFpush] at hy₀
  have key := AlgebraicCurve.DivisorialWeilPairingData.pair_pullbackAlong_eq_pair_pushforwardAlongHom_of_isPurelyInseparable
    u hui hFI hfin hN hpi e e (x : Pic0 κ (Fbar p M H hpM κ)) (Pic0.mem_torsion.mp x.2) (y : Pic0 κ (Fbar p M H hpM κ)) (Pic0.mem_torsion.mp y.2)
    D₀ hD₀ _ rfl (Pic0.mem_torsion.mp hx') (Pic0.mem_torsion.mp hy₀)

  have e1 : (⟨Pic0.mk ⟨Divisor.pullbackAlong u hui (D₀ : Divisor κ (Fbar p M H hpM κ)), Divisor.pullbackAlong_mem_degZero u hui hFI D₀.2⟩,
      Pic0.mem_torsion.mpr (Pic0.mem_torsion.mp hx')⟩ : Pic0.torsion κ (Fbar p M H hpM κ) n) = ⟨Fstar (x : Pic0 κ (Fbar p M H hpM κ)), hx⟩ := by
    apply Subtype.ext
    show _ = Fstar (x : Pic0 κ (Fbar p M H hpM κ))
    rw [← hD₀, hFstar_pull]
  have e2 : (⟨Pic0.pushforwardAlongHom u hui hfin hN (y : Pic0 κ (Fbar p M H hpM κ)), Pic0.mem_torsion.mpr (Pic0.mem_torsion.mp hy₀)⟩ :
      Pic0.torsion κ (Fbar p M H hpM κ) n) = ⟨F (y : Pic0 κ (Fbar p M H hpM κ)), hy⟩ := by
    apply Subtype.ext
    exact (hFpush _).symm
  have e3 : (⟨(x : Pic0 κ (Fbar p M H hpM κ)), Pic0.mem_torsion.mpr (Pic0.mem_torsion.mp x.2)⟩ : Pic0.torsion κ (Fbar p M H hpM κ) n) = x := Subtype.ext rfl
  have e4 : (⟨(y : Pic0 κ (Fbar p M H hpM κ)), Pic0.mem_torsion.mpr (Pic0.mem_torsion.mp y.2)⟩ : Pic0.torsion κ (Fbar p M H hpM κ) n) = y := Subtype.ext rfl
  rw [e1, e2, e3, e4] at key
  exact key

end NoEig2S3

open AlgebraicCurve in
theorem NoEig2.natCard_fixed_eq_of_perfect_of_adjoint
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    {n : ℕ} [NeZero n] [Finite (Pic0.torsion K F n)]
    (e : DivisorialWeilPairingData K F n) (he : e.Perfect)
    (S S' : Pic0 K F →+ Pic0 K F)
    (hS : ∀ x ∈ Pic0.torsion K F n, S x ∈ Pic0.torsion K F n) (hS' : ∀ y ∈ Pic0.torsion K F n, S' y ∈ Pic0.torsion K F n)
    (hadj : ∀ (x y : Pic0.torsion K F n), e.pair ⟨S x, hS x x.2⟩ y = e.pair x ⟨S' y, hS' y y.2⟩) :
    Nat.card {x : Pic0.torsion K F n // S (x : Pic0 K F) = x} = Nat.card {y : Pic0.torsion K F n // S' (y : Pic0 K F) = y} := by
  classical
  set P := Pic0.torsion K F n with hPdef

  let Sr : ↥P →+ ↥P := AddMonoidHom.mk' (fun x => ⟨S x, hS x x.2⟩) (fun a b => Subtype.ext (by simp [map_add]))
  let Sr' : ↥P →+ ↥P := AddMonoidHom.mk' (fun y => ⟨S' y, hS' y y.2⟩) (fun a b => Subtype.ext (by simp [map_add]))
  let T : ↥P →+ ↥P := Sr - AddMonoidHom.id _
  let T' : ↥P →+ ↥P := Sr' - AddMonoidHom.id _

  let u : ↥P → ↥P → Kˣ := fun x y => Units.mk0 (e.pair x y) (e.pair_ne_zero x y)
  have hu : ∀ x y, (u x y : K) = e.pair x y := fun x y => rfl

  have hneg_left : ∀ x y : ↥P, e.pair (-x) y = (e.pair x y)⁻¹ := fun x y => by
    apply eq_inv_of_mul_eq_one_left
    rw [← e.pair_add_left, neg_add_cancel, e.pair_zero_left]
  have hneg_right : ∀ x y : ↥P, e.pair x (-y) = (e.pair x y)⁻¹ := fun x y => by
    apply eq_inv_of_mul_eq_one_left
    rw [← e.pair_add_right, neg_add_cancel, e.pair_zero_right]

  have hleft0 : ∀ x : ↥P, (∀ y, e.pair x y = 1) → x = 0 := fun x hx => by
    have h0 : e.toHom x = 0 := by
      apply Additive.toMul.injective
      ext y
      rw [DivisorialWeilPairingData.toHom_apply_apply, hx y, toMul_zero, AddChar.one_apply]
    exact he.1 (h0.trans (map_zero e.toHom).symm)
  have hadd₁ : ∀ x x' y, u (x + x') y = u x y * u x' y := fun x x' y => by
    ext; rw [Units.val_mul, hu, hu, hu, e.pair_add_left]
  have hadd₂ : ∀ x y y', u x (y + y') = u x y * u x y' := fun x y y' => by
    ext; rw [Units.val_mul, hu, hu, hu, e.pair_add_right]
  have hleft : ∀ x, (∀ y, u x y = 1) → x = 0 := fun x hx =>
    hleft0 x fun y => by rw [← hu, hx y, Units.val_one]
  have hright : ∀ y, (∀ x, u x y = 1) → y = 0 := fun y hy =>
    hleft0 y fun x => by rw [e.pair_swap_eq_inv, ← hu, hy x, Units.val_one, inv_one]
  have hsurj : ∀ χ : Multiplicative ↥P →* Kˣ, ∃ y, ∀ x, u x y = χ (Multiplicative.ofAdd x) := fun χ => by

    let ψ : AddChar ↥P K :=
      { toFun := fun x => ((χ (Multiplicative.ofAdd x))⁻¹ : Kˣ)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := fun a b => by
          rw [ofAdd_add, map_mul, mul_inv, Units.val_mul] }
    obtain ⟨z, hz⟩ := he.2 (Additive.ofMul ψ)
    refine ⟨z, fun x => ?_⟩
    have h1 : e.pair z x = ψ x := by
      have := congrArg (fun φ : Additive (HomPic0Gm K F n) => (Additive.toMul φ) x) hz
      simpa [DivisorialWeilPairingData.toHom_apply_apply] using this
    have h2 : ψ x = (((χ (Multiplicative.ofAdd x))⁻¹ : Kˣ) : K) := rfl
    ext
    rw [hu, e.pair_swap_eq_inv, h1, h2, ← Units.val_inv_eq_inv_val, inv_inv]
  have hadjT : ∀ x y, u (T x) y = u x (T' y) := fun x y => by
    ext
    rw [hu, hu]
    show e.pair (Sr x - x) y = e.pair x (Sr' y - y)
    rw [sub_eq_add_neg, sub_eq_add_neg, e.pair_add_left, e.pair_add_right, hneg_left, hneg_right]
    exact congrArg (· * (e.pair x y)⁻¹) (hadj x y)
  have key := AddMonoidHom.natCard_ker_eq_natCard_ker_of_pairing_adjoint u hadd₁ hadd₂ hleft hright hsurj T T' hadjT

  have eT : ↥T.ker ≃ {x : ↥P // S (x : Pic0 K F) = x} :=
    Equiv.subtypeEquivRight fun x => by
      rw [AddMonoidHom.mem_ker]
      show Sr x - x = 0 ↔ _
      rw [sub_eq_zero, Subtype.ext_iff]
      rfl
  have eT' : ↥T'.ker ≃ {y : ↥P // S' (y : Pic0 K F) = y} :=
    Equiv.subtypeEquivRight fun y => by
      rw [AddMonoidHom.mem_ker]
      show Sr' y - y = 0 ↔ _
      rw [sub_eq_zero, Subtype.ext_iff]
      rfl
  rw [← Nat.card_congr eT, ← Nat.card_congr eT']
  exact key

theorem NoEig2.finite_fixedPoints_iterate_of_isOfFinAddOrder_of_bound
    {A : Type*} [AddCommGroup A] (p : ℕ) [hp : Fact p.Prime]
    (Fs : A →+ A) (N : ℕ) (hN : 0 < N)
    (hS1 : ∀ z : A, IsOfFinAddOrder z)
    (hS2 : ∀ (k : ℕ) (z : A), p ^ k • z = 0 → (⇑Fs)^[k] z = 0)
    (hS3 : ∃ B : ℕ, ∀ (n : ℕ), 0 < n → p.Coprime n →
      ∀ s : Finset A, (∀ z ∈ s, n • z = 0 ∧ (⇑Fs)^[N] z = z) → s.card ≤ B) :
    (Function.fixedPoints (⇑Fs)^[N]).Finite := by
  classical
  obtain ⟨B, hB⟩ := hS3

  have hit_nsmul : ∀ (k n : ℕ) (z : A), (⇑Fs)^[k] (n • z) = n • (⇑Fs)^[k] z := fun k n z => by
    induction k generalizing z with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_nsmul]
  have hit_zero : ∀ k : ℕ, (⇑Fs)^[k] (0 : A) = 0 := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]

  have hcop : ∀ z ∈ Function.fixedPoints (⇑Fs)^[N], ∃ n : ℕ, 0 < n ∧ p.Coprime n ∧ n • z = 0 := by
    intro z hz
    have hz' : (⇑Fs)^[N] z = z := hz
    have ho : addOrderOf z ≠ 0 := (hS1 z).addOrderOf_pos.ne'
    obtain ⟨a, n, hpn, hon⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho p hp.out.one_lt.ne'
    refine ⟨n, Nat.pos_of_ne_zero ?_, (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpn, ?_⟩
    · rintro rfl
      rw [mul_zero] at hon
      exact ho hon
    ·
      have hwfix : (⇑Fs)^[N] (n • z) = n • z := by rw [hit_nsmul, hz']
      have hpw : p ^ a • n • z = 0 := by
        rw [smul_smul, ← hon]; exact addOrderOf_nsmul_eq_zero z
      have hkill : (⇑Fs)^[a] (n • z) = 0 := hS2 a (n • z) hpw

      have hfixa : (⇑Fs)^[N * a] (n • z) = n • z := by
        rw [Function.iterate_mul]; exact Function.iterate_fixed hwfix a
      have hle : a ≤ N * a := Nat.le_mul_of_pos_left a hN
      calc n • z = (⇑Fs)^[N * a] (n • z) := hfixa.symm
        _ = (⇑Fs)^[N * a - a + a] (n • z) := by rw [Nat.sub_add_cancel hle]
        _ = (⇑Fs)^[N * a - a] ((⇑Fs)^[a] (n • z)) := by rw [Function.iterate_add_apply]
        _ = 0 := by rw [hkill, hit_zero]
  choose! nz hnz using hcop

  by_contra hinf
  obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (B + 1)
  have key := hB (∏ z ∈ t, nz z) ?_ ?_ t ?_
  · omega
  · exact Finset.prod_pos fun z hz => (hnz z (ht hz)).1
  · exact Nat.Coprime.prod_right fun z hz => (hnz z (ht hz)).2.1
  · intro z hz
    refine ⟨?_, ht hz⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem nz hz
    rw [hc, mul_comm, mul_smul, (hnz z (ht hz)).2.2, smul_zero]

namespace NoEig2

def iterHom {A : Type*} [AddZeroClass A] (f : A →+ A) : ℕ → (A →+ A)
  | 0 => AddMonoidHom.id A
  | k + 1 => (iterHom f k).comp f

theorem iterHom_apply {A : Type*} [AddZeroClass A] (f : A →+ A) (k : ℕ) (x : A) :
    iterHom f k x = (⇑f)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    show iterHom f k (f x) = _
    exact ih (f x)

theorem map_mem_torsion' {K F : Type*} [Field K] [Field F] [Algebra K F] (f : Pic0 K F →+ Pic0 K F) {n : ℕ}
    (x : Pic0 K F) (hx : x ∈ Pic0.torsion K F n) : f x ∈ Pic0.torsion K F n :=
  NoEig2S3.map_mem_torsion f hx

theorem iterate_mem_torsion {K F : Type*} [Field K] [Field F] [Algebra K F] (f : Pic0 K F →+ Pic0 K F) {n : ℕ}
    (k : ℕ) (x : Pic0 K F) (hx : x ∈ Pic0.torsion K F n) : (⇑f)^[k] x ∈ Pic0.torsion K F n := by
  induction k generalizing x with
  | zero => simpa using hx
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih _ (NoEig2S3.map_mem_torsion f hx)

theorem exists_algebra_ratFunc_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F]
    (j : F) (hj : Transcendental K j) (hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F) :
    ∃ (_ : Algebra (RatFunc K) F), IsScalarTower K (RatFunc K) F ∧ FiniteDimensional (RatFunc K) F := by
  obtain ⟨e, -⟩ := IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental K F j hj
  letI alg : Algebra (RatFunc K) (IntermediateField.adjoin K ({j} : Set F)) := e.symm.toAlgHom.toRingHom.toAlgebra
  letI algF : Algebra (RatFunc K) F :=
    ((algebraMap (IntermediateField.adjoin K ({j} : Set F)) F).comp e.symm.toAlgHom.toRingHom).toAlgebra
  haveI : IsScalarTower (RatFunc K) (IntermediateField.adjoin K ({j} : Set F)) F :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  refine ⟨algF, ?_, ?_⟩
  · refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    show algebraMap K F c = algebraMap (IntermediateField.adjoin K ({j} : Set F)) F (e.symm.toAlgHom (algebraMap K (RatFunc K) c))
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply K (IntermediateField.adjoin K ({j} : Set F)) F c
  · haveI : Module.Finite (RatFunc K) (IntermediateField.adjoin K ({j} : Set F)) :=
      Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) (IntermediateField.adjoin K ({j} : Set F))) e.symm.surjective
    exact Module.Finite.trans (IntermediateField.adjoin K ({j} : Set F)) F

theorem s3_bound
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (halg : ∀ a : κ, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (F Finv Fstar : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (N : ℕ) (hN : 0 < N) :
    ∃ B : ℕ, ∀ (n : ℕ), 0 < n → p.Coprime n →
      ∀ s : Finset (Pic0 κ (Fbar p M H hpM κ)), (∀ z ∈ s, n • z = 0 ∧ (⇑Fstar)^[N] z = z) → s.card ≤ B := by
  classical
  have hp : p.Prime := Fact.out

  have hT : ModularGroup.T ∈ ΓN p M H hpM := translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  haveI hCO : IsCurveOver κ (Fbar p M H hpM κ) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed κ (ΓN p M H hpM) hT
  obtain ⟨j, -, hjt, hjfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed κ (ΓN p M H hpM) hT
  have hfg : ∃ x : Fbar p M H hpM κ, Transcendental κ x ∧
      FiniteDimensional (IntermediateField.adjoin κ ({x} : Set (Fbar p M H hpM κ))) (Fbar p M H hpM κ) := ⟨j, hjt, hjfd⟩

  obtain ⟨algR, hST, hFD⟩ := exists_algebra_ratFunc_of_transcendental (K := κ) j hjt hjfd
  letI := algR
  haveI := hST
  haveI := hFD
  haveI : ExpChar κ p := ExpChar.prime hp

  have hfix : (Function.fixedPoints (⇑F)^[N]).Finite :=
    ModularCurve.finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL p M H hpM hpM2 κ halg F hF N hN
  haveI : Finite (Function.fixedPoints (⇑F)^[N]) := hfix.to_subtype
  refine ⟨Nat.card (Function.fixedPoints (⇑F)^[N]), fun n hn hcop s hs => ?_⟩

  haveI : NeZero n := ⟨hn.ne'⟩
  have hnκ : (n : κ) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff κ p n] at h
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h)

  haveI hfinT : Finite (Pic0.torsion κ (Fbar p M H hpM κ) n) := by
    have h1 := (AlgebraicCurve.Pic0.finite_and_card_torsion_le_of_natCast_ne_zero κ (Fbar p M H hpM κ) hfg n hn.ne' hnκ).1
    refine Finite.of_injective (fun x : Pic0.torsion κ (Fbar p M H hpM κ) n =>
      (⟨(x : Pic0 κ (Fbar p M H hpM κ)), ?_⟩ : {c : Pic0 κ (Fbar p M H hpM κ) // n • c = 0})) ?_
    · have := Pic0.mem_torsion.mp x.2
      rwa [natCast_zsmul] at this
    · intro a b hab
      exact Subtype.ext (congrArg Subtype.val hab)

  obtain ⟨e⟩ := AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed κ (Fbar p M H hpM κ) hfg n
  have hperf : e.Perfect :=
    AlgebraicCurve.DivisorialWeilPairingData.perfect_of_divisible_coprime_of_isAlgClosed hnκ
      (fun L' _ _ _ _ _ => AlgebraicCurve.Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self κ p halg L') e

  have hS : ∀ x ∈ Pic0.torsion κ (Fbar p M H hpM κ) n, iterHom Fstar N x ∈ Pic0.torsion κ (Fbar p M H hpM κ) n :=
    fun x hx => by rw [iterHom_apply]; exact iterate_mem_torsion Fstar N x hx
  have hS' : ∀ y ∈ Pic0.torsion κ (Fbar p M H hpM κ) n, iterHom F N y ∈ Pic0.torsion κ (Fbar p M H hpM κ) n :=
    fun y hy => by rw [iterHom_apply]; exact iterate_mem_torsion F N y hy
  have hiter : ∀ (k : ℕ) (x y : Pic0.torsion κ (Fbar p M H hpM κ) n)
      (hx : (⇑Fstar)^[k] (x : Pic0 κ (Fbar p M H hpM κ)) ∈ Pic0.torsion κ (Fbar p M H hpM κ) n)
      (hy : (⇑F)^[k] (y : Pic0 κ (Fbar p M H hpM κ)) ∈ Pic0.torsion κ (Fbar p M H hpM κ) n),
      e.pair ⟨(⇑Fstar)^[k] x, hx⟩ y = e.pair x ⟨(⇑F)^[k] y, hy⟩ := by
    intro k
    induction k with
    | zero => intro x y hx hy; rfl
    | succ k ih =>
      intro x y hx hy
      have hx1 : Fstar (x : Pic0 κ (Fbar p M H hpM κ)) ∈ Pic0.torsion κ (Fbar p M H hpM κ) n := NoEig2S3.map_mem_torsion Fstar x.2
      have hxk : (⇑Fstar)^[k] (Fstar (x : Pic0 κ (Fbar p M H hpM κ))) ∈ Pic0.torsion κ (Fbar p M H hpM κ) n :=
        iterate_mem_torsion Fstar k _ hx1
      have hyk : (⇑F)^[k] (y : Pic0 κ (Fbar p M H hpM κ)) ∈ Pic0.torsion κ (Fbar p M H hpM κ) n := iterate_mem_torsion F k _ y.2
      have hy1 : F ((⇑F)^[k] (y : Pic0 κ (Fbar p M H hpM κ))) ∈ Pic0.torsion κ (Fbar p M H hpM κ) n :=
        NoEig2S3.map_mem_torsion F hyk
      have e1 : (⟨(⇑Fstar)^[k + 1] (x : Pic0 κ (Fbar p M H hpM κ)), hx⟩ : Pic0.torsion κ (Fbar p M H hpM κ) n)
          = ⟨(⇑Fstar)^[k] (Fstar (x : Pic0 κ (Fbar p M H hpM κ))), hxk⟩ := Subtype.ext (Function.iterate_succ_apply _ _ _)
      have e2 : (⟨(⇑F)^[k + 1] (y : Pic0 κ (Fbar p M H hpM κ)), hy⟩ : Pic0.torsion κ (Fbar p M H hpM κ) n)
          = ⟨F ((⇑F)^[k] (y : Pic0 κ (Fbar p M H hpM κ))), hy1⟩ := Subtype.ext (Function.iterate_succ_apply' _ _ _)
      rw [e1, e2, ih ⟨Fstar x, hx1⟩ y hxk hyk]
      exact NoEig2S3.s3b p M H hpM hpM2 κ F Finv Fstar hF hFinv hFstar n hnκ e x ⟨(⇑F)^[k] y, hyk⟩ hx1 hy1
  have hadj : ∀ (x y : Pic0.torsion κ (Fbar p M H hpM κ) n),
      e.pair ⟨iterHom Fstar N x, hS x x.2⟩ y = e.pair x ⟨iterHom F N y, hS' y y.2⟩ := by
    intro x y
    have h1 : (⟨iterHom Fstar N x, hS x x.2⟩ : Pic0.torsion κ (Fbar p M H hpM κ) n)
        = ⟨(⇑Fstar)^[N] x, iterate_mem_torsion Fstar N _ x.2⟩ := Subtype.ext (iterHom_apply _ _ _)
    have h2 : (⟨iterHom F N y, hS' y y.2⟩ : Pic0.torsion κ (Fbar p M H hpM κ) n)
        = ⟨(⇑F)^[N] y, iterate_mem_torsion F N _ y.2⟩ := Subtype.ext (iterHom_apply _ _ _)
    rw [h1, h2]
    exact hiter N x y _ _
  have hcount := natCard_fixed_eq_of_perfect_of_adjoint e hperf (iterHom Fstar N) (iterHom F N) hS hS' hadj

  haveI : Finite {y : Pic0.torsion κ (Fbar p M H hpM κ) n // iterHom F N (y : Pic0 κ (Fbar p M H hpM κ)) = y} :=
    inferInstance
  have hle2 : Nat.card {y : Pic0.torsion κ (Fbar p M H hpM κ) n // iterHom F N (y : Pic0 κ (Fbar p M H hpM κ)) = y}
      ≤ Nat.card (Function.fixedPoints (⇑F)^[N]) := by
    refine Nat.card_le_card_of_injective (fun y => ⟨((y.1 : Pic0.torsion κ (Fbar p M H hpM κ) n) : Pic0 κ (Fbar p M H hpM κ)), ?_⟩) ?_
    · have := y.2
      rw [iterHom_apply] at this
      exact this
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      dsimp only at h1
      exact Subtype.ext (Subtype.ext h1)
  haveI : Finite {x : Pic0.torsion κ (Fbar p M H hpM κ) n // iterHom Fstar N (x : Pic0 κ (Fbar p M H hpM κ)) = x} :=
    inferInstance
  have hle1 : s.card ≤ Nat.card {x : Pic0.torsion κ (Fbar p M H hpM κ) n // iterHom Fstar N (x : Pic0 κ (Fbar p M H hpM κ)) = x} := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun z => ⟨⟨(z : Pic0 κ (Fbar p M H hpM κ)), ?_⟩, ?_⟩) ?_
    · rw [Pic0.mem_torsion, natCast_zsmul]; exact (hs z z.2).1
    · show iterHom Fstar N (z : Pic0 κ (Fbar p M H hpM κ)) = z
      rw [iterHom_apply]; exact (hs z z.2).2
    · intro a b hab
      have h1 : (a : Pic0 κ (Fbar p M H hpM κ)) = b :=
        congrArg (fun w : {x : Pic0.torsion κ (Fbar p M H hpM κ) n // iterHom Fstar N (x : Pic0 κ (Fbar p M H hpM κ)) = x} =>
          ((w.1 : Pic0.torsion κ (Fbar p M H hpM κ) n) : Pic0 κ (Fbar p M H hpM κ))) hab
      exact Subtype.ext h1
  calc s.card ≤ _ := hle1
    _ = _ := hcount
    _ ≤ _ := hle2

end NoEig2

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]

    (halg : ∀ a : κ, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)

    (F Finv Fstar : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ)
    (δ δ' : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL κ (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)
    (hδδ' : δ.comp δ' = AddMonoidHom.id _ ∧ δ'.comp δ = AddMonoidHom.id _) :
    {z : Pic0 κ (Fbar p M H hpM κ) | δ' (Fstar (Fstar z)) = z}.Finite := by
  classical

  obtain ⟨m, hm, hδm⟩ := ModularCurve.exists_iterate_diamond_eq_self_pic0_fbar p M H hpM hpM2 κ pb δ hδ

  have hδδ'1 : ∀ z, δ (δ' z) = z := fun z => by
    have := congrArg (fun f : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ) => f z) hδδ'.1
    simpa using this
  have hδ'δ1 : ∀ z, δ' (δ z) = z := fun z => by
    have := congrArg (fun f : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ) => f z) hδδ'.2
    simpa using this
  have hδ'm : ∀ z, (⇑δ')^[m] z = z := by

    have key : ∀ (k : ℕ), Function.LeftInverse (⇑δ')^[k] (⇑δ)^[k] := fun k => Function.LeftInverse.iterate hδ'δ1 k
    intro z
    conv_lhs => rw [← hδm z]
    exact key m z

  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpN : ¬ p ∣ M / p := fun h => hpM2 (by
    obtain ⟨c, hc⟩ := h
    have : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
    rw [pow_two, this, hc, ← mul_assoc]; exact dvd_mul_right _ _)
  have hδF : ∀ z, δ (F z) = F (δ z) := fun z => by
    rw [hδ, hδ, hF, hF]
    exact (ModularCurve.qExpFrobeniusPushforwardModL_ofAlgAut_diamondActionModL_smul κ p (M / p) hpN
      (infSubgroup p M H hpM) pb z).symm
  have hFinv1 : ∀ z, F (Finv z) = z := fun z => by
    have := congrArg (fun f : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ) => f z) hFinv.1; simpa using this
  have hFinv2 : ∀ z, Finv (F z) = z := fun z => by
    have := congrArg (fun f : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ) => f z) hFinv.2; simpa using this
  have hδ'Finv : ∀ z, δ' (Finv z) = Finv (δ' z) := fun z => by

    have h1 : δ (F (δ' (Finv z))) = z := by rw [hδF, hδδ'1, hFinv1]
    have h2 : δ (F (Finv (δ' z))) = z := by rw [hFinv1, hδδ'1]
    have hinj : Function.Injective (fun w => δ (F w)) := fun a b hab => by
      have := congrArg (fun w => Finv (δ' w)) hab; simpa [hδ'δ1, hFinv2] using this
    exact hinj (h1.trans h2.symm)
  have hcomm : ∀ z, δ' (Fstar z) = Fstar (δ' z) := fun z => by
    rw [hFstar, hFstar, map_zsmul, hδ'Finv]
  have hK : {z : Pic0 κ (Fbar p M H hpM κ) | δ' (Fstar (Fstar z)) = z} ⊆ Function.fixedPoints (⇑Fstar)^[2 * m] := by
    intro z hz
    have hz' : (⇑δ' ∘ (⇑Fstar ∘ ⇑Fstar)) z = z := hz
    have hcm : Function.Commute (⇑δ') (⇑Fstar ∘ ⇑Fstar) := fun w => by
      show δ' (Fstar (Fstar w)) = Fstar (Fstar (δ' w)); rw [hcomm, hcomm]
    have hfix : (⇑δ' ∘ (⇑Fstar ∘ ⇑Fstar))^[m] z = z := Function.iterate_fixed hz' m
    rw [hcm.comp_iterate, Function.comp_apply] at hfix

    have h2 : (⇑Fstar ∘ ⇑Fstar)^[m] = (⇑Fstar)^[2 * m] := by
      rw [Function.iterate_mul]; rfl
    rw [h2, hδ'm] at hfix
    exact hfix
  refine Set.Finite.subset ?_ hK

  have hS1 : ∀ z : Pic0 κ (Fbar p M H hpM κ), IsOfFinAddOrder z :=
    fun z => ModularCurve.isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self p M H hpM hpM2 κ halg z
  have hS2 : ∀ (k : ℕ) (z : Pic0 κ (Fbar p M H hpM κ)), p ^ k • z = 0 → (⇑Fstar)^[k] z = 0 := by

    have hFs : ∀ y, Fstar y = Finv ((p : ℕ) • y) := fun y => by
      rw [hFstar, map_nsmul, natCast_zsmul]
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      rw [Function.iterate_succ_apply]
      apply ih

      rw [← map_nsmul, hFs, smul_smul, ← pow_succ', hz, map_zero]
  have hS3 : ∃ B : ℕ, ∀ (n : ℕ), 0 < n → p.Coprime n →
      ∀ s : Finset (Pic0 κ (Fbar p M H hpM κ)), (∀ z ∈ s, n • z = 0 ∧ (⇑Fstar)^[2 * m] z = z) → s.card ≤ B :=
    NoEig2.s3_bound p M H hpM hpM2 κ halg F Finv Fstar hF hFinv hFstar (2 * m) (Nat.mul_pos two_pos hm)

  exact NoEig2.finite_fixedPoints_iterate_of_isOfFinAddOrder_of_bound p Fstar (2 * m) (Nat.mul_pos two_pos hm) hS1 hS2 hS3

end S_ModularCurve_finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self
end P2MW
export P2MW.S_ModularCurve_finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self (solution)
