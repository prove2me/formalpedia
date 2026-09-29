-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/54379df2-142b-54de-8eb8-c1d7af47e5ca

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AddMonoidHom_finite_setOf_pushPull_eq_zero
import Theorems.Thm_ModularCurve_finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self
import Theorems.Thm_ModularCurve_finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self
import Theorems.Thm_ModularCurve_qExpFrobeniusPushforwardModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul
import Theorems.Thm_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq CohCarrier.frickeH1L_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left RatFunc.denom_X_pow RatFunc.powerBasisAdjoinXPow_dim RatFunc.powerBasisAdjoinXPow_gen RatFunc.intDegree_X_pow RatFunc.num_X_pow AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"
p2m_attr_erase "simp" "ValuationSubring.coe_toResidueValuationSubring AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

section SpecGen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace SpecGenFinite

section Sections

variable {Ω : Type u} [Field Ω] {W : Scheme.{u}} (f : W ⟶ Spec (CommRingCat.of Ω))

theorem comp_eq_id_of_comp_eq_id {K : Type u} [Field K] (ψ : Ω →+* K) (φ : K →+* Ω)
    (h : φ.comp ψ = RingHom.id Ω) : ψ.comp φ = RingHom.id K := by
  ext c
  apply φ.injective
  have := congrArg (fun r => r (φ c)) h
  simpa using this

theorem section_ext {σ σ' : Spec (CommRingCat.of Ω) ⟶ W} (hσ : σ ≫ f = 𝟙 _) (hσ' : σ' ≫ f = 𝟙 _)
    (h : σ.base (IsLocalRing.closedPoint Ω) = σ'.base (IsLocalRing.closedPoint Ω)) : σ = σ' := by

  obtain ⟨⟨x, φ⟩, hx⟩ : ∃ q : Σ x : W, W.residueField x ⟶ CommRingCat.of Ω, (Scheme.SpecToEquivOfField Ω W) σ = q :=
    ⟨_, rfl⟩
  obtain ⟨⟨x', φ'⟩, hx'⟩ : ∃ q : Σ x : W, W.residueField x ⟶ CommRingCat.of Ω, (Scheme.SpecToEquivOfField Ω W) σ' = q :=
    ⟨_, rfl⟩
  have hσe : σ = Spec.map φ ≫ W.fromSpecResidueField x := by
    have := (Scheme.SpecToEquivOfField Ω W).symm_apply_apply σ
    rw [hx] at this
    exact this.symm
  have hσe' : σ' = Spec.map φ' ≫ W.fromSpecResidueField x' := by
    have := (Scheme.SpecToEquivOfField Ω W).symm_apply_apply σ'
    rw [hx'] at this
    exact this.symm
  have hxx : x = x' := by
    have h1 : σ.base (IsLocalRing.closedPoint Ω) = x := by
      rw [hσe]; simp
    have h2 : σ'.base (IsLocalRing.closedPoint Ω) = x' := by
      rw [hσe']; simp
    rw [← h1, ← h2, h]
  subst hxx

  obtain ⟨ψ, hψ⟩ : ∃ ψ : CommRingCat.of Ω ⟶ W.residueField x, Spec.map ψ = W.fromSpecResidueField x ≫ f :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hret : ∀ χ : W.residueField x ⟶ CommRingCat.of Ω, Spec.map χ ≫ W.fromSpecResidueField x ≫ f = 𝟙 _ →
      χ.hom.comp ψ.hom = RingHom.id Ω := by
    intro χ hχ
    rw [← hψ, ← Spec.map_comp] at hχ
    have h1 : ψ ≫ χ = 𝟙 _ := Spec.map_injective (by rw [hχ, Spec.map_id])
    have := congrArg (fun m => (m : CommRingCat.of Ω ⟶ CommRingCat.of Ω).hom) h1
    simpa using this
  have hφ : φ.hom.comp ψ.hom = RingHom.id Ω := hret φ (by rw [← Category.assoc, ← hσe]; exact hσ)
  have hφ' : φ'.hom.comp ψ.hom = RingHom.id Ω := hret φ' (by rw [← Category.assoc, ← hσe']; exact hσ')
  have e1 := comp_eq_id_of_comp_eq_id ψ.hom φ.hom hφ
  have e2 := comp_eq_id_of_comp_eq_id ψ.hom φ'.hom hφ'
  have hφφ : φ = φ' := by
    ext c

    have h3 : ψ.hom (φ'.hom c) = c := by
      have := congrArg (fun r => r c) e2
      simpa using this
    have h4 : φ.hom (ψ.hom (φ'.hom c)) = φ'.hom c := by
      have := congrArg (fun r => r (φ'.hom c)) hφ
      simpa using this
    rw [h3] at h4
    exact h4
  rw [hσe, hσe', hφφ]

theorem finite_sections [Finite W] : {σ : Spec (CommRingCat.of Ω) ⟶ W | σ ≫ f = 𝟙 _}.Finite := by
  let ev : ↥{σ : Spec (CommRingCat.of Ω) ⟶ W | σ ≫ f = 𝟙 _} → W := fun σ => σ.1.base (IsLocalRing.closedPoint Ω)
  have hev : Function.Injective ev := fun σ σ' h => Subtype.ext (section_ext f σ.2 σ'.2 h)
  exact Set.finite_coe_iff.mp (Finite.of_injective ev hev)

end Sections

section GeometricFibre

variable {Z S : Scheme.{u}} (g : Z ⟶ S)
  {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S)

theorem finite_pullback_of_finite [LocallyOfFiniteType g]
    (hfin : {z : Spec (CommRingCat.of k) ⟶ Z | z ≫ g = s}.Finite) : Finite ↥(pullback g s) := by
  haveI := hfin.to_subtype

  haveI : JacobsonSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  haveI hJ : JacobsonSpace ↥(pullback g s) := LocallyOfFiniteType.jacobsonSpace (pullback.snd g s)

  let ι : closedPoints ↥(pullback g s) → ↥{z : Spec (CommRingCat.of k) ⟶ Z | z ≫ g = s} := fun x =>
    ⟨((pointEquivClosedPoint (pullback.snd g s)).symm x).1 ≫ pullback.fst g s, by
      rw [Set.mem_setOf_eq, Category.assoc, pullback.condition, ← Category.assoc,
        ((pointEquivClosedPoint (pullback.snd g s)).symm x).2, Category.id_comp]⟩
  have hι : Function.Injective ι := by
    intro x x' h
    have h' : ((pointEquivClosedPoint (pullback.snd g s)).symm x).1 ≫ pullback.fst g s =
        ((pointEquivClosedPoint (pullback.snd g s)).symm x').1 ≫ pullback.fst g s := congrArg Subtype.val h
    apply (pointEquivClosedPoint (pullback.snd g s)).symm.injective
    apply Subtype.ext
    apply pullback.hom_ext h'
    rw [((pointEquivClosedPoint (pullback.snd g s)).symm x).2, ((pointEquivClosedPoint (pullback.snd g s)).symm x').2]
  haveI hcl : Finite (closedPoints ↥(pullback g s)) := Finite.of_injective ι hι

  have hcl' : (closedPoints ↥(pullback g s)).Finite := Set.finite_coe_iff.mp hcl
  have hclosed : IsClosed (closedPoints ↥(pullback g s)) := by
    have : closedPoints ↥(pullback g s) = ⋃ x ∈ closedPoints ↥(pullback g s), {x} := by
      ext y; simp
    rw [this]
    exact hcl'.isClosed_biUnion fun x hx => hx
  have huniv : (Set.univ : Set ↥(pullback g s)) = closedPoints ↥(pullback g s) := by
    rw [← closure_closedPoints, hclosed.closure_eq]
  have : (Set.univ : Set ↥(pullback g s)).Finite := by rw [huniv]; exact hcl'
  exact Set.finite_univ_iff.mp this

private theorem _root_.SpecGenFinite.finite_preimage_singleton [LocallyOfFiniteType g]
    (hfin : {z : Spec (CommRingCat.of k) ⟶ Z | z ≫ g = s}.Finite) :
    (g.base ⁻¹' {s.base (IsLocalRing.closedPoint k)}).Finite := by
  haveI := finite_pullback_of_finite g s hfin
  have hr : Set.range s.base = {s.base (IsLocalRing.closedPoint k)} := by
    apply Set.range_eq_singleton_iff.mpr ?_ |>.symm.symm
    intro x
    exact congrArg s.base (Subsingleton.elim x _)
  have h := Scheme.Pullback.range_fst g s
  rw [hr] at h
  rw [← h]
  exact Set.finite_range _

p2m_export "SpecGenFinite" "finite_preimage_singleton"
end GeometricFibre

theorem finite_setOf_comp_eq_of_isProper_of_finite_of_specializes
    {Z S : Scheme.{u}} (g : Z ⟶ S) [IsProper g]
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S)
    (hfin : {z : Spec (CommRingCat.of k) ⟶ Z | z ≫ g = s}.Finite)
    {Ω : Type u} [Field Ω] (t : Spec (CommRingCat.of Ω) ⟶ S)
    (hst : t.base (IsLocalRing.closedPoint Ω) ⤳ s.base (IsLocalRing.closedPoint k)) :
    {z : Spec (CommRingCat.of Ω) ⟶ Z | z ≫ g = t}.Finite := by

  have hy := finite_preimage_singleton g s hfin

  obtain ⟨V, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton g _ hy

  have htV : t.base (IsLocalRing.closedPoint Ω) ∈ V := hst.mem_open V.2 hyV
  have hrange : Set.range t.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (IsLocalRing.closedPoint Ω)]
    exact htV

  set tV : Spec (CommRingCat.of Ω) ⟶ V := IsOpenImmersion.lift V.ι t hrange with htVdef
  have htV_fac : tV ≫ V.ι = t := IsOpenImmersion.lift_fac V.ι t hrange

  haveI : IsFinite (pullback.snd (g ∣_ V) tV) := inferInstance
  haveI hWfin : Finite ↥(pullback (g ∣_ V) tV) := by
    have h := (pullback.snd (g ∣_ V) tV).finite_preimage_singleton (IsLocalRing.closedPoint Ω)
    exact Set.finite_univ_iff.mp (h.subset fun w _ => Subsingleton.elim _ _)
  have hsec := finite_sections (pullback.snd (g ∣_ V) tV)
  haveI := hsec.to_subtype

  have hzrange : ∀ z : ↥{z : Spec (CommRingCat.of Ω) ⟶ Z | z ≫ g = t},
      Set.range z.1.base ⊆ Set.range (g ⁻¹ᵁ V).ι.base := by
    intro z
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (IsLocalRing.closedPoint Ω)]
    show g.base (z.1.base (IsLocalRing.closedPoint Ω)) ∈ V
    have : g.base (z.1.base (IsLocalRing.closedPoint Ω)) = t.base (IsLocalRing.closedPoint Ω) := by
      rw [← Scheme.Hom.comp_apply, z.2]
    rw [this]; exact htV
  have hzV : ∀ z : ↥{z : Spec (CommRingCat.of Ω) ⟶ Z | z ≫ g = t},
      IsOpenImmersion.lift (g ⁻¹ᵁ V).ι z.1 (hzrange z) ≫ (g ∣_ V) = tV := by
    intro z
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac, htV_fac]
    exact z.2
  let σ : ↥{z : Spec (CommRingCat.of Ω) ⟶ Z | z ≫ g = t} →
      ↥{σ : Spec (CommRingCat.of Ω) ⟶ pullback (g ∣_ V) tV | σ ≫ pullback.snd (g ∣_ V) tV = 𝟙 _} := fun z =>
    ⟨pullback.lift (IsOpenImmersion.lift (g ⁻¹ᵁ V).ι z.1 (hzrange z)) (𝟙 _) (by rw [hzV, Category.id_comp]),
      pullback.lift_snd _ _ _⟩
  have hσ : Function.Injective σ := by
    intro z z' h
    have h' : pullback.lift (IsOpenImmersion.lift (g ⁻¹ᵁ V).ι z.1 (hzrange z)) (𝟙 _) (by rw [hzV, Category.id_comp]) =
        pullback.lift (IsOpenImmersion.lift (g ⁻¹ᵁ V).ι z'.1 (hzrange z')) (𝟙 _) (by rw [hzV, Category.id_comp]) :=
      congrArg Subtype.val h
    have h1 := congrArg (fun m => m ≫ pullback.fst (g ∣_ V) tV ≫ (g ⁻¹ᵁ V).ι) h'
    simp only [pullback.lift_fst_assoc, IsOpenImmersion.lift_fac] at h1
    exact Subtype.ext h1
  exact Set.finite_coe_iff.mp (Finite.of_injective σ hσ)

end SpecGenFinite

end SpecGen

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace PPprimeKernelScheme

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

theorem comp_mul_coe (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x y : SchemeHomOver t f) :
    ψ ≫ (L.mul t x y).1 =
      (L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ y)).1 := by
  have h := congrArg Subtype.val (L.mul_natural t t' ψ hψ x y)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  exact h

theorem comp_one_coe (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    ψ ≫ (L.one t).1 = (L.one t').1 := by
  have h := congrArg Subtype.val (L.one_natural t t' ψ hψ)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  exact h

variable (f)

abbrev X2 : Scheme.{u} := pullback f f

abbrev π : X2 f ⟶ Spec (CommRingCat.of R) := pullback.fst f f ≫ f

def pfst : SchemeHomOver (π f) f := ⟨pullback.fst f f, rfl⟩

def psnd : SchemeHomOver (π f) f := ⟨pullback.snd f f, pullback.condition.symm⟩

variable {f}
variable (L : RelativeGroupLaw R f) (E : Fin 2 → Fin 2 → SchemeHomOver f f)

def rowMap (j : Fin 2) : X2 f ⟶ X :=
  (L.mul (π f) (pfst f ⊚ E j 0) (psnd f ⊚ E j 1)).1

theorem rowMap_comp (j : Fin 2) : rowMap L E j ≫ f = π f :=
  (L.mul (π f) (pfst f ⊚ E j 0) (psnd f ⊚ E j 1)).2

def unit : Spec (CommRingCat.of R) ⟶ X := (L.one (𝟙 _)).1

theorem unit_comp : unit L ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

abbrev Zrow (j : Fin 2) : Scheme.{u} := pullback (rowMap L E j) (unit L)

abbrev Z : Scheme.{u} :=
  pullback (pullback.fst (rowMap L E 0) (unit L)) (pullback.fst (rowMap L E 1) (unit L))

def toX2 : Z L E ⟶ X2 f :=
  pullback.fst (pullback.fst (rowMap L E 0) (unit L)) (pullback.fst (rowMap L E 1) (unit L)) ≫
    pullback.fst (rowMap L E 0) (unit L)

def toS : Z L E ⟶ Spec (CommRingCat.of R) := toX2 L E ≫ π f

theorem toS_eq : toS L E = toX2 L E ≫ π f := rfl

theorem toX2_eq :
    toX2 L E = pullback.fst (pullback.fst (rowMap L E 0) (unit L)) (pullback.fst (rowMap L E 1) (unit L)) ≫
      pullback.fst (rowMap L E 0) (unit L) := rfl

theorem toX2_eq_snd :
    toX2 L E = pullback.snd (pullback.fst (rowMap L E 0) (unit L)) (pullback.fst (rowMap L E 1) (unit L)) ≫
      pullback.fst (rowMap L E 1) (unit L) :=
  pullback.condition

scoped instance isProper_toS [IsProper f] : IsProper (toS L E) := by
  have h1 : IsProper (unit L) := by
    have : IsProper (unit L ≫ f) := by rw [unit_comp]; infer_instance
    exact IsProper.of_comp (unit L) f
  unfold toS toX2
  infer_instance

theorem lift_rowMap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x₀ x₁ : SchemeHomOver t f)
    (j : Fin 2) :
    pullback.lift x₀.1 x₁.1 (x₀.2.trans x₁.2.symm) ≫ rowMap L E j =
      (L.mul t (x₀ ⊚ E j 0) (x₁ ⊚ E j 1)).1 := by
  have hw : pullback.lift x₀.1 x₁.1 (x₀.2.trans x₁.2.symm) ≫ π f = t := by
    rw [← Category.assoc, pullback.lift_fst]; exact x₀.2
  rw [rowMap, comp_mul_coe L _ hw]
  congr 2
  · apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, pfst,
      pullback.lift_fst_assoc]
  · apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, psnd,
      pullback.lift_snd_assoc]

theorem one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : (L.one t).1 = t ≫ unit L := by
  rw [unit, comp_one_coe L t (Category.comp_id t)]

section Points

variable {L E}
variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

def fstPt (z : T ⟶ Z L E) (hz : z ≫ toS L E = t) : SchemeHomOver t f :=
  ⟨z ≫ toX2 L E ≫ pullback.fst f f, by
    have h := hz; rw [toS_eq] at h; simpa only [Category.assoc] using h⟩

def sndPt (z : T ⟶ Z L E) (hz : z ≫ toS L E = t) : SchemeHomOver t f :=
  ⟨z ≫ toX2 L E ≫ pullback.snd f f, by
    have h : pullback.snd f f ≫ f = pullback.fst f f ≫ f := pullback.condition.symm
    rw [Category.assoc, Category.assoc, h]
    have h' := hz; rw [toS_eq] at h'; simpa only [Category.assoc] using h'⟩

@[scoped simp] theorem fstPt_coe (z : T ⟶ Z L E) (hz : z ≫ toS L E = t) :
    (fstPt z hz).1 = z ≫ toX2 L E ≫ pullback.fst f f := rfl

@[scoped simp] theorem sndPt_coe (z : T ⟶ Z L E) (hz : z ≫ toS L E = t) :
    (sndPt z hz).1 = z ≫ toX2 L E ≫ pullback.snd f f := rfl

theorem lift_fstPt_sndPt (z : T ⟶ Z L E) (hz : z ≫ toS L E = t) :
    pullback.lift (fstPt z hz).1 (sndPt z hz).1 ((fstPt z hz).2.trans (sndPt z hz).2.symm) = z ≫ toX2 L E := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, fstPt_coe, Category.assoc]
  · rw [pullback.lift_snd, sndPt_coe, Category.assoc]

theorem comp_snd_zero (z : T ⟶ Z L E) (hz : z ≫ toS L E = t) :
    z ≫ pullback.fst _ _ ≫ pullback.snd (rowMap L E 0) (unit L) = t := by
  have h : z ≫ pullback.fst _ _ ≫ pullback.snd (rowMap L E 0) (unit L) =
      (z ≫ pullback.fst _ _ ≫ pullback.snd (rowMap L E 0) (unit L)) ≫ unit L ≫ f := by
    rw [unit_comp, Category.comp_id]
  rw [h, Category.assoc, Category.assoc, ← pullback.condition_assoc, rowMap_comp]
  rw [toS_eq, toX2_eq] at hz
  simpa only [Category.assoc] using hz

theorem comp_snd_one (z : T ⟶ Z L E) (hz : z ≫ toS L E = t) :
    z ≫ pullback.snd _ _ ≫ pullback.snd (rowMap L E 1) (unit L) = t := by
  have h : z ≫ pullback.snd _ _ ≫ pullback.snd (rowMap L E 1) (unit L) =
      (z ≫ pullback.snd _ _ ≫ pullback.snd (rowMap L E 1) (unit L)) ≫ unit L ≫ f := by
    rw [unit_comp, Category.comp_id]
  rw [h, Category.assoc, Category.assoc, ← pullback.condition_assoc, rowMap_comp]
  have h2 : z ≫ toS L E = z ≫ pullback.snd _ _ ≫ pullback.fst (rowMap L E 1) (unit L) ≫ π f := by
    rw [toS_eq, toX2_eq_snd, Category.assoc]
  rw [← h2]; exact hz

theorem mul_fstPt_sndPt (z : T ⟶ Z L E) (hz : z ≫ toS L E = t) (j : Fin 2) :
    L.mul t (fstPt z hz ⊚ E j 0) (sndPt z hz ⊚ E j 1) = L.one t := by
  apply Subtype.ext
  rw [← lift_rowMap, lift_fstPt_sndPt, one_coe]
  fin_cases j
  · show z ≫ toX2 L E ≫ rowMap L E 0 = t ≫ unit L
    rw [← comp_snd_zero z hz, toX2_eq, Category.assoc, Category.assoc, pullback.condition, Category.assoc]
  · show z ≫ toX2 L E ≫ rowMap L E 1 = t ≫ unit L
    rw [← comp_snd_one z hz, toX2_eq_snd, Category.assoc, Category.assoc, pullback.condition, Category.assoc]

theorem ext_of_fstPt_sndPt {z z' : T ⟶ Z L E} (hz : z ≫ toS L E = t) (hz' : z' ≫ toS L E = t)
    (h0 : (fstPt z hz).1 = (fstPt z' hz').1) (h1 : (sndPt z hz).1 = (sndPt z' hz').1) : z = z' := by
  have hX2 : z ≫ toX2 L E = z' ≫ toX2 L E := by
    rw [← lift_fstPt_sndPt z hz, ← lift_fstPt_sndPt z' hz']
    congr 1
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [toX2_eq] at hX2
      simpa only [Category.assoc] using hX2
    · rw [Category.assoc, Category.assoc, comp_snd_zero z hz, comp_snd_zero z' hz']
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ← toX2_eq_snd]
      exact hX2
    · rw [Category.assoc, Category.assoc, comp_snd_one z hz, comp_snd_one z' hz']

def liftPt (x₀ x₁ : SchemeHomOver t f) (h : ∀ j : Fin 2, L.mul t (x₀ ⊚ E j 0) (x₁ ⊚ E j 1) = L.one t) :
    T ⟶ Z L E :=
  pullback.lift
    (pullback.lift (pullback.lift x₀.1 x₁.1 (x₀.2.trans x₁.2.symm)) t
      (by rw [lift_rowMap, h 0, one_coe]))
    (pullback.lift (pullback.lift x₀.1 x₁.1 (x₀.2.trans x₁.2.symm)) t
      (by rw [lift_rowMap, h 1, one_coe]))
    (by rw [pullback.lift_fst, pullback.lift_fst])

theorem liftPt_toX2 (x₀ x₁ : SchemeHomOver t f)
    (h : ∀ j : Fin 2, L.mul t (x₀ ⊚ E j 0) (x₁ ⊚ E j 1) = L.one t) :
    liftPt x₀ x₁ h ≫ toX2 L E = pullback.lift x₀.1 x₁.1 (x₀.2.trans x₁.2.symm) := by
  rw [liftPt, toX2_eq, pullback.lift_fst_assoc, pullback.lift_fst]

theorem liftPt_toS (x₀ x₁ : SchemeHomOver t f)
    (h : ∀ j : Fin 2, L.mul t (x₀ ⊚ E j 0) (x₁ ⊚ E j 1) = L.one t) :
    liftPt x₀ x₁ h ≫ toS L E = t := by
  rw [toS_eq, ← Category.assoc, liftPt_toX2, ← Category.assoc, pullback.lift_fst]
  exact x₀.2

theorem fstPt_liftPt (x₀ x₁ : SchemeHomOver t f)
    (h : ∀ j : Fin 2, L.mul t (x₀ ⊚ E j 0) (x₁ ⊚ E j 1) = L.one t) :
    (fstPt (liftPt x₀ x₁ h) (liftPt_toS x₀ x₁ h)).1 = x₀.1 := by
  rw [fstPt_coe, ← Category.assoc, liftPt_toX2, pullback.lift_fst]

theorem sndPt_liftPt (x₀ x₁ : SchemeHomOver t f)
    (h : ∀ j : Fin 2, L.mul t (x₀ ⊚ E j 0) (x₁ ⊚ E j 1) = L.one t) :
    (sndPt (liftPt x₀ x₁ h) (liftPt_toS x₀ x₁ h)).1 = x₁.1 := by
  rw [sndPt_coe, ← Category.assoc, liftPt_toX2, pullback.lift_snd]

end Points

end PPprimeKernelScheme
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.PPprimeKernelScheme"

end
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.PPprimeKernelScheme"

section Dict

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.ModularCurve ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP diamondActionModL infSubgroup xHFunctionFieldBar JH qExpFunctionFieldC qExpand qExpFrobeniusPushforwardModL jqModC JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self qExpFrobeniusPushforwardModL_ofAlgAut_diamondActionModL_smul diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "ΓN Fbar LevelData ptsSp mk.injEq abqFibre_ptsSp ssFinset mk pts g pts_add degeneracyHom_pts separated degeneracyHom_special degPts degeneracyHom G ptsSp_add L"
namespace PPprimeDict
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

section Generic

variable (Λ : LevelData p M H hpM A)

theorem pts_zero
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y)) :
    Λ.pts 0 = Λ.L.one (genPt p) := by
  letI := Λ.L.pointGroup (genPt p)
  have h : Λ.pts 0 * Λ.pts 0 = Λ.pts 0 := by
    show Λ.L.mul _ (Λ.pts 0) (Λ.pts 0) = Λ.pts 0
    rw [← hΛpts_add, add_zero]
  exact mul_eq_left.mp h

variable {Λ}

theorem pts_degPts_pull (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (i j : Fin 2) (a : JH (M / p) (infSubgroup p M H hpM)) :
    Λ.pts (O.degPts j (αpull i a)) = Λ.pts a ⊚ (degPull i ⊚ O.degeneracyHom j) := by
  apply Subtype.ext
  rw [O.degeneracyHom_pts, hpull, NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
    Category.assoc]

theorem mul_pts_eq_one_of_degPts_eq_zero (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (a b : JH (M / p) (infSubgroup p M H hpM)) (j : Fin 2)
    (h : O.degPts j (αpull 0 a + αpull 1 b) = 0) :
    Λ.L.mul (genPt p) (Λ.pts a ⊚ (degPull 0 ⊚ O.degeneracyHom j)) (Λ.pts b ⊚ (degPull 1 ⊚ O.degeneracyHom j)) =
      Λ.L.one (genPt p) := by
  rw [← pts_degPts_pull O αpull degPull hpull, ← pts_degPts_pull O αpull degPull hpull, ← hΛpts_add,
    ← map_add, h, pts_zero Λ hΛpts_add]

end Generic
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.PPprimeKernelScheme"

section Special

variable {Λ : LevelData p M H hpM A}

theorem toFibrePt_coe {ι : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ base p} (x : SchemeHomOver ι Λ.f) :
    (toFibrePt x).1 = pullback.lift x.1 (𝟙 _) (by rw [Category.id_comp]; exact x.2) := rfl

theorem ofFibrePt_coe {ι : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ base p}
    (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι Λ.f)) :
    (ofFibrePt y).1 = y.1 ≫ pullback.fst _ _ := rfl

theorem baseChangePointToBase_toFibrePt {ι : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ base p}
    (x : SchemeHomOver ι Λ.f) :
    RelativeGroupLaw.baseChangePointToBase ι (toFibrePt x) = overId x := by
  rw [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]

theorem ptsSp_symm_mul
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (x y : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f) :
    Λ.ptsSp.symm (Λ.L.mul _ x y) = Λ.ptsSp.symm x + Λ.ptsSp.symm y := by
  apply Λ.ptsSp.injective
  rw [Equiv.apply_symm_apply, hΛptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [ofFibrePt_coe, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
    baseChangePointToBase_toFibrePt, baseChangePointToBase_toFibrePt]
  have h := congrArg Subtype.val (Λ.L.mul_natural (resPt A ≫ Λ.σA) (𝟙 _ ≫ (resPt A ≫ Λ.σA)) (𝟙 _) rfl x y)
  rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at h
  have e : ∀ z : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f,
      GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl z = overId z :=
    fun z => Subtype.ext (Category.id_comp _)
  rw [e, e] at h
  exact h

theorem ptsSp_symm_one
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y)))) :
    Λ.ptsSp.symm (Λ.L.one (resPt A ≫ Λ.σA)) = 0 := by
  have h := ptsSp_symm_mul hΛptsSp_add (Λ.L.one (resPt A ≫ Λ.σA)) (Λ.L.one (resPt A ≫ Λ.σA))
  rw [Λ.L.one_mul] at h
  exact left_eq_add.mp h

set_option maxHeartbeats 6400000 in

theorem ptsSp_symm_pull_zero_deg [NeZero (M / p)] (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (Fstar δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))
    (ē : (ZMod (M / p))ˣ) (hē : ((ē : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) :
    Λ.ptsSp.symm ((Λ.ptsSp z ⊚ degPull 0) ⊚ O.degeneracyHom 0) =
        z + qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p (Fstar z) ∧
      Λ.ptsSp.symm ((Λ.ptsSp z ⊚ degPull 0) ⊚ O.degeneracyHom 1) =
        qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z +
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) ē)) • Fstar z := by
  have hsp := O.degeneracyHom_special ē hē (Λ.ptsSp z ⊚ degPull 0)
  have h0 := O.abqFibre_ptsSp (O.ptsSp.symm (Λ.ptsSp z ⊚ degPull 0)) 0
  rw [Equiv.apply_symm_apply, if_pos rfl] at h0
  have h1 := O.abqFibre_ptsSp (O.ptsSp.symm (Λ.ptsSp z ⊚ degPull 0)) 1
  rw [Equiv.apply_symm_apply, if_neg (by decide)] at h1
  have hpair := hpullsp 0 (Λ.ptsSp z)
  rw [Equiv.symm_apply_apply, if_pos rfl] at hpair
  rw [h0, h1, hpair] at hsp
  exact hsp

set_option maxHeartbeats 6400000 in

theorem ptsSp_symm_pull_one_deg [NeZero (M / p)] (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (Fstar δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))
    (ē : (ZMod (M / p))ˣ) (hē : ((ē : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) :
    Λ.ptsSp.symm ((Λ.ptsSp z ⊚ degPull 1) ⊚ O.degeneracyHom 0) =
        Fstar z + qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p (δ z) ∧
      Λ.ptsSp.symm ((Λ.ptsSp z ⊚ degPull 1) ⊚ O.degeneracyHom 1) =
        qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p (Fstar z) +
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) ē)) • δ z := by
  have hsp := O.degeneracyHom_special ē hē (Λ.ptsSp z ⊚ degPull 1)
  have h0 := O.abqFibre_ptsSp (O.ptsSp.symm (Λ.ptsSp z ⊚ degPull 1)) 0
  rw [Equiv.apply_symm_apply, if_pos rfl] at h0
  have h1 := O.abqFibre_ptsSp (O.ptsSp.symm (Λ.ptsSp z ⊚ degPull 1)) 1
  rw [Equiv.apply_symm_apply, if_neg (by decide)] at h1
  have hpair := hpullsp 1 (Λ.ptsSp z)
  rw [Equiv.symm_apply_apply, if_neg (by decide)] at hpair
  rw [h0, h1, hpair] at hsp
  exact hsp

noncomputable def dia [NeZero (M / p)] (A : ValuationSubring (AlgebraicClosure ℚ)) (d : (ZMod (M / p))ˣ) :
    Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+ Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
  DistribSMul.toAddMonoidHom _
    (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) d)))

theorem dia_apply [NeZero (M / p)] (d : (ZMod (M / p))ˣ) (z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) :
    dia (hpM := hpM) A d z =
      SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) d)) • z := rfl

set_option maxHeartbeats 6400000 in

theorem finite_specialMatrix_ker [NeZero (M / p)] (hA : A.LiesOverPrime p) (hpM2 : ¬ p ^ 2 ∣ M)
    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z) :
    {ab : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) |
      (1 + p) • ab.1 + (Fstar ab.2 + F (δ ab.2)) = 0 ∧
      (F ab.1 + dia A pb⁻¹ (Fstar ab.1)) + (1 + p) • ab.2 = 0}.Finite := by
  have hp : p.Prime := Fact.out
  have hpN : ¬ p ∣ M / p := by
    intro h; apply hpM2; obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [pow_two, mul_assoc, ← hk, mul_comm, Nat.div_mul_cancel hpM]⟩
  have hδ' : δ = dia A pb := AddMonoidHom.ext fun z => by rw [hδ, dia_apply]
  obtain ⟨-, -, -, -, -, -, hdia⟩ :=
    ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul.{0}
      (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
  have hδδi : ∀ z, δ (dia A pb⁻¹ z) = z := fun z => by
    rw [hδ', dia_apply, dia_apply]; exact (hdia (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) z pb).1
  have hδiδ : ∀ z, dia A pb⁻¹ (δ z) = z := fun z => by
    rw [hδ', dia_apply, dia_apply]; exact (hdia (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) z pb).2
  have hFV : ∀ z, F (Fstar z) = p • z := fun z => by
    rw [hFstar, map_zsmul, ← AddMonoidHom.comp_apply, hFinv.1, AddMonoidHom.id_apply, natCast_zsmul]
  have hVF : ∀ z, Fstar (F z) = p • z := fun z => by
    rw [hFstar, ← AddMonoidHom.comp_apply, hFinv.2, AddMonoidHom.id_apply, natCast_zsmul]
  have hFD : ∀ (d : (ZMod (M / p))ˣ) (z), F (dia A d z) = dia A d (F z) := fun d z => by
    rw [dia_apply, dia_apply, hF, hF]
    exact ModularCurve.qExpFrobeniusPushforwardModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
      (infSubgroup p M H hpM) d z
  have hFinvD : ∀ (d : (ZMod (M / p))ˣ) (z), Finv (dia A d z) = dia A d (Finv z) := fun d z => by
    have h1 : ∀ w, F (Finv w) = w := fun w => by
      rw [← AddMonoidHom.comp_apply, hFinv.1, AddMonoidHom.id_apply]
    have h2 : ∀ w, Finv (F w) = w := fun w => by
      rw [← AddMonoidHom.comp_apply, hFinv.2, AddMonoidHom.id_apply]
    calc Finv (dia A d z) = Finv (dia A d (F (Finv z))) := by rw [h1]
      _ = Finv (F (dia A d (Finv z))) := by rw [hFD]
      _ = dia A d (Finv z) := h2 _
  have hVD : ∀ (d : (ZMod (M / p))ˣ) (z), Fstar (dia A d z) = dia A d (Fstar z) := fun d z => by
    rw [hFstar, hFstar, hFinvD, map_zsmul]
  have halg : ∀ a : ResidueField ↥A, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a :=
    fun a => ValuationSubring.exists_pow_pow_eq_self_residueField_of_liesOverPrime A hp hA a
  have hNE1 : {x : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) | x - δ (F (F x)) = 0}.Finite := by
    have h := ModularCurve.finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self p M H hpM hpM2
      (ResidueField ↥A) halg F hF pb δ hδ
    refine h.subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact (sub_eq_zero.mp hx).symm
  have hNE2 : {x : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) |
      x - dia A pb⁻¹ (Fstar (Fstar x)) = 0}.Finite := by
    have h := ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self p M H hpM hpM2
      (ResidueField ↥A) halg F Finv Fstar hF hFinv hFstar pb δ (dia A pb⁻¹) hδ
      ⟨AddMonoidHom.ext hδδi, AddMonoidHom.ext hδiδ⟩
    refine h.subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact (sub_eq_zero.mp hx).symm
  exact AddMonoidHom.finite_setOf_pushPull_eq_zero p F Fstar δ (dia A pb⁻¹)
    (AddMonoidHom.ext hFV) (AddMonoidHom.ext hVF) (AddMonoidHom.ext hδδi) (AddMonoidHom.ext hδiδ)
    (AddMonoidHom.ext fun z => by rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hδ', hFD])
    (AddMonoidHom.ext fun z => by rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hδ', hVD])
    (AddMonoidHom.ext fun z => by rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hFD])
    (AddMonoidHom.ext fun z => by rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hVD])
    hNE1 hNE2

noncomputable def pushPullMatrix (O : JHNeronObjectAtP p M H hpM A hA Λ) (degPull : Fin 2 → SchemeHomOver Λ.f O.g) :
    Fin 2 → Fin 2 → SchemeHomOver Λ.f Λ.f :=
  fun j i => degPull i ⊚ O.degeneracyHom j

theorem pushPullMatrix_apply (O : JHNeronObjectAtP p M H hpM A hA Λ) (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (j i : Fin 2) : pushPullMatrix O degPull j i = degPull i ⊚ O.degeneracyHom j := rfl

set_option maxHeartbeats 6400000 in

theorem finite_specialPoints_kernelScheme [NeZero (M / p)] (hA' : A.LiesOverPrime p) (hpM2 : ¬ p ^ 2 ∣ M)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y)))) :
    {z : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ PPprimeKernelScheme.Z Λ.L (pushPullMatrix O degPull) |
      z ≫ PPprimeKernelScheme.toS Λ.L (pushPullMatrix O degPull) = resPt A ≫ Λ.σA}.Finite := by
  have hKfin := finite_specialMatrix_ker hA' hpM2 F Finv Fstar hF hFinv hFstar pb δ hδ
  haveI := hKfin.to_subtype
  have hFV : ∀ z, F (Fstar z) = p • z := fun z => by
    rw [hFstar, map_zsmul, ← AddMonoidHom.comp_apply, hFinv.1, AddMonoidHom.id_apply, natCast_zsmul]
  have hē : (((pb⁻¹ : (ZMod (M / p))ˣ) : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 := by
    rw [← hpb, Units.inv_mul]
  obtain ⟨-, -, -, -, -, -, hdia⟩ :=
    ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul.{0}
      (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
  have hδiδ : ∀ z, dia A pb⁻¹ (δ z) = z := fun z => by
    rw [hδ, dia_apply]; exact (hdia (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) z pb).2

  have hmem : ∀ z : ↥{z : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ PPprimeKernelScheme.Z Λ.L (pushPullMatrix O degPull) |
      z ≫ PPprimeKernelScheme.toS Λ.L (pushPullMatrix O degPull) = resPt A ≫ Λ.σA},
      (Λ.ptsSp.symm (PPprimeKernelScheme.fstPt z.1 z.2), Λ.ptsSp.symm (PPprimeKernelScheme.sndPt z.1 z.2)) ∈
        {ab : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) |
          (1 + p) • ab.1 + (Fstar ab.2 + F (δ ab.2)) = 0 ∧
          (F ab.1 + dia A pb⁻¹ (Fstar ab.1)) + (1 + p) • ab.2 = 0} := by
    intro z
    have hker := fun j => PPprimeKernelScheme.mul_fstPt_sndPt (L := Λ.L) (E := pushPullMatrix O degPull) z.1 z.2 j
    have hrow : ∀ j : Fin 2,
        Λ.ptsSp.symm ((Λ.ptsSp (Λ.ptsSp.symm (PPprimeKernelScheme.fstPt z.1 z.2)) ⊚ degPull 0) ⊚ O.degeneracyHom j) +
          Λ.ptsSp.symm ((Λ.ptsSp (Λ.ptsSp.symm (PPprimeKernelScheme.sndPt z.1 z.2)) ⊚ degPull 1) ⊚ O.degeneracyHom j) = 0 := by
      intro j
      have h := congrArg Λ.ptsSp.symm (hker j)
      rw [ptsSp_symm_mul hΛptsSp_add, ptsSp_symm_one hΛptsSp_add, pushPullMatrix_apply, pushPullMatrix_apply,
        ← NeronModelInfra.schemeHomOverComp_assoc, ← NeronModelInfra.schemeHomOverComp_assoc] at h
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact h
    have c0 := ptsSp_symm_pull_zero_deg O Fstar δ degPull hpullsp pb⁻¹ hē (Λ.ptsSp.symm (PPprimeKernelScheme.fstPt z.1 z.2))
    have c1 := ptsSp_symm_pull_one_deg O Fstar δ degPull hpullsp pb⁻¹ hē (Λ.ptsSp.symm (PPprimeKernelScheme.sndPt z.1 z.2))
    have r0 := hrow 0
    have r1 := hrow 1
    rw [c0.1, c1.1, ← hF, ← hF, hFV] at r0
    rw [c0.2, c1.2, ← hF, ← hF, hFV, ← dia_apply, ← dia_apply, hδiδ] at r1
    refine ⟨?_, ?_⟩
    · rw [add_nsmul, one_nsmul]
      simpa only [add_assoc] using r0
    · rw [add_nsmul, one_nsmul, add_comm (Λ.ptsSp.symm (PPprimeKernelScheme.sndPt z.1 z.2))
        (p • Λ.ptsSp.symm (PPprimeKernelScheme.sndPt z.1 z.2))]
      simpa only [add_assoc] using r1
  let φ : ↥{z : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ PPprimeKernelScheme.Z Λ.L (pushPullMatrix O degPull) |
      z ≫ PPprimeKernelScheme.toS Λ.L (pushPullMatrix O degPull) = resPt A ≫ Λ.σA} →
      ↥{ab : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) |
          (1 + p) • ab.1 + (Fstar ab.2 + F (δ ab.2)) = 0 ∧
          (F ab.1 + dia A pb⁻¹ (Fstar ab.1)) + (1 + p) • ab.2 = 0} := fun z => ⟨_, hmem z⟩
  have hφ : Function.Injective φ := by
    intro z z' h
    have h' := congrArg Subtype.val h
    simp only [φ, Prod.mk.injEq] at h'
    apply Subtype.ext
    apply PPprimeKernelScheme.ext_of_fstPt_sndPt z.2 z'.2
    · exact congrArg Subtype.val (Λ.ptsSp.symm.injective h'.1)
    · exact congrArg Subtype.val (Λ.ptsSp.symm.injective h'.2)
  exact Set.finite_coe_iff.mp (Finite.of_injective φ hφ)

noncomputable def pushPullKer (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H)) :
    AddSubgroup (JH (M / p) (infSubgroup p M H hpM) × JH (M / p) (infSubgroup p M H hpM)) :=
  ⨅ j : Fin 2, (((O.degPts j).comp (αpull 0)).coprod ((O.degPts j).comp (αpull 1))).ker

theorem mem_pushPullKer (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (ab : JH (M / p) (infSubgroup p M H hpM) × JH (M / p) (infSubgroup p M H hpM)) :
    ab ∈ pushPullKer O αpull ↔ ∀ j : Fin 2, O.degPts j (αpull 0 ab.1 + αpull 1 ab.2) = 0 := by
  simp only [pushPullKer, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, AddMonoidHom.coprod_apply,
    AddMonoidHom.comp_apply, map_add]

theorem finite_pushPullKer_of_finite (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (hgenfin : {z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ PPprimeKernelScheme.Z Λ.L (pushPullMatrix O degPull) |
      z ≫ PPprimeKernelScheme.toS Λ.L (pushPullMatrix O degPull) = genPt p}.Finite) :
    Finite ↥(pushPullKer O αpull) := by
  haveI := hgenfin.to_subtype
  have hk : ∀ ab : ↥(pushPullKer O αpull), ∀ j : Fin 2,
      Λ.L.mul (genPt p) (Λ.pts ab.1.1 ⊚ pushPullMatrix O degPull j 0) (Λ.pts ab.1.2 ⊚ pushPullMatrix O degPull j 1) =
        Λ.L.one (genPt p) := fun ab j =>
    mul_pts_eq_one_of_degPts_eq_zero O hΛpts_add αpull degPull hpull ab.1.1 ab.1.2 j
      (((mem_pushPullKer O αpull ab.1).mp ab.2) j)
  let ψ : ↥(pushPullKer O αpull) →
      ↥{z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ PPprimeKernelScheme.Z Λ.L (pushPullMatrix O degPull) |
        z ≫ PPprimeKernelScheme.toS Λ.L (pushPullMatrix O degPull) = genPt p} := fun ab =>
    ⟨PPprimeKernelScheme.liftPt (Λ.pts ab.1.1) (Λ.pts ab.1.2) (hk ab), PPprimeKernelScheme.liftPt_toS _ _ _⟩
  refine Finite.of_injective ψ ?_
  intro ab ab' h
  have h' : PPprimeKernelScheme.liftPt (Λ.pts ab.1.1) (Λ.pts ab.1.2) (hk ab) =
      PPprimeKernelScheme.liftPt (Λ.pts ab'.1.1) (Λ.pts ab'.1.2) (hk ab') := congrArg Subtype.val h
  have h0 := PPprimeKernelScheme.fstPt_liftPt (Λ.pts ab.1.1) (Λ.pts ab.1.2) (hk ab)
  have h1 := PPprimeKernelScheme.sndPt_liftPt (Λ.pts ab.1.1) (Λ.pts ab.1.2) (hk ab)
  have h0' := PPprimeKernelScheme.fstPt_liftPt (Λ.pts ab'.1.1) (Λ.pts ab'.1.2) (hk ab')
  have h1' := PPprimeKernelScheme.sndPt_liftPt (Λ.pts ab'.1.1) (Λ.pts ab'.1.2) (hk ab')
  rw [PPprimeKernelScheme.fstPt_coe] at h0 h0'
  rw [PPprimeKernelScheme.sndPt_coe] at h1 h1'
  rw [h'] at h0 h1
  rw [h0'] at h0
  rw [h1'] at h1
  have e0 : ab.1.1 = ab'.1.1 := Λ.pts.injective (Subtype.ext h0.symm)
  have e1 : ab.1.2 = ab'.1.2 := Λ.pts.injective (Subtype.ext h1.symm)
  exact Subtype.ext (Prod.ext e0 e1)

end Special
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.PPprimeKernelScheme"

end ModularCurve.JHNeronObjectAtP.PPprimeDict
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.PPprimeKernelScheme"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.PPprimeKernelScheme"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.PPprimeKernelScheme"

end Dict
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.PPprimeKernelScheme"

section Card

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.ModularCurve ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

p2m_open "ModularCurve.XHDRLevel~ΓN"
open _root_.ModularCurve.JHNeronObjectAtP (ΓN Fbar)
open scoped MatrixGroups

theorem PPprimeCard.genPt_specializes (p : ℕ) (x : Spec (CommRingCat.of (baseRing p))) :
    (genPt p).base (closedPoint (AlgebraicClosure ℚ)) ⤳ x := by
  have h : ((genPt p).base (closedPoint (AlgebraicClosure ℚ))).asIdeal = ⊥ := by
    rw [genPt]
    show (PrimeSpectrum.comap _ (closedPoint (AlgebraicClosure ℚ))).asIdeal = ⊥
    rw [PrimeSpectrum.comap_asIdeal]
    rw [le_bot_iff.symm]
    intro r hr
    rw [Ideal.mem_comap] at hr
    have hr' : algebraMap (baseRing p) (AlgebraicClosure ℚ) r ∈ maximalIdeal (AlgebraicClosure ℚ) := hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hr'
    have hinj : Function.Injective (algebraMap (baseRing p) (AlgebraicClosure ℚ)) := by
      rw [IsScalarTower.algebraMap_eq (baseRing p) ℚ (AlgebraicClosure ℚ), RingHom.coe_comp]
      exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp
        (FaithfulSMul.algebraMap_injective (baseRing p) ℚ)
    exact hinj (by rw [hr', map_zero])
  have hle : ((genPt p).base (closedPoint (AlgebraicClosure ℚ))).asIdeal ≤
      (show PrimeSpectrum (baseRing p) from x).asIdeal := by
    rw [h]; exact bot_le
  exact (PrimeSpectrum.le_iff_specializes _ _).mp ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hle)

end Card
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.PPprimeKernelScheme"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.ModularCurve ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

p2m_open "ModularCurve.XHDRLevel~ΓN"
open _root_.ModularCurve.JHNeronObjectAtP (ΓN Fbar)
open scoped MatrixGroups

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y)))) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ a b : JH (M / p) (infSubgroup p M H hpM),
      (∃ m : ℕ, 0 < m ∧ m • a = 0 ∧ m • b = 0) →
      (∀ j : Fin 2, O.degPts j (αpull 0 a + αpull 1 b) = 0) → N • a = 0 ∧ N • b = 0 := by
  haveI : IsProper Λ.f := hΛ.proper

  have hspfin := ModularCurve.JHNeronObjectAtP.PPprimeDict.finite_specialPoints_kernelScheme hA hpM2 O F Finv Fstar hF hFinv
    hFstar pb hpb δ hδ degPull hpullsp hΛptsSp_add

  have hgenfin := SpecGenFinite.finite_setOf_comp_eq_of_isProper_of_finite_of_specializes.{0}
    (PPprimeKernelScheme.toS Λ.L (ModularCurve.JHNeronObjectAtP.PPprimeDict.pushPullMatrix O degPull))
    (resPt A ≫ Λ.σA) hspfin (genPt p) (PPprimeCard.genPt_specializes p _)

  haveI hK := ModularCurve.JHNeronObjectAtP.PPprimeDict.finite_pushPullKer_of_finite O hΛpts_add αpull degPull hpull hgenfin
  refine ⟨Nat.card ↥(ModularCurve.JHNeronObjectAtP.PPprimeDict.pushPullKer O αpull),
    (Nat.card_pos (α := ↥(ModularCurve.JHNeronObjectAtP.PPprimeDict.pushPullKer O αpull))).ne', ?_⟩
  intro a b _ hab
  have hmem : (a, b) ∈ ModularCurve.JHNeronObjectAtP.PPprimeDict.pushPullKer O αpull :=
    (ModularCurve.JHNeronObjectAtP.PPprimeDict.mem_pushPullKer O αpull (a, b)).mpr hab
  have h : Nat.card ↥(ModularCurve.JHNeronObjectAtP.PPprimeDict.pushPullKer O αpull) •
      (⟨(a, b), hmem⟩ : ↥(ModularCurve.JHNeronObjectAtP.PPprimeDict.pushPullKer O αpull)) = 0 := card_nsmul_eq_zero'
  have h' : Nat.card ↥(ModularCurve.JHNeronObjectAtP.PPprimeDict.pushPullKer O αpull) •
      ((a, b) : JH (M / p) (infSubgroup p M H hpM) × JH (M / p) (infSubgroup p M H hpM)) = 0 := by
    have h2 := congrArg Subtype.val h
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero] at h2
    exact h2
  have h1 := congrArg Prod.fst h'
  have h2 := congrArg Prod.snd h'
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero] at h1 h2
  exact ⟨h1, h2⟩

end S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero (solution)
