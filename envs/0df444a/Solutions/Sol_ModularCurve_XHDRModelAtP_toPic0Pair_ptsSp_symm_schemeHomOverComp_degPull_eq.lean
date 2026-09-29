-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5f530bde-ec1a-5f58-a8cd-ea69762423ca

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
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
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
import Theorems.Thm_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single_of_notMem
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_CurveModel_infinite_place
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_XHDRModelAtP_degPull_mul_and_zeroSection_comp_of_classifies_pullback
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_ModularCurve_qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_w_inv_placeOfPoint_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun"
p2m_attr_erase "simp" "KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

namespace HPRead

universe u

abbrev cls {X : Scheme.{u}} (M : X.Modules) : Skeleton X.Modules := toSkeleton M

theorem cls_eq_iff {X : Scheme.{u}} (A B : X.Modules) : cls A = cls B ↔ Nonempty (A ≅ B) :=
  ⟨fun h => Quotient.exact h, fun ⟨e⟩ => Quotient.sound ⟨e⟩⟩

theorem cls_congr {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) : cls A = cls B :=
  (cls_eq_iff A B).2 ⟨e⟩

noncomputable def isoOfClsEq {X : Scheme.{u}} {A B : X.Modules} (h : cls A = cls B) : A ≅ B :=
  ((cls_eq_iff A B).1 h).some

theorem cls_tensor {X : Scheme.{u}} (A B : X.Modules) : cls (A ⊗ B) = cls A * cls B :=
  Skeleton.toSkeleton_tensorObj A B

theorem cls_unit (X : Scheme.{u}) : cls (𝟙_ X.Modules) = 1 := Skeleton.one_eq.symm

theorem isUnit_cls {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    IsUnit (cls L) := by
  obtain ⟨N, -, ⟨e⟩⟩ := hL.exists_tensor_inverse
  have h : cls L * cls N = 1 := ((cls_tensor L N).symm.trans (cls_congr e)).trans (cls_unit X)
  exact ⟨⟨cls L, cls N, h, (mul_comm _ _).trans h⟩, rfl⟩

theorem isInvertible_of_iso {X : Scheme.{u}} {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (e : L ≅ L') : Scheme.Modules.IsInvertible L' := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨t⟩⟩ := hL.1 x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ t⟩⟩

theorem cls_mul_cls_dual {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    cls L * cls (Scheme.Modules.dual L) = 1 :=
  ((cls_tensor _ _).symm.trans (cls_congr hL.dual.2.some)).trans (cls_unit X)

theorem cls_pullback_congr {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules} (h : cls A = cls B) :
    cls ((Scheme.Modules.pullback f).obj A) = cls ((Scheme.Modules.pullback f).obj B) :=
  cls_congr ((Scheme.Modules.pullback f).mapIso (isoOfClsEq h))

theorem cls_pullback_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj (A ⊗ B)) =
      cls ((Scheme.Modules.pullback f).obj A) * cls ((Scheme.Modules.pullback f).obj B) :=
  (cls_congr (Scheme.Modules.pullbackTensorObjIso f A B)).trans (cls_tensor _ _)

theorem cls_pullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cls ((Scheme.Modules.pullback f).obj (𝟙_ Y.Modules)) = 1 :=
  (cls_congr (Scheme.Modules.pullbackTensorUnitObjIso f)).trans (cls_unit X)

theorem cls_pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    cls ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) =
      cls ((Scheme.Modules.pullback (f ≫ g)).obj M) :=
  cls_congr ((Scheme.Modules.pullbackComp f g).app M)

theorem cls_pullback_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj M) = cls ((Scheme.Modules.pullback g).obj M) := by
  subst h; rfl

theorem cls_pullback_mul_cls_pullback_dual {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    cls ((Scheme.Modules.pullback f).obj L) * cls ((Scheme.Modules.pullback f).obj (Scheme.Modules.dual L)) = 1 := by
  rw [← cls_pullback_tensor, cls_pullback_congr f ((cls_tensor _ _).trans (cls_mul_cls_dual hL)), cls_pullback_unit]

theorem cls_module_mul_cls_invModule {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) :
    cls I.module * cls I.invModule = 1 :=
  ((cls_tensor _ _).symm.trans (cls_congr hI.nonempty_module_tensor_invModule_iso.1.some)).trans (cls_unit X)

theorem cls_invModule_mul {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    cls (I * J).invModule = cls I.invModule * cls J.invModule :=
  (cls_congr (hI.nonempty_mul_invModule_iso_tensor hJ).some).trans (cls_tensor _ _)

theorem isInvertible_prod_pow {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (n : ι → ℕ) (h : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i ^ n i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Scheme.IdealSheafData.isInvertible_top
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact ((h a (Finset.mem_insert_self a s)).pow _).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isInvertible_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (h : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i).IsInvertible := by
  simpa using isInvertible_prod_pow s I (fun _ => 1) h

theorem cls_invModule_pow_mul {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (n : ℕ) :
    cls (I ^ n * J).invModule = cls I.invModule ^ n * cls J.invModule := by
  induction n generalizing J with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ n ih => rw [pow_succ, mul_assoc, ih (hI.mul hJ), cls_invModule_mul hI hJ, pow_succ, mul_assoc]

theorem cls_invModule_prod_pow_mul {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (n : ι → ℕ) (h : ∀ i ∈ s, (I i).IsInvertible) {J : X.IdealSheafData} (hJ : J.IsInvertible) :
    cls ((∏ i ∈ s, I i ^ n i) * J).invModule = (∏ i ∈ s, cls (I i).invModule ^ n i) * cls J.invModule := by
  classical
  induction s using Finset.induction_on generalizing J with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, one_mul, one_mul]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_assoc,
      cls_invModule_pow_mul (h a (Finset.mem_insert_self a s))
        ((isInvertible_prod_pow s I n fun i hi => h i (Finset.mem_insert_of_mem hi)).mul hJ),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hJ, mul_assoc]

theorem cls_invModule_mul_prod_pow {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (n : ι → ℕ) (h : ∀ i ∈ s, (I i).IsInvertible) {J : X.IdealSheafData} (hJ : J.IsInvertible) :
    cls (J * ∏ i ∈ s, I i ^ n i).invModule = cls J.invModule * ∏ i ∈ s, cls (I i).invModule ^ n i := by
  rw [mul_comm J, cls_invModule_prod_pow_mul s I n h hJ, mul_comm]

theorem cls_invModule_mul_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (h : ∀ i ∈ s, (I i).IsInvertible) {J : X.IdealSheafData} (hJ : J.IsInvertible) :
    cls (J * ∏ i ∈ s, I i).invModule = cls J.invModule * ∏ i ∈ s, cls (I i).invModule := by
  have h1 := cls_invModule_mul_prod_pow s I (fun _ => 1) h hJ
  simpa only [pow_one] using h1

end HPRead

namespace HPRead

universe u

theorem poincare_mul_iso {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D from h)
    |>.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk s) (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

theorem cls_poincare_mul {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    cls (h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y)).L =
      cls (h.poincare.pullbackAlong x).L * cls (h.poincare.pullbackAlong y).L :=
  (cls_congr (poincare_mul_iso h s x y).some).trans (cls_tensor _ _)

theorem cls_poincare_list_prod {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (l : List (SchemeHomOver s D.toBase)) :
    letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).pointGroup s
    cls (h.poincare.pullbackAlong l.prod).L = (l.map fun x => cls (h.poincare.pullbackAlong x).L).prod := by
  letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).pointGroup s
  induction l with
  | nil =>
    rw [List.prod_nil, List.map_nil, List.prod_nil]

    have h1 := cls_poincare_mul h s 1 1
    rw [show (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s 1 1 = (1 : SchemeHomOver s D.toBase)
      from mul_one (1 : SchemeHomOver s D.toBase)] at h1
    exact (isUnit_cls (h.poincare.pullbackAlong 1).isInvertible).mul_right_injective (h1.symm.trans (mul_one _).symm)
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    exact cls_poincare_mul h s a l.prod

theorem cls_rigidify_of_isLocalRing {A : Type u} [CommRing A] [IsLocalRing A] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of A) ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)) {L : P.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    cls (Scheme.Modules.rigidify σ q L) = cls L := by
  rw [Scheme.Modules.rigidify_def, cls_tensor]
  have h1 := (hL.pullback σ).dual.1
  obtain ⟨e⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing h1
  rw [cls_pullback_congr q (cls_congr e), cls_pullback_unit, mul_one]

end HPRead

namespace HPRead

universe u

noncomputable def pbc {X Y : Scheme.{u}} (f : X ⟶ Y) : Skeleton Y.Modules →* Skeleton X.Modules where
  toFun := Quotient.lift (fun M : Y.Modules => cls ((Scheme.Modules.pullback f).obj M))
    (fun A B h => cls_congr ((Scheme.Modules.pullback f).mapIso (Classical.choice h)))
  map_one' := by
    change Quotient.lift _ _ (cls (𝟙_ Y.Modules)) = 1
    exact cls_pullback_unit f
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h A =>
    induction b using Quotient.inductionOn with | h B =>
    change Quotient.lift _ _ (cls A * cls B) = cls ((Scheme.Modules.pullback f).obj A) * cls ((Scheme.Modules.pullback f).obj B)
    rw [← cls_tensor]
    exact cls_pullback_tensor f A B

theorem pbc_cls {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    pbc f (cls M) = cls ((Scheme.Modules.pullback f).obj M) := rfl

theorem curveChange_comp {R : Type u} [CommRing R] {C C' C'' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} {c'' : C'' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (g : C'' ⟶ C') (hg : g ≫ c' = c'') (hgf : (g ≫ f) ≫ c = c'')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange (g ≫ f) hgf t = curveChange g hg t ≫ curveChange f hf t := by
  apply pullback.hom_ext <;> simp [curveChange, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem graphOver_translate_comp_curveChange {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} (w : C ≅ C) (hw : w.hom ≫ c = c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a b : SchemeHomOver t c) (hb : b.1 = a.1 ≫ w.inv) :
    graphOver c b.1 b.2 ≫ curveChange w.hom hw t = graphOver c a.1 a.2 := by
  apply pullback.hom_ext
  · simp [curveChange, pullback.lift_fst, graphOver_fst, hb]
  · simp [curveChange, pullback.lift_snd, graphOver_snd]

theorem cls_pullback_curveChange_ofPoint {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} [IsSeparated c] (w : C ≅ C) (hw : w.hom ≫ c = c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a b : SchemeHomOver t c) (hb : b.1 = a.1 ≫ w.inv)
    (ha' : (RelEffCartierDiv.ofPoint c a.1 a.2).I.IsInvertible) (hb' : (RelEffCartierDiv.ofPoint c b.1 b.2).I.IsInvertible) :
    cls ((Scheme.Modules.pullback (curveChange w.hom hw t)).obj (RelEffCartierDiv.ofPoint c a.1 a.2).lineBundle) =
        cls (RelEffCartierDiv.ofPoint c b.1 b.2).lineBundle ∧
      cls ((Scheme.Modules.pullback (curveChange w.hom hw t)).obj (RelEffCartierDiv.ofPoint c a.1 a.2).idealModule) =
        cls (RelEffCartierDiv.ofPoint c b.1 b.2).idealModule := by
  rw [RelEffCartierDiv.ofPoint_I] at ha' hb'
  haveI : IsIso (curveChange w.hom hw t) := by unfold curveChange; infer_instance
  have h := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso (curveChange w.hom hw t)
    (graphOver c a.1 a.2) (graphOver c b.1 b.2) (graphOver_translate_comp_curveChange w hw a b hb) ha' hb' 1
  simp only [pow_one] at h
  exact ⟨cls_congr h.1.some, cls_congr h.2.some⟩

end HPRead

namespace HPRead

open GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem ofFibrePt_baseChange_mul {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (a b : SchemeHomOver ι f) :
    ofFibrePt ((G.baseChange ι).mul (𝟙 _) (toFibrePt a) (toFibrePt b)) = G.mul ι a b := by
  apply Subtype.ext
  change (RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).mul (𝟙 _) (toFibrePt a) (toFibrePt b))).1 = _
  rw [RelativeGroupLaw.baseChangePointToBase_mul]
  simp only [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]
  have ha : overId a = GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl a :=
    Subtype.ext (Category.id_comp _).symm
  have hb : overId b = GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl b :=
    Subtype.ext (Category.id_comp _).symm
  rw [ha, hb, ← G.mul_natural ι (𝟙 _ ≫ ι) (𝟙 _) rfl a b, GoodReductionJacobian.schemeHomOverComp_coe,
    Category.id_comp]

end HPRead

set_option maxHeartbeats 3200000 in

theorem HPRead.exists_configuredPoint_zero
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ 𝔛.placeOn0 A hA ρ hρ n) :
    ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      ∃ uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 ∧
        uκ ≫ pullback.snd _ _ = 𝟙 _ ∧
        (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by

  have hsm : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
    have h := (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 A hA ρ hρ
      ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1)).mpr
    refine h ?_
    rintro ⟨-, ⟨z, hz⟩⟩

    have hxy : (𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base P.1) = (𝔛.comp A hA ρ hρ 1).base z := by
      rw [hz, Scheme.Hom.comp_apply]
    obtain ⟨n, hn₁, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hxy
    obtain ⟨-, ⟨hcl, hpl⟩⟩ := 𝔛.node_pin A hA ρ hρ n
    apply hP n

    have hpt : (inv (𝔛.efib A hA ρ hρ)).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) = P.1 := by
      rw [hn₁, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl
    have hsub : (⟨_, hcl⟩ : closedPoints (𝔛.Mfib A hA ρ hρ).C) = P := Subtype.ext hpt
    rw [← hsub]
    exact hpl
  exact ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
    p M H hpM hj 𝔛 A hA ρ hρ 0 P hsm

set_option maxHeartbeats 6400000 in
theorem HPRead.gen0
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (ptsSp₀ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase)

    (hptsSp₀_add : ∀ a b, ptsSp₀ (a + b) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange
        (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _ (toFibrePt (ptsSp₀ a)) (toFibrePt (ptsSp₀ b))))

    (hptsSp₀ : ∀ (v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1)
      (_ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 = vκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1)
      (_ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 = vκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        Nonempty ((hD₀.poincare.pullbackAlong s₀).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (hptsSp_add : ∀ x y, ptsSp (x + y) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _
        (toFibrePt (ptsSp x)) (toFibrePt (ptsSp y))))
    (hptsSp : ∀ (i : Fin 2)
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (x : ↥(GluingData.admissible SS))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.2 = 0),
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hD.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule) ∧
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x)

    (degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase)
    (hdegPull : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L)))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)
    (Q₁ Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hQ₁ : ∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁ ≠ s.1)
    (hQ₂ : ∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂ ≠ s.1)
    (hDw : Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) (1 : ℤ) - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1 ∈
          Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))) :
    GluedPic0.toPic0Pair SS (ptsSp.symm (schemeHomOverComp
        (ptsSp₀ (Pic0.mk ⟨_, hDw⟩)) (degPull 0))) = (Pic0.mk ⟨_, hDw⟩, Fstar (Pic0.mk ⟨_, hDw⟩)) := by
  classical
  haveI := 𝔛.smooth0

  have hoff : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C), (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
      ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ 𝔛.placeOn0 A hA ρ hρ n := by
    intro Q hQ n
    refine hQ (𝔛.placeOn0 A hA ρ hρ n, 𝔛.placeOn1 A hA ρ hρ n) ?_
    rw [hSS, ModularCurve.mem_ssNodePairsQExp_iff]
    exact ⟨(𝔛.nodeEquiv A hA ρ hρ n).2, rfl⟩
  obtain ⟨y₁, u₁, hu₁, husm₁, uκ₁, huκ₁₁, huκ₁₂, hP₁⟩ :=
    HPRead.exists_configuredPoint_zero p M H hpM hpM2 hj 𝔛 A hA ρ hρ Q₁ (hoff Q₁ hQ₁)
  obtain ⟨y₂, u₂, hu₂, husm₂, uκ₂, huκ₂₁, huκ₂₂, hP₂⟩ :=
    HPRead.exists_configuredPoint_zero p M H hpM hpM2 hj 𝔛 A hA ρ hρ Q₂ (hoff Q₂ hQ₂)

  obtain ⟨k₁, u'₁, e₁, hepos₁, hesum₁, hy'₁, hπ'₁, husm'₁, hsp'₁, hI₁⟩ :=
    ModularCurve.XHDRModelAtP.exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le p M H hpM hpM2 hHp hj 𝔛 A hA
      ρ hρ y₁ u₁ hu₁ husm₁ uκ₁ huκ₁₁ huκ₁₂ Q₁ hP₁ (hoff Q₁ hQ₁)
  obtain ⟨k₂, u'₂, e₂, hepos₂, hesum₂, hy'₂, hπ'₂, husm'₂, hsp'₂, hI₂⟩ :=
    ModularCurve.XHDRModelAtP.exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le p M H hpM hpM2 hHp hj 𝔛 A hA
      ρ hρ y₂ u₂ hu₂ husm₂ uκ₂ huκ₂₁ huκ₂₂ Q₂ hP₂ (hoff Q₂ hQ₂)

  have hvT : ∀ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      (u.1 ≫ 𝔛.π.1) ≫ toBase p (ΓN p M H hpM) hj = Spec.map (CommRingCat.ofHom ρ) := fun u =>
    (Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) 𝔛.π.2).trans u.2)
  let v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj) := ⟨u₁.1 ≫ 𝔛.π.1, hvT u₁⟩
  let v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj) := ⟨u₂.1 ≫ 𝔛.π.1, hvT u₂⟩
  let vκ₁ := uκ₁ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)
  let vκ₂ := uκ₂ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)
  have hfm_fst : XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ 𝔛.π.1 := pullback.lift_fst _ _ _
  have hfm_snd : XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.snd _ _ =
      pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hvκ₁₁ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1 := by
    simp only [vκ₁, v₁, Category.assoc, hfm_fst]; rw [← Category.assoc, huκ₁₁, Category.assoc]
  have hvκ₂₁ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1 := by
    simp only [vκ₂, v₂, Category.assoc, hfm_fst]; rw [← Category.assoc, huκ₂₁, Category.assoc]
  have hvκ₁₂ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _ := by simp only [vκ₁, Category.assoc, hfm_snd]; exact huκ₁₂
  have hvκ₂₂ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _ := by simp only [vκ₂, Category.assoc, hfm_snd]; exact huκ₂₂
  have hQv : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) →
      (𝔛.efib A hA ρ hρ).base Q.1 = (uκ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base
        (IsLocalRing.closedPoint (ResidueField ↥A)) := by
    intro Q uκ h
    rw [Scheme.Hom.comp_apply, ← h, ← Scheme.Hom.comp_apply, Category.assoc, 𝔛.comp_pi A hA ρ hρ, Category.comp_id]

  obtain ⟨s₀, ⟨iso₀⟩, hs₀⟩ := hptsSp₀ v₁ vκ₁ hvκ₁₁ hvκ₁₂ Q₁ (hQv Q₁ uκ₁ hP₁) v₂ vκ₂ hvκ₂₁ hvκ₂₂ Q₂ (hQv Q₂ uκ₂ hP₂) ⟨_, hDw⟩ rfl
  have hx : ptsSp₀ (Pic0.mk ⟨_, hDw⟩) = schemeHomOverComp ⟨resPt A, rfl⟩ s₀ := by
    rw [← hs₀, Equiv.apply_symm_apply]
  rw [hx]

  have hcard : ∀ {k : ℕ} (e : Fin k → ℕ), ∑ j, e j = p → Fintype.card (Σ j : Fin k, Fin (e j)) = p := by
    intro k e he; rw [Fintype.card_sigma]; simpa using he
  let τ₁ : Fin p ≃ (Σ j : Fin k₁, Fin (e₁ j)) := (Fintype.equivFinOfCardEq (hcard e₁ hesum₁)).symm
  let τ₂ : Fin p ≃ (Σ j : Fin k₂, Fin (e₂ j)) := (Fintype.equivFinOfCardEq (hcard e₂ hesum₂)).symm
  let a₁ : Fin p → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj) := fun r => u'₁ (τ₁ r).1
  let a₂ : Fin p → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj) := fun r => u'₂ (τ₂ r).1

  have hprod : ∀ {k : ℕ} (e : Fin k → ℕ) (he : ∑ j, e j = p)
      (I : Fin k → (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).IdealSheafData),
      ∏ j, I j ^ e j = ∏ r : Fin p, I ((Fintype.equivFinOfCardEq (hcard e he)).symm r).1 := by
    intro k e he I
    calc ∏ j, I j ^ e j = ∏ j, ∏ _r : Fin (e j), I j := Finset.prod_congr rfl fun j _ => by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ x : (Σ j : Fin k, Fin (e j)), I x.1 := (Fintype.prod_sigma (fun x : (Σ j : Fin k, Fin (e j)) => I x.1)).symm
      _ = ∏ r : Fin p, I ((Fintype.equivFinOfCardEq (hcard e he)).symm r).1 :=
          (Fintype.prod_equiv (Fintype.equivFinOfCardEq (hcard e he)).symm _ _ (fun _ => rfl)).symm
  have hI₁' : (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).I.comap
        (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ))) =
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).I *
        ∏ r : Fin p, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₁ r).1 (a₁ r).2).I := by
    rw [← hprod e₁ hesum₁ fun j => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u'₁ j).1 (u'₁ j).2).I]
    exact hI₁
  have hI₂' : (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).I.comap
        (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ))) =
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).I *
        ∏ r : Fin p, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₂ r).1 (a₂ r).2).I := by
    rw [← hprod e₂ hesum₂ fun j => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u'₂ j).1 (u'₂ j).2).I]
    exact hI₂

  choose uκ'₁ huκ'₁₁ huκ'₁₂ P'₁ hP'₁ hfrob₁ using hsp'₁
  choose uκ'₂ huκ'₂₁ huκ'₂₂ P'₂ hP'₂ hfrob₂ using hsp'₂

  have hcurve : IsCurveOver (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ∧
      Algebra.EssFiniteType (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := by
    obtain ⟨xj, -, hxj, hfdj⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      (ResidueField ↥A) (ΓN p M H hpM) (ModularCurve.translation_mem_GammaH _ _)
    exact ⟨AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxj hfdj,
      AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxj hfdj⟩
  haveI := hcurve.1
  haveI := hcurve.2
  have hdeg : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), v.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have hdz : ∀ (P P' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
      Finsupp.single P (1 : ℤ) - Finsupp.single P' 1 ∈ Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)) := by
    intro P P'
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg, sub_self]

  have hP'off : ∀ (P' Q : closedPoints (𝔛.Mfib A hA ρ hρ).C), (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
      qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P') =
        (𝔛.Mfib A hA ρ hρ).placeOfPoint Q →
      ∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint P' ≠ s.2 := by
    intro P' Q hQ hfr s hs heq
    apply hQ s hs
    rw [← hfr, heq]
    exact ((hSS s).1 hs).2.symm
  let xinf : ↥(GluingData.admissible SS) :=
    ⟨(Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1, 0, 0),
      hDw, zero_mem _, fun s hs => ⟨by simp [Finsupp.single_apply, hQ₁ s hs, hQ₂ s hs], rfl⟩⟩
  let xr : Fin p → ↥(GluingData.admissible SS) := fun r =>
    ⟨(0, Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P'₁ (τ₁ r).1)) 1 -
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P'₂ (τ₂ r).1)) 1, 0),
      zero_mem _, hdz _ _, fun s hs => ⟨rfl, by
        simp [Finsupp.single_apply, hP'off _ _ hQ₁ (hfrob₁ _) s hs, hP'off _ _ hQ₂ (hfrob₂ _) s hs]⟩⟩

  obtain ⟨sinf, ⟨isoinf⟩, hsinf⟩ := hptsSp 0 u₁ husm₁ uκ₁ huκ₁₁ huκ₁₂ Q₁ hP₁ u₂ husm₂ uκ₂ huκ₂₁ huκ₂₂ Q₂ hP₂ xinf
    (by simp [xinf]) (by simp [xinf]) rfl

  have hslot : ∀ r : Fin p, ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong s).L ≅
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₁ r).1 (a₁ r).2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₂ r).1 (a₂ r).2).idealModule) ∧
      ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS (xr r) := fun r =>
    hptsSp 1 (a₁ r) (husm'₁ _) (uκ'₁ _) (huκ'₁₁ _) (huκ'₁₂ _) (P'₁ _) (hP'₁ _) (a₂ r) (husm'₂ _) (uκ'₂ _) (huκ'₂₁ _)
      (huκ'₂₂ _) (P'₂ _) (hP'₂ _) (xr r) (by simp [xr]) (by simp [xr]) rfl
  choose sr hsr_iso hsr_read using hslot

  letI grp := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).pointGroup (Spec.map (CommRingCat.ofHom ρ))
  have hkey : schemeHomOverComp s₀ (degPull 0) = sinf * (List.ofFn sr).prod := by

    have hsuppU : ∀ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
        Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) →
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).SupportedIn 𝔛.smoothLocus := by
      intro u husm x hx
      rw [RelEffCartierDiv.ofPoint_I, Scheme.Hom.support_ker,
        (graphOver (toBase p (ΓM M H) hj) u.1 u.2).isClosedEmbedding.isClosed_range.closure_eq] at hx
      obtain ⟨t, rfl⟩ := hx
      show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((graphOver (toBase p (ΓM M H) hj) u.1 u.2).base t) ∈
        (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
      rw [← Scheme.Hom.comp_apply, graphOver_fst]
      exact husm ⟨t, rfl⟩
    have hinvU : ∀ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
        Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) →
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).I.IsInvertible := fun u husm =>
      RelEffCartierDiv.isInvertible_I_of_supportedIn 𝔛.smoothLocus _ (hsuppU u husm)
    have hinvV : ∀ (v : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj)),
        (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v.1 v.2).I.IsInvertible := fun v =>
      RelEffCartierDiv.isInvertible_I _

    let Iu₁ := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).I
    let Iu₂ := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).I
    let Ia₁ := fun r : Fin p => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₁ r).1 (a₁ r).2).I
    let Ia₂ := fun r : Fin p => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₂ r).1 (a₂ r).2).I
    have hIu₁ : Iu₁.IsInvertible := hinvU u₁ husm₁
    have hIu₂ : Iu₂.IsInvertible := hinvU u₂ husm₂
    have hIa₁ : ∀ r, (Ia₁ r).IsInvertible := fun r => hinvU (a₁ r) (husm'₁ _)
    have hIa₂ : ∀ r, (Ia₂ r).IsInvertible := fun r => hinvU (a₂ r) (husm'₂ _)
    let U₁ := HPRead.cls Iu₁.invModule * ∏ r, HPRead.cls (Ia₁ r).invModule
    let U₂ := HPRead.cls Iu₂.invModule * ∏ r, HPRead.cls (Ia₂ r).invModule
    let M₂ := HPRead.cls Iu₂.module * ∏ r, HPRead.cls (Ia₂ r).module
    have hU₂unit : IsUnit U₂ :=
      (HPRead.isUnit_cls hIu₂.isInvertible_invModule).mul (IsUnit.prod_univ_iff.mpr fun r => HPRead.isUnit_cls (hIa₂ r).isInvertible_invModule)
    have hMU : M₂ * U₂ = 1 := by
      simp only [M₂, U₂]
      rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, HPRead.cls_module_mul_cls_invModule hIu₂,
        Finset.prod_eq_one (fun r _ => HPRead.cls_module_mul_cls_invModule (hIa₂ r)), one_mul]

    let πA := curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ))
    have hc₁ : ((RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).I.comap πA).IsInvertible := by
      rw [hI₁']; exact hIu₁.mul (HPRead.isInvertible_prod _ _ fun r _ => hIa₁ r)
    have hc₂ : ((RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).I.comap πA).IsInvertible := by
      rw [hI₂']; exact hIu₂.mul (HPRead.isInvertible_prod _ _ fun r _ => hIa₂ r)
    have hpull₁ : HPRead.cls ((Scheme.Modules.pullback πA).obj
        (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle) = U₁ := by
      rw [HPRead.cls_congr (Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso πA (hinvV v₁) hc₁).some, hI₁',
        HPRead.cls_invModule_mul_prod _ _ (fun r _ => hIa₁ r) hIu₁]
    have hpull₂ : HPRead.cls ((Scheme.Modules.pullback πA).obj
        (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).lineBundle) = U₂ := by
      rw [HPRead.cls_congr (Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso πA (hinvV v₂) hc₂).some, hI₂',
        HPRead.cls_invModule_mul_prod _ _ (fun r _ => hIa₂ r) hIu₂]
    have hpull₂' : HPRead.cls ((Scheme.Modules.pullback πA).obj
        (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) * U₂ = 1 := by
      rw [← hpull₂, ← HPRead.cls_pullback_tensor,
        HPRead.cls_pullback_congr πA ((HPRead.cls_tensor _ _).trans (HPRead.cls_module_mul_cls_invModule (hinvV v₂))),
        HPRead.cls_pullback_unit]

    obtain ⟨edeg⟩ := hdegPull 0 (Spec.map (CommRingCat.ofHom ρ)) s₀
    have hite : (if (0 : Fin 2) = 0 then 𝔛.π else 𝔛.πw) = 𝔛.π := if_pos rfl
    rw [hite] at edeg
    have hLHS : HPRead.cls (hD.poincare.pullbackAlong (schemeHomOverComp s₀ (degPull 0))).L =
        U₁ * HPRead.cls ((Scheme.Modules.pullback πA).obj (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) := by
      rw [HPRead.cls_congr edeg, HPRead.cls_rigidify_of_isLocalRing _ _ ((hD₀.poincare.pullbackAlong s₀).isInvertible.pullback _),
        HPRead.cls_pullback_congr πA (HPRead.cls_congr iso₀), HPRead.cls_pullback_tensor, hpull₁]

    have hRHS : HPRead.cls (hD.poincare.pullbackAlong (sinf * (List.ofFn sr).prod)).L = U₁ * M₂ := by
      rw [show sinf * (List.ofFn sr).prod = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ sinf
          (List.ofFn sr).prod from rfl,
        HPRead.cls_poincare_mul, HPRead.cls_poincare_list_prod, List.map_ofFn, List.prod_ofFn, HPRead.cls_congr isoinf, HPRead.cls_tensor]
      have hr : ∀ r, HPRead.cls (hD.poincare.pullbackAlong (sr r)).L = HPRead.cls (Ia₁ r).invModule * HPRead.cls (Ia₂ r).module := fun r =>
        (HPRead.cls_congr (hsr_iso r).some).trans (HPRead.cls_tensor _ _)
      simp only [Function.comp_def, hr, Finset.prod_mul_distrib, U₁, M₂]
      rw [mul_mul_mul_comm]

    apply hD.ext_of_iso (Spec.map (CommRingCat.ofHom ρ))
    refine ⟨HPRead.isoOfClsEq ?_⟩
    rw [hLHS, hRHS]
    congr 1
    exact hU₂unit.mul_left_injective (hpull₂'.trans hMU.symm)

  let φ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase → GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS :=
    fun a => ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ a)
  let ψ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase →
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
    fun a => GluedPic0.toPic0Pair SS (φ a)
  have hcv : ∀ a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom ρ))) a =
        GoodReductionJacobian.schemeHomOverComp (resPt A) rfl a := fun a => Subtype.ext rfl
  have hφmul : ∀ a b : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, φ (a * b) = φ a + φ b := by
    intro a b
    apply ptsSp.injective
    have e2 := HPRead.ofFibrePt_baseChange_mul
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD)
      (schemeHomOverComp ⟨resPt A, rfl⟩ a) (schemeHomOverComp ⟨resPt A, rfl⟩ b)
    simp only [φ]
    rw [Equiv.apply_symm_apply, hptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, e2, hcv, hcv, hcv]
    exact (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul_natural
      (Spec.map (CommRingCat.ofHom ρ)) (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) (resPt A) rfl a b
  have hψmul : ∀ a b : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, ψ (a * b) = ψ a + ψ b := fun a b =>
    congrArg (GluedPic0.toPic0Pair SS) (hφmul a b) |>.trans ((GluedPic0.toPic0Pair SS).map_add _ _)
  have hψone : ψ 1 = 0 := by
    have h := hψmul 1 1
    rw [mul_one] at h
    have h' : ψ 1 + ψ 1 = ψ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hψlist : ∀ l : List (SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase), ψ l.prod = (l.map ψ).sum := by
    intro l
    induction l with
    | nil => rw [List.prod_nil, List.map_nil, List.sum_nil]; exact hψone
    | cons a l ih => rw [List.prod_cons, List.map_cons, List.sum_cons, hψmul, ih]

  have hassoc : schemeHomOverComp (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) (degPull 0) =
      schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom ρ)))
        (schemeHomOverComp s₀ (degPull 0)) :=
    Subtype.ext (Category.assoc _ _ _)
  rw [hassoc, hkey]
  change ψ (sinf * (List.ofFn sr).prod) = _
  rw [hψmul, hψlist, List.map_ofFn]
  have hψinf : ψ sinf = (Pic0.mk ⟨_, hDw⟩, 0) := by
    show GluedPic0.toPic0Pair SS (φ sinf) = _
    have : φ sinf = GluedPic0.mk SS xinf := hsinf
    rw [this, GluedPic0.toPic0Pair_mk]
    refine Prod.ext rfl ?_
    show Pic0.mk _ = 0
    exact (congrArg Pic0.mk (Subtype.ext rfl : (⟨((xinf : GluingData _ _ SS)).2.1, (xinf).2.2.1⟩ : Divisor.degZero) = 0)).trans
      (QuotientAddGroup.mk_zero _)

  let Φ := Equiv.ofBijective _ (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM))
  have hxj : ∃ x : ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM), Transcendental (ResidueField ↥A) x ∧
      FiniteDimensional (IntermediateField.adjoin (ResidueField ↥A) ({x} : Set (ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))))
        (ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) := by
    obtain ⟨xj, -, hxj, hfdj⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      (ResidueField ↥A) (ΓN p M H hpM) (ModularCurve.translation_mem_GammaH _ _)
    exact ⟨xj, hxj, hfdj⟩
  have hFdiv := ModularCurve.qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain (ResidueField ↥A) p (ΓN p M H hpM) hxj F hF Φ
    (fun _ => rfl)
  have hψr : ∀ r, ψ (sr r) = (0, Finv (Pic0.mk ⟨_, hDw⟩)) := by
    intro r
    show GluedPic0.toPic0Pair SS (φ (sr r)) = _
    have : φ (sr r) = GluedPic0.mk SS (xr r) := hsr_read r
    rw [this, GluedPic0.toPic0Pair_mk]
    refine Prod.ext ?_ ?_
    · show Pic0.mk _ = 0
      exact (congrArg Pic0.mk (Subtype.ext rfl : (⟨((xr r : GluingData _ _ SS)).1, (xr r).2.1⟩ : Divisor.degZero) = 0)).trans
        (QuotientAddGroup.mk_zero _)
    ·
      show Pic0.mk _ = Finv (Pic0.mk ⟨_, hDw⟩)
      have hF1 : F (Pic0.mk ⟨((xr r : GluingData _ _ SS)).2.1, (xr r).2.2.1⟩) = Pic0.mk ⟨_, hDw⟩ := by
        apply hFdiv
        show Finsupp.single _ 1 - Finsupp.single _ 1 = Finsupp.mapDomain Φ (Finsupp.single _ 1 - Finsupp.single _ 1)
        rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
        show _ = Finsupp.single (qExpFrobeniusPlaceModL _ _ _ _) 1 - Finsupp.single (qExpFrobeniusPlaceModL _ _ _ _) 1
        rw [hfrob₁, hfrob₂]
      rw [← hF1]
      exact (DFunLike.congr_fun hFinv.2 _).symm
  have hcompψ : ψ ∘ sr = fun _ => ((0 : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), Finv (Pic0.mk ⟨_, hDw⟩)) :=
    funext hψr
  rw [hψinf, hcompψ, List.ofFn_const, List.sum_replicate, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add, hFstar,
    natCast_zsmul]

set_option maxHeartbeats 16000000 in
theorem HPRead.gen1
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (ptsSp₀ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase)

    (hptsSp₀_add : ∀ a b, ptsSp₀ (a + b) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange
        (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _ (toFibrePt (ptsSp₀ a)) (toFibrePt (ptsSp₀ b))))

    (hptsSp₀ : ∀ (v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1)
      (_ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 = vκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1)
      (_ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 = vκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        Nonempty ((hD₀.poincare.pullbackAlong s₀).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (hptsSp_add : ∀ x y, ptsSp (x + y) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _
        (toFibrePt (ptsSp x)) (toFibrePt (ptsSp y))))
    (hptsSp : ∀ (i : Fin 2)
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (x : ↥(GluingData.admissible SS))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.2 = 0),
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hD.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule) ∧
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x)

    (degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase)
    (hdegPull : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L)))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)
    (Q₁ Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hQ₁ : ∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁ ≠ s.1)
    (hQ₂ : ∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂ ≠ s.1)
    (hQF₁ : ∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁ ≠ qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p s.1)
    (hQF₂ : ∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂ ≠ qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p s.1)
    (hQσ₁ : ∀ s ∈ SS, SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁ ≠ s.2)
    (hQσ₂ : ∀ s ∈ SS, SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂ ≠ s.2)
    (hDw : Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) (1 : ℤ) - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1 ∈
          Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))) :
    GluedPic0.toPic0Pair SS (ptsSp.symm (schemeHomOverComp
        (ptsSp₀ (Pic0.mk ⟨_, hDw⟩)) (degPull 1))) = (Fstar (Pic0.mk ⟨_, hDw⟩), δ (Pic0.mk ⟨_, hDw⟩)) := by
  classical
  haveI := 𝔛.smooth0

  have hoff : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C), (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
      ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ 𝔛.placeOn0 A hA ρ hρ n := by
    intro Q hQ n
    refine hQ (𝔛.placeOn0 A hA ρ hρ n, 𝔛.placeOn1 A hA ρ hρ n) ?_
    rw [hSS, ModularCurve.mem_ssNodePairsQExp_iff]
    exact ⟨(𝔛.nodeEquiv A hA ρ hρ n).2, rfl⟩
  obtain ⟨y₁, u₁, hu₁, husm₁, uκ₁, huκ₁₁, huκ₁₂, hP₁⟩ :=
    HPRead.exists_configuredPoint_zero p M H hpM hpM2 hj 𝔛 A hA ρ hρ Q₁ (hoff Q₁ hQ₁)
  obtain ⟨y₂, u₂, hu₂, husm₂, uκ₂, huκ₂₁, huκ₂₂, hP₂⟩ :=
    HPRead.exists_configuredPoint_zero p M H hpM hpM2 hj 𝔛 A hA ρ hρ Q₂ (hoff Q₂ hQ₂)

  obtain ⟨k₁, u'₁, e₁, hepos₁, hesum₁, hy'₁, hπ'₁, husm'₁, hsp'₁, hI₁⟩ :=
    ModularCurve.XHDRModelAtP.exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le p M H hpM hpM2 hHp hj 𝔛 A hA
      ρ hρ y₁ u₁ hu₁ husm₁ uκ₁ huκ₁₁ huκ₁₂ Q₁ hP₁ (hoff Q₁ hQ₁)
  obtain ⟨k₂, u'₂, e₂, hepos₂, hesum₂, hy'₂, hπ'₂, husm'₂, hsp'₂, hI₂⟩ :=
    ModularCurve.XHDRModelAtP.exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le p M H hpM hpM2 hHp hj 𝔛 A hA
      ρ hρ y₂ u₂ hu₂ husm₂ uκ₂ huκ₂₁ huκ₂₂ Q₂ hP₂ (hoff Q₂ hQ₂)

  have hvT : ∀ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      (u.1 ≫ 𝔛.π.1) ≫ toBase p (ΓN p M H hpM) hj = Spec.map (CommRingCat.ofHom ρ) := fun u =>
    (Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) 𝔛.π.2).trans u.2)
  let v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj) := ⟨u₁.1 ≫ 𝔛.π.1, hvT u₁⟩
  let v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj) := ⟨u₂.1 ≫ 𝔛.π.1, hvT u₂⟩
  let vκ₁ := uκ₁ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)
  let vκ₂ := uκ₂ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)
  have hfm_fst : XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ 𝔛.π.1 := pullback.lift_fst _ _ _
  have hfm_snd : XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.snd _ _ =
      pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hvκ₁₁ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1 := by
    simp only [vκ₁, v₁, Category.assoc, hfm_fst]; rw [← Category.assoc, huκ₁₁, Category.assoc]
  have hvκ₂₁ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1 := by
    simp only [vκ₂, v₂, Category.assoc, hfm_fst]; rw [← Category.assoc, huκ₂₁, Category.assoc]
  have hvκ₁₂ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _ := by simp only [vκ₁, Category.assoc, hfm_snd]; exact huκ₁₂
  have hvκ₂₂ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _ := by simp only [vκ₂, Category.assoc, hfm_snd]; exact huκ₂₂
  have hQv : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) →
      (𝔛.efib A hA ρ hρ).base Q.1 = (uκ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base
        (IsLocalRing.closedPoint (ResidueField ↥A)) := by
    intro Q uκ h
    rw [Scheme.Hom.comp_apply, ← h, ← Scheme.Hom.comp_apply, Category.assoc, 𝔛.comp_pi A hA ρ hρ, Category.comp_id]

  obtain ⟨s₀, ⟨iso₀⟩, hs₀⟩ := hptsSp₀ v₁ vκ₁ hvκ₁₁ hvκ₁₂ Q₁ (hQv Q₁ uκ₁ hP₁) v₂ vκ₂ hvκ₂₁ hvκ₂₂ Q₂ (hQv Q₂ uκ₂ hP₂) ⟨_, hDw⟩ rfl
  have hx : ptsSp₀ (Pic0.mk ⟨_, hDw⟩) = schemeHomOverComp ⟨resPt A, rfl⟩ s₀ := by
    rw [← hs₀, Equiv.apply_symm_apply]
  rw [hx]

  have hcard : ∀ {k : ℕ} (e : Fin k → ℕ), ∑ j, e j = p → Fintype.card (Σ j : Fin k, Fin (e j)) = p := by
    intro k e he; rw [Fintype.card_sigma]; simpa using he
  let τ₁ : Fin p ≃ (Σ j : Fin k₁, Fin (e₁ j)) := (Fintype.equivFinOfCardEq (hcard e₁ hesum₁)).symm
  let τ₂ : Fin p ≃ (Σ j : Fin k₂, Fin (e₂ j)) := (Fintype.equivFinOfCardEq (hcard e₂ hesum₂)).symm
  let a₁ : Fin p → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj) := fun r => u'₁ (τ₁ r).1
  let a₂ : Fin p → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj) := fun r => u'₂ (τ₂ r).1

  have hprod : ∀ {k : ℕ} (e : Fin k → ℕ) (he : ∑ j, e j = p)
      (I : Fin k → (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).IdealSheafData),
      ∏ j, I j ^ e j = ∏ r : Fin p, I ((Fintype.equivFinOfCardEq (hcard e he)).symm r).1 := by
    intro k e he I
    calc ∏ j, I j ^ e j = ∏ j, ∏ _r : Fin (e j), I j := Finset.prod_congr rfl fun j _ => by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ x : (Σ j : Fin k, Fin (e j)), I x.1 := (Fintype.prod_sigma (fun x : (Σ j : Fin k, Fin (e j)) => I x.1)).symm
      _ = ∏ r : Fin p, I ((Fintype.equivFinOfCardEq (hcard e he)).symm r).1 :=
          (Fintype.prod_equiv (Fintype.equivFinOfCardEq (hcard e he)).symm _ _ (fun _ => rfl)).symm
  have hI₁' : (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).I.comap
        (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ))) =
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).I *
        ∏ r : Fin p, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₁ r).1 (a₁ r).2).I := by
    rw [← hprod e₁ hesum₁ fun j => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u'₁ j).1 (u'₁ j).2).I]
    exact hI₁
  have hI₂' : (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).I.comap
        (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ))) =
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).I *
        ∏ r : Fin p, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₂ r).1 (a₂ r).2).I := by
    rw [← hprod e₂ hesum₂ fun j => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u'₂ j).1 (u'₂ j).2).I]
    exact hI₂

  choose uκ'₁ huκ'₁₁ huκ'₁₂ P'₁ hP'₁ hfrob₁ using hsp'₁
  choose uκ'₂ huκ'₂₁ huκ'₂₂ P'₂ hP'₂ hfrob₂ using hsp'₂

  have hcurve : IsCurveOver (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ∧
      Algebra.EssFiniteType (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := by
    obtain ⟨xj, -, hxj, hfdj⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      (ResidueField ↥A) (ΓN p M H hpM) (ModularCurve.translation_mem_GammaH _ _)
    exact ⟨AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxj hfdj,
      AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxj hfdj⟩
  haveI := hcurve.1
  haveI := hcurve.2
  have hdeg : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), v.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have hdz : ∀ (P P' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
      Finsupp.single P (1 : ℤ) - Finsupp.single P' 1 ∈ Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)) := by
    intro P P'
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg, sub_self]

  have hP'off : ∀ (P' Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p s.1) →
      qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P') =
        (𝔛.Mfib A hA ρ hρ).placeOfPoint Q →
      ∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint P' ≠ s.1 := by
    intro P' Q hQ hfr s hs heq
    apply hQ s hs
    rw [← hfr, heq]

  have hdia0 := ModularCurve.XHDRModelAtP.exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ

  obtain ⟨w₁, hw₁, hwsm₁, wκ₁, hwκ₁₁, hwκ₁₂, -, R₁, hR₁, hplR₁⟩ :=
    ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_placeOfPoint_eq p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb 0
      u₁ husm₁ uκ₁ huκ₁₁ huκ₁₂ Q₁ hP₁
  obtain ⟨w₂, hw₂, hwsm₂, wκ₂, hwκ₂₁, hwκ₂₂, -, R₂, hR₂, hplR₂⟩ :=
    ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_placeOfPoint_eq p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb 0
      u₂ husm₂ uκ₂ huκ₂₁ huκ₂₂ Q₂ hP₂
  rw [if_pos rfl] at hR₁ hR₂ hplR₁ hplR₂

  have hslotw : ∀ (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (husm : Set.range a.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (h1 : uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ a.1)
      (h2 : uκ' ≫ pullback.snd _ _ = 𝟙 _)
      (P' : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (h3 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      ∃ (b : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
        b.1 = a.1 ≫ 𝔛.w.inv ∧ Set.range b.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
        ∃ bκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
          bκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ b.1 ∧
          bκ ≫ pullback.snd _ _ = 𝟙 _ ∧
          ∃ R : closedPoints (𝔛.Mfib A hA ρ hρ).C,
            (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base R.1 = bκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
            (𝔛.Mfib A hA ρ hρ).placeOfPoint R = (𝔛.Mfib A hA ρ hρ).placeOfPoint P' := by
    intro a husm uκ' h1 h2 P' h3
    obtain ⟨b, hb, hbsm, bκ, hbκ₁, hbκ₂, -, R, hR, hplR⟩ :=
      ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_placeOfPoint_eq p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb 1
        a husm uκ' h1 h2 P' h3
    rw [if_neg (by decide)] at hR hplR
    exact ⟨b, hb, hbsm, bκ, hbκ₁, hbκ₂, R, hR, hplR⟩
  have hslotw₁ := fun r : Fin p => hslotw (a₁ r) (husm'₁ _) (uκ'₁ _) (huκ'₁₁ _) (huκ'₁₂ _) (P'₁ _) (hP'₁ _)
  have hslotw₂ := fun r : Fin p => hslotw (a₂ r) (husm'₂ _) (uκ'₂ _) (huκ'₂₁ _) (huκ'₂₂ _) (P'₂ _) (hP'₂ _)
  choose b₁ hb₁ hbsm₁ bκ₁ hbκ₁₁ hbκ₁₂ R'₁ hR'₁ hplR'₁ using hslotw₁
  choose b₂ hb₂ hbsm₂ bκ₂ hbκ₂₁ hbκ₂₂ R'₂ hR'₂ hplR'₂ using hslotw₂

  let xinf : ↥(GluingData.admissible SS) :=
    ⟨(0, Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint R₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint R₂) 1, 0),
      zero_mem _, hdz _ _, fun s hs => ⟨rfl, by rw [hplR₁, hplR₂]; simp [hQσ₁ s hs, hQσ₂ s hs]⟩⟩
  let xr : Fin p → ↥(GluingData.admissible SS) := fun r =>
    ⟨(Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (R'₁ r)) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (R'₂ r)) 1, 0, 0),
      hdz _ _, zero_mem _, fun s hs => ⟨by
        rw [hplR'₁, hplR'₂]
        simp [hP'off _ _ hQF₁ (hfrob₁ _) s hs, hP'off _ _ hQF₂ (hfrob₂ _) s hs], rfl⟩⟩

  obtain ⟨sinf, ⟨isoinf⟩, hsinf⟩ := hptsSp 1 w₁ hwsm₁ wκ₁ hwκ₁₁ hwκ₁₂ R₁ hR₁ w₂ hwsm₂ wκ₂ hwκ₂₁ hwκ₂₂ R₂ hR₂ xinf
    (by simp [xinf]) (by simp [xinf]) rfl

  have hslot : ∀ r : Fin p, ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong s).L ≅
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (b₁ r).1 (b₁ r).2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (b₂ r).1 (b₂ r).2).idealModule) ∧
      ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS (xr r) := fun r =>
    hptsSp 0 (b₁ r) (hbsm₁ _) (bκ₁ _) (hbκ₁₁ _) (hbκ₁₂ _) (R'₁ _) (hR'₁ _) (b₂ r) (hbsm₂ _) (bκ₂ _) (hbκ₂₁ _)
      (hbκ₂₂ _) (R'₂ _) (hR'₂ _) (xr r) (by simp [xr]) (by simp [xr]) rfl
  choose sr hsr_iso hsr_read using hslot
  letI grp := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).pointGroup (Spec.map (CommRingCat.ofHom ρ))
  have hkey : schemeHomOverComp s₀ (degPull 1) = sinf * (List.ofFn sr).prod := by

    have hsuppU : ∀ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
        Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) →
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).SupportedIn 𝔛.smoothLocus := by
      intro u husm x hx
      rw [RelEffCartierDiv.ofPoint_I, Scheme.Hom.support_ker,
        (graphOver (toBase p (ΓM M H) hj) u.1 u.2).isClosedEmbedding.isClosed_range.closure_eq] at hx
      obtain ⟨t, rfl⟩ := hx
      show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((graphOver (toBase p (ΓM M H) hj) u.1 u.2).base t) ∈
        (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
      rw [← Scheme.Hom.comp_apply, graphOver_fst]
      exact husm ⟨t, rfl⟩
    have hinvU : ∀ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
        Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) →
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).I.IsInvertible := fun u husm =>
      RelEffCartierDiv.isInvertible_I_of_supportedIn 𝔛.smoothLocus _ (hsuppU u husm)
    have hinvV : ∀ (v : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj)),
        (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v.1 v.2).I.IsInvertible := fun v =>
      RelEffCartierDiv.isInvertible_I _

    let Iu₁ := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).I
    let Iu₂ := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).I
    let Ia₁ := fun r : Fin p => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₁ r).1 (a₁ r).2).I
    let Ia₂ := fun r : Fin p => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (a₂ r).1 (a₂ r).2).I
    let Iw₁ := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) w₁.1 w₁.2).I
    let Iw₂ := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) w₂.1 w₂.2).I
    let Ib₁ := fun r : Fin p => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (b₁ r).1 (b₁ r).2).I
    let Ib₂ := fun r : Fin p => (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (b₂ r).1 (b₂ r).2).I
    have hIu₁ : Iu₁.IsInvertible := hinvU u₁ husm₁
    have hIu₂ : Iu₂.IsInvertible := hinvU u₂ husm₂
    have hIa₁ : ∀ r, (Ia₁ r).IsInvertible := fun r => hinvU (a₁ r) (husm'₁ _)
    have hIa₂ : ∀ r, (Ia₂ r).IsInvertible := fun r => hinvU (a₂ r) (husm'₂ _)
    have hIw₁ : Iw₁.IsInvertible := hinvU w₁ hwsm₁
    have hIw₂ : Iw₂.IsInvertible := hinvU w₂ hwsm₂
    have hIb₁ : ∀ r, (Ib₁ r).IsInvertible := fun r => hinvU (b₁ r) (hbsm₁ r)
    have hIb₂ : ∀ r, (Ib₂ r).IsInvertible := fun r => hinvU (b₂ r) (hbsm₂ r)
    let U₁ := HPRead.cls Iu₁.invModule * ∏ r, HPRead.cls (Ia₁ r).invModule
    let U₂ := HPRead.cls Iu₂.invModule * ∏ r, HPRead.cls (Ia₂ r).invModule
    let W₁ := HPRead.cls Iw₁.invModule * ∏ r, HPRead.cls (Ib₁ r).invModule
    let W₂ := HPRead.cls Iw₂.invModule * ∏ r, HPRead.cls (Ib₂ r).invModule
    let N₂ := HPRead.cls Iw₂.module * ∏ r, HPRead.cls (Ib₂ r).module
    have hW₂unit : IsUnit W₂ :=
      (HPRead.isUnit_cls hIw₂.isInvertible_invModule).mul (IsUnit.prod_univ_iff.mpr fun r => HPRead.isUnit_cls (hIb₂ r).isInvertible_invModule)
    have hNW : N₂ * W₂ = 1 := by
      simp only [N₂, W₂]
      rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, HPRead.cls_module_mul_cls_invModule hIw₂,
        Finset.prod_eq_one (fun r _ => HPRead.cls_module_mul_cls_invModule (hIb₂ r)), one_mul]

    let πA := curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ))
    let wA := curveChange 𝔛.w.hom 𝔛.w_over (Spec.map (CommRingCat.ofHom ρ))
    have hπw : curveChange 𝔛.πw.1 𝔛.πw.2 (Spec.map (CommRingCat.ofHom ρ)) = wA ≫ πA :=
      HPRead.curveChange_comp 𝔛.π.1 𝔛.π.2 𝔛.w.hom 𝔛.w_over _ _

    have htr : ∀ (a b : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)) (hb : b.1 = a.1 ≫ 𝔛.w.inv)
        (ha' : (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) a.1 a.2).I.IsInvertible)
        (hb' : (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) b.1 b.2).I.IsInvertible),
        HPRead.pbc wA (HPRead.cls (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) a.1 a.2).I.invModule) =
          HPRead.cls (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) b.1 b.2).I.invModule :=
      fun a b hb ha' hb' => (HPRead.cls_pullback_curveChange_ofPoint 𝔛.w 𝔛.w_over a b hb ha' hb').1
    have hW₁ : HPRead.pbc wA U₁ = W₁ := by
      simp only [U₁, W₁, map_mul, map_prod]
      rw [htr u₁ w₁ hw₁ hIu₁ hIw₁]
      exact congrArg _ (Finset.prod_congr rfl fun r _ => htr (a₁ r) (b₁ r) (hb₁ r) (hIa₁ r) (hIb₁ r))
    have hW₂ : HPRead.pbc wA U₂ = W₂ := by
      simp only [U₂, W₂, map_mul, map_prod]
      rw [htr u₂ w₂ hw₂ hIu₂ hIw₂]
      exact congrArg _ (Finset.prod_congr rfl fun r _ => htr (a₂ r) (b₂ r) (hb₂ r) (hIa₂ r) (hIb₂ r))

    have hc₁ : ((RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).I.comap πA).IsInvertible := by
      rw [hI₁']; exact hIu₁.mul (HPRead.isInvertible_prod _ _ fun r _ => hIa₁ r)
    have hc₂ : ((RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).I.comap πA).IsInvertible := by
      rw [hI₂']; exact hIu₂.mul (HPRead.isInvertible_prod _ _ fun r _ => hIa₂ r)
    have hpull₁ : HPRead.cls ((Scheme.Modules.pullback πA).obj
        (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle) = U₁ := by
      rw [HPRead.cls_congr (Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso πA (hinvV v₁) hc₁).some, hI₁',
        HPRead.cls_invModule_mul_prod _ _ (fun r _ => hIa₁ r) hIu₁]
    have hpull₂ : HPRead.cls ((Scheme.Modules.pullback πA).obj
        (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).lineBundle) = U₂ := by
      rw [HPRead.cls_congr (Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso πA (hinvV v₂) hc₂).some, hI₂',
        HPRead.cls_invModule_mul_prod _ _ (fun r _ => hIa₂ r) hIu₂]
    have hpull₂' : HPRead.cls ((Scheme.Modules.pullback πA).obj
        (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) * U₂ = 1 := by
      rw [← hpull₂, ← HPRead.cls_pullback_tensor,
        HPRead.cls_pullback_congr πA ((HPRead.cls_tensor _ _).trans (HPRead.cls_module_mul_cls_invModule (hinvV v₂))),
        HPRead.cls_pullback_unit]

    have hm₂ : HPRead.pbc wA (HPRead.cls ((Scheme.Modules.pullback πA).obj
        (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule)) * W₂ = 1 := by
      rw [← hW₂, ← map_mul, hpull₂', map_one]

    obtain ⟨edeg⟩ := hdegPull 1 (Spec.map (CommRingCat.ofHom ρ)) s₀
    have hite : (if (1 : Fin 2) = 0 then 𝔛.π else 𝔛.πw) = 𝔛.πw := if_neg (by decide)
    rw [hite] at edeg
    have hLHS : HPRead.cls (hD.poincare.pullbackAlong (schemeHomOverComp s₀ (degPull 1))).L =
        W₁ * HPRead.pbc wA (HPRead.cls ((Scheme.Modules.pullback πA).obj
          (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule)) := by
      rw [HPRead.cls_congr edeg, HPRead.cls_rigidify_of_isLocalRing _ _ ((hD₀.poincare.pullbackAlong s₀).isInvertible.pullback _),
        HPRead.cls_pullback_congr_hom hπw, ← HPRead.cls_pullback_comp, ← HPRead.pbc_cls,
        HPRead.cls_pullback_congr πA (HPRead.cls_congr iso₀), HPRead.cls_pullback_tensor, hpull₁, map_mul, hW₁]

    have hRHS : HPRead.cls (hD.poincare.pullbackAlong (sinf * (List.ofFn sr).prod)).L = W₁ * N₂ := by
      rw [show sinf * (List.ofFn sr).prod = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ sinf
          (List.ofFn sr).prod from rfl,
        HPRead.cls_poincare_mul, HPRead.cls_poincare_list_prod, List.map_ofFn, List.prod_ofFn, HPRead.cls_congr isoinf, HPRead.cls_tensor]
      have hr : ∀ r, HPRead.cls (hD.poincare.pullbackAlong (sr r)).L = HPRead.cls (Ib₁ r).invModule * HPRead.cls (Ib₂ r).module := fun r =>
        (HPRead.cls_congr (hsr_iso r).some).trans (HPRead.cls_tensor _ _)
      simp only [Function.comp_def, hr, Finset.prod_mul_distrib, W₁, N₂]
      rw [mul_mul_mul_comm]

    apply hD.ext_of_iso (Spec.map (CommRingCat.ofHom ρ))
    refine ⟨HPRead.isoOfClsEq ?_⟩
    rw [hLHS, hRHS]
    congr 1
    exact hW₂unit.mul_left_injective (hm₂.trans hNW.symm)

  let φ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase → GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS :=
    fun a => ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ a)
  let ψ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase →
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
    fun a => GluedPic0.toPic0Pair SS (φ a)
  have hcv : ∀ a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom ρ))) a =
        GoodReductionJacobian.schemeHomOverComp (resPt A) rfl a := fun a => Subtype.ext rfl
  have hφmul : ∀ a b : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, φ (a * b) = φ a + φ b := by
    intro a b
    apply ptsSp.injective
    have e2 := HPRead.ofFibrePt_baseChange_mul
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD)
      (schemeHomOverComp ⟨resPt A, rfl⟩ a) (schemeHomOverComp ⟨resPt A, rfl⟩ b)
    simp only [φ]
    rw [Equiv.apply_symm_apply, hptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, e2, hcv, hcv, hcv]
    exact (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul_natural
      (Spec.map (CommRingCat.ofHom ρ)) (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) (resPt A) rfl a b
  have hψmul : ∀ a b : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, ψ (a * b) = ψ a + ψ b := fun a b =>
    congrArg (GluedPic0.toPic0Pair SS) (hφmul a b) |>.trans ((GluedPic0.toPic0Pair SS).map_add _ _)
  have hψone : ψ 1 = 0 := by
    have h := hψmul 1 1
    rw [mul_one] at h
    have h' : ψ 1 + ψ 1 = ψ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hψlist : ∀ l : List (SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase), ψ l.prod = (l.map ψ).sum := by
    intro l
    induction l with
    | nil => rw [List.prod_nil, List.map_nil, List.sum_nil]; exact hψone
    | cons a l ih => rw [List.prod_cons, List.map_cons, List.sum_cons, hψmul, ih]
  have hassoc : schemeHomOverComp (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) (degPull 1) =
      schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom ρ)))
        (schemeHomOverComp s₀ (degPull 1)) :=
    Subtype.ext (Category.assoc _ _ _)
  rw [hassoc, hkey]
  change ψ (sinf * (List.ofFn sr).prod) = _
  rw [hψmul, hψlist, List.map_ofFn]

  have hψinf : ψ sinf = (0, δ (Pic0.mk ⟨_, hDw⟩)) := by
    show GluedPic0.toPic0Pair SS (φ sinf) = _
    have : φ sinf = GluedPic0.mk SS xinf := hsinf
    rw [this, GluedPic0.toPic0Pair_mk]
    refine Prod.ext ?_ ?_
    · show Pic0.mk _ = 0
      exact (congrArg Pic0.mk (Subtype.ext rfl : (⟨((xinf : GluingData _ _ SS)).1, (xinf).2.1⟩ : Divisor.degZero) = 0)).trans
        (QuotientAddGroup.mk_zero _)
    · show Pic0.mk _ = δ _
      rw [hδ, SemilinearAut.pic0_smul_mk]
      refine congrArg Pic0.mk (Subtype.ext ?_)
      rw [SemilinearAut.coe_degZeroSMulHom]
      change Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint R₁) (1 : ℤ) - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint R₂) 1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) •
          (Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) (1 : ℤ) - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1)
      rw [smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single, ← hplR₁, ← hplR₂]

  let Φ := Equiv.ofBijective _ (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM))
  have hxj : ∃ x : ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM), Transcendental (ResidueField ↥A) x ∧
      FiniteDimensional (IntermediateField.adjoin (ResidueField ↥A) ({x} : Set (ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))))
        (ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) := by
    obtain ⟨xj, -, hxj, hfdj⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      (ResidueField ↥A) (ΓN p M H hpM) (ModularCurve.translation_mem_GammaH _ _)
    exact ⟨xj, hxj, hfdj⟩
  have hFdiv := ModularCurve.qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain (ResidueField ↥A) p (ΓN p M H hpM) hxj F hF Φ
    (fun _ => rfl)
  have hψr : ∀ r, ψ (sr r) = (Finv (Pic0.mk ⟨_, hDw⟩), 0) := by
    intro r
    show GluedPic0.toPic0Pair SS (φ (sr r)) = _
    have : φ (sr r) = GluedPic0.mk SS (xr r) := hsr_read r
    rw [this, GluedPic0.toPic0Pair_mk]
    refine Prod.ext ?_ ?_
    · show Pic0.mk _ = Finv (Pic0.mk ⟨_, hDw⟩)
      have hF1 : F (Pic0.mk ⟨((xr r : GluingData _ _ SS)).1, (xr r).2.1⟩) = Pic0.mk ⟨_, hDw⟩ := by
        apply hFdiv
        show Finsupp.single _ 1 - Finsupp.single _ 1 = Finsupp.mapDomain Φ (Finsupp.single _ 1 - Finsupp.single _ 1)
        rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
        show _ = Finsupp.single (qExpFrobeniusPlaceModL _ _ _ _) 1 - Finsupp.single (qExpFrobeniusPlaceModL _ _ _ _) 1
        rw [hplR'₁, hplR'₂, hfrob₁, hfrob₂]
      rw [← hF1]
      exact (DFunLike.congr_fun hFinv.2 _).symm
    · show Pic0.mk _ = 0
      exact (congrArg Pic0.mk (Subtype.ext rfl : (⟨((xr r : GluingData _ _ SS)).2.1, (xr r).2.2.1⟩ : Divisor.degZero) = 0)).trans
        (QuotientAddGroup.mk_zero _)
  have hcompψ : ψ ∘ sr = fun _ => (Finv (Pic0.mk ⟨_, hDw⟩), (0 : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) :=
    funext hψr
  rw [hψinf, hcompψ, List.ofFn_const, List.sum_replicate, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add, hFstar,
    natCast_zsmul]

set_option maxHeartbeats 6400000 in
theorem HPRead.generator_case
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (ptsSp₀ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase)

    (hptsSp₀_add : ∀ a b, ptsSp₀ (a + b) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange
        (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _ (toFibrePt (ptsSp₀ a)) (toFibrePt (ptsSp₀ b))))

    (hptsSp₀ : ∀ (v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1)
      (_ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 = vκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1)
      (_ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 = vκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        Nonempty ((hD₀.poincare.pullbackAlong s₀).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (hptsSp_add : ∀ x y, ptsSp (x + y) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _
        (toFibrePt (ptsSp x)) (toFibrePt (ptsSp y))))
    (hptsSp : ∀ (i : Fin 2)
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (x : ↥(GluingData.admissible SS))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.2 = 0),
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hD.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule) ∧
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x)

    (degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase)
    (hdegPull : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L)))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)
    (i : Fin 2) :
    ∃ S : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
      ∀ (V V₀ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), V ∉ S → V₀ ∉ S →
      ∀ (hVV₀ : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈
          Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))),
        GluedPic0.toPic0Pair SS (ptsSp.symm (schemeHomOverComp
            (ptsSp₀ (Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, hVV₀⟩)) (degPull i))) =
          if i = 0 then (Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, hVV₀⟩,
              Fstar (Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, hVV₀⟩))
          else (Fstar (Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, hVV₀⟩),
              δ (Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, hVV₀⟩)) := by
  classical

  let σpb : SemilinearAut (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
    SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb))
  let T : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) := SS.image Prod.fst ∪ SS.image Prod.snd
  let S : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) :=
    T ∪ T.image (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) ∪ T.image (fun v => σpb • v) ∪ T.image (fun v => σpb⁻¹ • v)
  refine ⟨S, ?_⟩
  intro V V₀ hV hV₀ hVV₀

  let Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C := (𝔛.Mfib A hA ρ hρ).placeEquiv.symm V
  let Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C := (𝔛.Mfib A hA ρ hρ).placeEquiv.symm V₀
  have hQ₁V : (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁ = V := (𝔛.Mfib A hA ρ hρ).placeEquiv.apply_symm_apply V
  have hQ₂V : (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂ = V₀ := (𝔛.Mfib A hA ρ hρ).placeEquiv.apply_symm_apply V₀
  have hTS : ∀ v, v ∈ T → v ∈ S := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
  have hoff1 : ∀ v, v ∉ S → ∀ s ∈ SS, v ≠ s.1 := fun v hv s hs heq =>
    hv (hTS v (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hs, heq.symm⟩)))
  revert hVV₀
  rw [← hQ₁V, ← hQ₂V]
  intro hVV₀
  match i with
  | 0 =>
    rw [if_pos rfl]
    exact HPRead.gen0 p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ D hD D₀ hD₀ ptsSp₀ hptsSp₀_add hptsSp₀ SS hSS ptsSp hptsSp_add hptsSp degPull
      hdegPull F Finv Fstar pb δ hF hFinv hFstar hpb hδ Q₁ Q₂ (hoff1 _ (hQ₁V ▸ hV)) (hoff1 _ (hQ₂V ▸ hV₀)) hVV₀
  | 1 =>
    rw [if_neg (by decide)]
    have hT2 : ∀ s ∈ SS, s.2 ∈ T := fun s hs => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    have hT1 : ∀ s ∈ SS, s.1 ∈ T := fun s hs => Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    have hoffF : ∀ v, v ∉ S → ∀ s ∈ SS, v ≠ qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p s.1 := fun v hv s hs heq =>
      hv (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨s.1, hT1 s hs, heq.symm⟩))))
    have hoffσ : ∀ v, v ∉ S → ∀ s ∈ SS, σpb • v ≠ s.2 := fun v hv s hs heq =>
      hv (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s.2, hT2 s hs, by rw [← heq, inv_smul_smul]⟩))
    exact HPRead.gen1 p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ D hD D₀ hD₀ ptsSp₀ hptsSp₀_add hptsSp₀ SS hSS ptsSp hptsSp_add hptsSp degPull
      hdegPull F Finv Fstar pb δ hF hFinv hFstar hpb hδ Q₁ Q₂ (hoff1 _ (hQ₁V ▸ hV)) (hoff1 _ (hQ₂V ▸ hV₀))
      (hoffF _ (hQ₁V ▸ hV)) (hoffF _ (hQ₂V ▸ hV₀)) (hoffσ _ (hQ₁V ▸ hV)) (hoffσ _ (hQ₂V ▸ hV₀)) hVV₀

set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (ptsSp₀ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase)

    (hptsSp₀_add : ∀ a b, ptsSp₀ (a + b) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange
        (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _ (toFibrePt (ptsSp₀ a)) (toFibrePt (ptsSp₀ b))))

    (hptsSp₀ : ∀ (v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1)
      (_ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 = vκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1)
      (_ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 = vκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        Nonempty ((hD₀.poincare.pullbackAlong s₀).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (hptsSp_add : ∀ x y, ptsSp (x + y) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _
        (toFibrePt (ptsSp x)) (toFibrePt (ptsSp y))))
    (hptsSp : ∀ (i : Fin 2)
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (x : ↥(GluingData.admissible SS))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.2 = 0),
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hD.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule) ∧
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x)

    (degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase)
    (hdegPull : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L)))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z) :
    ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase),
      GluedPic0.toPic0Pair SS (ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (ptsSp₀.symm x, Fstar (ptsSp₀.symm x))
        else (Fstar (ptsSp₀.symm x), δ (ptsSp₀.symm x)) := by
  intro i x
  classical

  let Lf : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := fun z =>
    GluedPic0.toPic0Pair SS (ptsSp.symm (schemeHomOverComp (ptsSp₀ z) (degPull i)))

  let Rf : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := fun z =>
    if i = 0 then (z, Fstar z) else (Fstar z, δ z)

  have hpull_mul := (ModularCurve.XHDRModelAtP.degPull_mul_and_zeroSection_comp_of_classifies_pullback
    p M H hpM hj 𝔛 D hD D₀ hD₀ degPull hdegPull).1
  have hLadd : ∀ a b, Lf (a + b) = Lf a + Lf b := by
    intro a b
    have e1 := HPRead.ofFibrePt_baseChange_mul
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀) (ptsSp₀ a) (ptsSp₀ b)
    have e2 := HPRead.ofFibrePt_baseChange_mul
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD)
      (schemeHomOverComp (ptsSp₀ a) (degPull i)) (schemeHomOverComp (ptsSp₀ b) (degPull i))
    have key : ptsSp.symm (schemeHomOverComp (ptsSp₀ (a + b)) (degPull i)) =
        ptsSp.symm (schemeHomOverComp (ptsSp₀ a) (degPull i)) + ptsSp.symm (schemeHomOverComp (ptsSp₀ b) (degPull i)) := by
      apply ptsSp.injective
      rw [Equiv.apply_symm_apply, hptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hptsSp₀_add, e1, e2]
      exact hpull_mul i _ (ptsSp₀ a) (ptsSp₀ b)
    exact congrArg (GluedPic0.toPic0Pair SS) key |>.trans ((GluedPic0.toPic0Pair SS).map_add _ _)
  have hRadd : ∀ a b, Rf (a + b) = Rf a + Rf b := by
    intro a b
    simp only [Rf]
    split_ifs <;> simp only [map_add, Prod.mk_add_mk]
  let fL : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+ Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := AddMonoidHom.mk' Lf hLadd
  let fR : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+ Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := AddMonoidHom.mk' Rf hRadd

  have hgen := HPRead.generator_case p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ D hD D₀ hD₀ ptsSp₀ hptsSp₀_add hptsSp₀ SS hSS ptsSp hptsSp_add hptsSp degPull hdegPull F Finv Fstar pb δ hF hFinv hFstar hpb hδ i
  obtain ⟨S, hS⟩ := hgen

  have hcurve : IsCurveOver (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ∧
      Algebra.EssFiniteType (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := by
    obtain ⟨xj, -, hxj, hfdj⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      (ResidueField ↥A) (ΓN p M H hpM) (ModularCurve.translation_mem_GammaH _ _)
    exact ⟨AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxj hfdj,
      AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxj hfdj⟩
  haveI := hcurve.1
  haveI := hcurve.2

  haveI := AlgebraicCurve.CurveModel.infinite_place (𝔛.Mfib A hA ρ hρ)
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), V₀ ∉ S :=
    Infinite.exists_notMem_finset S
  have hdense : AddSubgroup.closure
      {y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) | ∃ (V : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (_ : V ∉ S)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := (ResidueField ↥A)) (F := Fbar p M H hpM (ResidueField ↥A))),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single_of_notMem S V₀ hV₀ y
  have heq : fL = fR := by
    refine AddMonoidHom.eq_of_eqOn_dense hdense ?_
    rintro _ ⟨V, hV, hVV₀, rfl⟩
    exact hS V V₀ hV hV₀ hVV₀
  have hx : Lf (ptsSp₀.symm x) = Rf (ptsSp₀.symm x) := DFunLike.congr_fun heq (ptsSp₀.symm x)
  simp only [Lf, Rf, Equiv.apply_symm_apply] at hx
  exact hx

#print axioms solution

end S_ModularCurve_XHDRModelAtP_toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq (solution)
