-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/1cac8e44-3570-5840-83f3-acb5b5696753

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeRingHom ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate"
p2m_attr_erase "simp" "ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom"
p2m_attr_erase "simp" "AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_jqNGen"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E142P3

universe u

theorem exists_opens_smooth_of_iso {X Y S : Scheme.{u}} (w : X ≅ Y) (fX : X ⟶ S) (fY : Y ⟶ S)
    (hw : w.hom ≫ fY = fX) (z : X) (U : X.Opens) (hzU : z ∈ U) (hU : Smooth (U.ι ≫ fX)) :
    ∃ V : Y.Opens, w.hom.base z ∈ V ∧ Smooth (V.ι ≫ fY) := by
  refine ⟨w.hom ''ᵁ U, ⟨z, hzU, rfl⟩, ?_⟩
  have : (w.hom ''ᵁ U).ι ≫ fY = (w.hom.isoImage U).inv ≫ (U.ι ≫ fX) := by
    rw [← hw, ← Scheme.Hom.isoImage_inv_ι w.hom U]
    simp only [Category.assoc]
  rw [this]
  exact (MorphismProperty.cancel_left_of_respectsIso @Smooth _ _).mpr hU

theorem exists_point_of_bijective {B B' : CommRingCat.{u}} (e : B ⟶ B')
    (hbij : Function.Bijective e.hom) {Y Z : Scheme.{u}}
    (ι : Spec B ⟶ Z) (ι' : Spec B' ⟶ Y) (v : Y ⟶ Z)
    (hv : Function.Injective v.base)
    (h : Spec.map e ≫ ι = ι' ≫ v)
    (y : ↥(Spec B)) (x : ↥Y) (hy : ι.base y = v.base x) :
    ∃ y' : ↥(Spec B'), ι'.base y' = x ∧ ∀ b : ↑B, b ∈ y.asIdeal ↔ e.hom b ∈ y'.asIdeal := by
  let ε : ↑B ≃+* ↑B' := RingEquiv.ofBijective e.hom hbij
  let y' : ↥(Spec B') := (Spec.map (CommRingCat.ofHom ε.symm.toRingHom)).base y
  have hmem : ∀ b : ↑B, b ∈ y.asIdeal ↔ e.hom b ∈ y'.asIdeal := by
    intro b
    change b ∈ y.asIdeal ↔ ε.symm (e.hom b) ∈ y.asIdeal
    rw [show ε.symm (e.hom b) = b from ε.symm_apply_apply b]
  have hy'y : (Spec.map e).base y' = y := by
    apply PrimeSpectrum.ext
    ext b
    exact (hmem b).symm
  refine ⟨y', ?_, hmem⟩
  apply hv
  have := congrArg (fun φ => φ.base y') h
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  rw [← this, hy'y, hy]

theorem germ_appTop_mem_maximalIdeal {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing ↑R]
    (f : X ⟶ Spec R) (z : ↥X) (hz : f.base z = closedPoint ↑R) (r : ↑R) (hr : r ∈ maximalIdeal ↑R) :
    (X.presheaf.germ ⊤ z trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) ∈
      maximalIdeal (X.presheaf.stalk z) := by
  have h1 : (X.presheaf.germ ⊤ z trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) =
      (f.stalkMap z).hom (((Spec R).presheaf.germ ⊤ (f.base z) trivial).hom
        ((Scheme.ΓSpecIso R).inv.hom r)) := by
    erw [Scheme.Hom.germ_stalkMap_apply f ⊤ z trivial]
    rfl
  rw [h1]
  apply (IsLocalRing.mem_maximalIdeal _).mpr
  intro hu
  have hu1 := (isUnit_map_iff (f.stalkMap z).hom _).mp hu
  rw [hz] at hu1
  have h2 := congrArg (fun φ => φ.hom r) (Spec.algebraMap_stalkIso_inv (R := R) (closedPoint ↑R))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  erw [← h2] at hu1
  have hu2 : IsUnit (algebraMap ↑R (Localization.AtPrime (closedPoint ↑R).asIdeal) r) := by
    have := hu1.map (Spec.stalkIso R (closedPoint ↑R)).hom.hom
    rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at this
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (closedPoint ↑R).asIdeal) (closedPoint ↑R).asIdeal r] at hu2
  exact hu2 hr

theorem coeffMap_algebraMap' {L L' : Type*} [Field L] [Field L'] (φ : L →+* L') (c : L) :
    ModularCurve.coeffMap φ (algebraMap L (LaurentSeries L) c) = algebraMap L' (LaurentSeries L') (φ c) := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single,
    ModularCurve.coeffMap_single]

theorem exists_primitiveRoot_embedding (q ℓ : ℕ) (hq : q.Prime) (hℓ : ℓ.Prime)
    (K₁ : Type) [Field K₁] [Algebra K₁ (AlgebraicClosure ℚ)]
    (ζ₀ : K₁) (hζ₀ : IsPrimitiveRoot (algebraMap K₁ (AlgebraicClosure ℚ) ζ₀) (q * ℓ)) :
    ∃ ζ : K₁, IsPrimitiveRoot ζ q ∧ (∃ n : ℕ, ζ = ζ₀ ^ n) ∧
      ∃ ι : K₁ →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q) := by
  classical
  have hq0 : q ≠ 0 := hq.ne_zero
  haveI : NeZero q := ⟨hq0⟩
  let ι₀ : AlgebraicClosure ℚ →ₐ[ℚ] ℂ :=
    @IsAlgClosed.lift ℂ _ _ ℚ _ _ (AlgebraicClosure ℚ) _ _ _ _ _ _ (AlgebraicClosure.isAlgebraic ℚ)
  let ι : K₁ →+* ℂ := ι₀.toRingHom.comp (algebraMap K₁ (AlgebraicClosure ℚ))
  have hinjK : Function.Injective (algebraMap K₁ (AlgebraicClosure ℚ)) := (algebraMap K₁ _).injective
  have hμ : IsPrimitiveRoot (ζ₀ ^ ℓ) q := by
    have h' : IsPrimitiveRoot ζ₀ (q * ℓ) := IsPrimitiveRoot.of_map_of_injective hζ₀ hinjK
    exact h'.pow (Nat.pos_of_ne_zero (Nat.mul_ne_zero hq0 hℓ.ne_zero)) (Nat.mul_comm q ℓ ▸ rfl)
  have hιμ : IsPrimitiveRoot (ι (ζ₀ ^ ℓ)) q := hμ.map_of_injective ι.injective
  obtain ⟨i, -, hi⟩ := hιμ.eq_pow_of_pow_eq_one (Complex.isPrimitiveRoot_exp q hq0).pow_eq_one
  refine ⟨(ζ₀ ^ ℓ) ^ i, ?_, ⟨ℓ * i, by rw [pow_mul]⟩, ι, by rw [map_pow, hi]⟩
  apply IsPrimitiveRoot.of_map_of_injective (f := ι) _ ι.injective
  rw [map_pow, hi]
  exact Complex.isPrimitiveRoot_exp q hq0

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Injective g) :
    Function.Injective (ModularCurve.coeffMap g) := by
  intro x y h
  ext n
  apply hg
  have := congrArg (fun z => HahnSeries.coeff z n) h
  simpa [ModularCurve.coeffMap_coeff] using this

def inclA {k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)} (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (A₁ : ValuationSubring ↥K₁)
    (h : ∀ a : ↥A₁, ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ A) : ↥A₁ →+* ↥A where
  toFun a := ⟨((a : ↥K₁) : AlgebraicClosure ℚ), h a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem isAlgClosed_residueField_small {k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (A₁ : ValuationSubring ↥K₁)
    (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧
      ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    IsAlgClosed (ResidueField ↥A₁) := by
  have hA₁A : ∀ a : ↥A₁, ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ A := fun a => (hA₁ a).mp a.2
  let τ := inclA K₁ A A₁ hA₁A
  have hτ : ∀ a, ((τ a : ↥A) : AlgebraicClosure ℚ) = ((a : ↥K₁) : AlgebraicClosure ℚ) := fun _ => rfl

  haveI : IsLocalHom τ := by
    constructor
    intro a ha
    rw [ValuationSubring.valuation_eq_one_iff] at ha ⊢

    by_contra hne
    have hlt : A₁.valuation (a : ↥K₁) < 1 := lt_of_le_of_ne (A₁.valuation_le_one a) hne
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hlt
    have ha' : ¬ (A.valuation ((τ a : ↥A) : AlgebraicClosure ℚ) < 1) := by rw [ha]; exact lt_irrefl 1
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, hτ] at ha'
    push Not at ha'
    rcases hlt with h0 | hinv
    · exact ha'.1 (by rw [h0]; simp)
    · exact hinv ((hA₁ _).mpr (by simpa using ha'.2))
  let ρ := IsLocalRing.ResidueField.map τ
  have hsurj : Function.Surjective ρ := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    obtain ⟨c₀, hc₀A, hsub, hmax⟩ := hκ (a : AlgebraicClosure ℚ) a.2
    refine ⟨IsLocalRing.residue ↥A₁ ⟨algebraMap ↥k₀ ↥K₁ c₀, (hA₁ _).mpr (by simpa using hc₀A)⟩, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]

    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    rw [← neg_mem_iff, neg_sub]
    convert hmax using 1
    rfl
  have hbij : Function.Bijective ρ := ⟨ρ.injective, hsurj⟩
  haveI := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  exact IsAlgClosed.of_ringEquiv (ResidueField ↥A) (ResidueField ↥A₁) (RingEquiv.ofBijective ρ hbij).symm

theorem iso_hom_inv_base {X Y : Scheme.{u}} (w : X ≅ Y) (y : ↥Y) : w.hom.base (w.inv.base y) = y := by
  change (w.inv ≫ w.hom).base y = y
  rw [w.inv_hom_id]
  rfl

theorem exists_iso_goodPt_transport (q : ℕ) {R : Type} [CommRing R] [IsLocalRing R]
    {F F' : Type} [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (jF : F) (jF' : F') [Fact (jF ≠ 0)] [Fact (jF' ≠ 0)]
    (σ : F ≃ₐ[R] F') (hσj : σ jF = jF')
    (PF : F → Prop) (PF' : F' → Prop) (hP : ∀ b : F, PF b → PF' (σ b))
    (x : ↥(TwoChartIntegralModel R F' jF'))
    (hGbase : (TwoChartIntegralModel.toBase R F' jF').base x = closedPoint R)
    (hGFin : ∀ y : ↥(TwoChartIntegralModel.XFin R F' jF'), (TwoChartIntegralModel.ιFin R F' jF').base y = x →
        ∀ b : ↥(TwoChartIntegralModel.chartAlgFin R F' jF'), PF' (b : F') → b ∈ y.asIdeal)
    (hGInf : ∀ y : ↥(TwoChartIntegralModel.XInf R F' jF'), (TwoChartIntegralModel.ιInf R F' jF').base y = x →
        ∀ b : ↥(TwoChartIntegralModel.chartAlgInf R F' jF'), PF' (b : F') → b ∈ y.asIdeal)
    (hGord : ∀ y : ↥(TwoChartIntegralModel.XFin R F' jF'), (TwoChartIntegralModel.ιFin R F' jF').base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(TwoChartIntegralModel.chartAlgFin R F' jF') →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (TwoChartIntegralModel.jChartFin R F' jF') ∉ ModularCurve.ssJSet q Ω) :
    ∃ w : TwoChartIntegralModel R F jF ≅ TwoChartIntegralModel R F' jF',
      w.hom ≫ TwoChartIntegralModel.toBase R F' jF' = TwoChartIntegralModel.toBase R F jF ∧
      w.hom.base (w.inv.base x) = x ∧
      (TwoChartIntegralModel.toBase R F jF).base (w.inv.base x) = closedPoint R ∧
      (∀ y : ↥(TwoChartIntegralModel.XFin R F jF), (TwoChartIntegralModel.ιFin R F jF).base y = w.inv.base x →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgFin R F jF), PF (b : F) → b ∈ y.asIdeal) ∧
      (∀ y : ↥(TwoChartIntegralModel.XInf R F jF), (TwoChartIntegralModel.ιInf R F jF).base y = w.inv.base x →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgInf R F jF), PF (b : F) → b ∈ y.asIdeal) ∧
      (∀ y : ↥(TwoChartIntegralModel.XFin R F jF), (TwoChartIntegralModel.ιFin R F jF).base y = w.inv.base x →
          ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
            (φ : ↥(TwoChartIntegralModel.chartAlgFin R F jF) →+* Ω), RingHom.ker φ = y.asIdeal →
              φ (TwoChartIntegralModel.jChartFin R F jF) ∉ ModularCurve.ssJSet q Ω) := by
  have hcomm : ∀ r : R, (σ : F ≃+* F') (algebraMap R F r) = algebraMap R F' r := fun r => σ.commutes r
  obtain ⟨w, eFin, eInf, hcoeFin, hcoeInf, hwbase, hιFin, hιInf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq R F F' jF jF' σ hσj
  have hC1 := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv
    (R := R) (σ : F ≃+* F') hcomm).1
  have hbijFin : Function.Bijective (CommRingCat.ofHom eFin.toRingHom).hom := by
    rw [CommRingCat.hom_ofHom]
    constructor
    · intro a b h
      apply Subtype.ext
      apply σ.injective
      rw [← hcoeFin, ← hcoeFin]
      exact congrArg Subtype.val h
    · intro c
      have hb : σ.symm (c : F') ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F jF := by
        have := hC1 {jF} (σ.symm c)
        rw [Set.image_singleton] at this
        rw [show AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F jF =
          AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {jF} from rfl, this]
        change σ (σ.symm c) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg R F' {(σ : F ≃+* F') jF}
        rw [σ.apply_symm_apply, show (σ : F ≃+* F') jF = jF' from hσj]
        exact c.2
      exact ⟨⟨σ.symm c, hb⟩, Subtype.ext ((hcoeFin ⟨_, hb⟩).trans (σ.apply_symm_apply _))⟩
  have hbijInf : Function.Bijective (CommRingCat.ofHom eInf.toRingHom).hom := by
    rw [CommRingCat.hom_ofHom]
    constructor
    · intro a b h
      apply Subtype.ext
      apply σ.injective
      rw [← hcoeInf, ← hcoeInf]
      exact congrArg Subtype.val h
    · intro c
      have hb : σ.symm (c : F') ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F jF := by
        have := hC1 {jF⁻¹} (σ.symm c)
        rw [Set.image_singleton, map_inv₀] at this
        rw [show AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F jF =
          AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {jF⁻¹} from rfl, this]
        change σ (σ.symm c) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg R F' {((σ : F ≃+* F') jF)⁻¹}
        rw [σ.apply_symm_apply, show (σ : F ≃+* F') jF = jF' from hσj]
        exact c.2
      exact ⟨⟨σ.symm c, hb⟩, Subtype.ext ((hcoeInf ⟨_, hb⟩).trans (σ.apply_symm_apply _))⟩
  have hwinj : Function.Injective w.inv.base :=
    Function.LeftInverse.injective (g := w.hom.base) (iso_hom_inv_base w)
  have hzbase : (AlgebraicCurve.TwoChartIntegralModel.toBase R F jF).base (w.inv.base x) = closedPoint R := by
    rw [← hwbase]
    change (AlgebraicCurve.TwoChartIntegralModel.toBase R F' jF').base (w.hom.base (w.inv.base x)) = _
    rw [iso_hom_inv_base, hGbase]
  refine ⟨w, hwbase, iso_hom_inv_base w x, hzbase, ?_, ?_, ?_⟩
  · intro y hy b hb
    obtain ⟨y', hy'x, hmem⟩ := exists_point_of_bijective (CommRingCat.ofHom eFin.toRingHom) hbijFin _ _ w.inv hwinj hιFin y x hy
    apply (hmem b).mpr
    apply hGFin y' hy'x
    have h1 : (((CommRingCat.ofHom eFin.toRingHom).hom b : _) : F') = σ b := by
      change ((eFin b : _) : F') = σ b
      rw [hcoeFin]
    rw [h1]
    exact hP _ hb
  · intro y hy b hb
    obtain ⟨y', hy'x, hmem⟩ := exists_point_of_bijective (CommRingCat.ofHom eInf.toRingHom) hbijInf _ _ w.inv hwinj hιInf y x hy
    apply (hmem b).mpr
    apply hGInf y' hy'x
    have h1 : (((CommRingCat.ofHom eInf.toRingHom).hom b : _) : F') = σ b := by
      change ((eInf b : _) : F') = σ b
      rw [hcoeInf]
    rw [h1]
    exact hP _ hb
  · intro y hy Ω _ _ _ _ φ hker
    obtain ⟨y', hy'x, hmem⟩ := exists_point_of_bijective (CommRingCat.ofHom eFin.toRingHom) hbijFin _ _ w.inv hwinj hιFin y x hy
    let ε := RingEquiv.ofBijective eFin.toRingHom (by simpa only [CommRingCat.hom_ofHom] using hbijFin)
    have hε : ∀ b, ε b = eFin b := fun _ => rfl
    have hker' : RingHom.ker (φ.comp ε.symm.toRingHom) = y'.asIdeal := by
      ext c
      rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hker]
      change ε.symm c ∈ y.asIdeal ↔ c ∈ y'.asIdeal
      rw [hmem]
      change ε (ε.symm c) ∈ y'.asIdeal ↔ c ∈ y'.asIdeal
      rw [ε.apply_symm_apply]
    have := hGord y' hy'x Ω (φ.comp ε.symm.toRingHom) hker'
    have hjj : ε.symm (AlgebraicCurve.TwoChartIntegralModel.jChartFin R F' jF') =
        AlgebraicCurve.TwoChartIntegralModel.jChartFin R F jF := by
      apply ε.injective
      rw [ε.apply_symm_apply, hε]
      apply Subtype.ext
      rw [hcoeFin]
      exact hσj.symm
    rw [RingHom.comp_apply] at this
    change φ (ε.symm (AlgebraicCurve.TwoChartIntegralModel.jChartFin R F' jF')) ∉ _ at this
    rwa [hjj] at this

theorem core (q : ℕ) {R : Type} [CommRing R] [IsLocalRing R]
    {F F' : Type} [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (jF : F) (jF' : F') [Fact (jF ≠ 0)] [Fact (jF' ≠ 0)]
    (σ : F ≃ₐ[R] F') (hσj : σ jF = jF')
    (PF : F → Prop) (PF' : F' → Prop) (hP : ∀ b : F, PF b → PF' (σ b))
    (ϖ : R) (hϖ : ϖ ∈ maximalIdeal R)
    (x : ↥(TwoChartIntegralModel R F' jF'))
    (hGbase : (TwoChartIntegralModel.toBase R F' jF').base x = closedPoint R)
    (hGFin : ∀ y : ↥(TwoChartIntegralModel.XFin R F' jF'), (TwoChartIntegralModel.ιFin R F' jF').base y = x →
        ∀ b : ↥(TwoChartIntegralModel.chartAlgFin R F' jF'), PF' (b : F') → b ∈ y.asIdeal)
    (hGInf : ∀ y : ↥(TwoChartIntegralModel.XInf R F' jF'), (TwoChartIntegralModel.ιInf R F' jF').base y = x →
        ∀ b : ↥(TwoChartIntegralModel.chartAlgInf R F' jF'), PF' (b : F') → b ∈ y.asIdeal)
    (hGord : ∀ y : ↥(TwoChartIntegralModel.XFin R F' jF'), (TwoChartIntegralModel.ιFin R F' jF').base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(TwoChartIntegralModel.chartAlgFin R F' jF') →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (TwoChartIntegralModel.jChartFin R F' jF') ∉ ModularCurve.ssJSet q Ω)
    (hX : ∀ (z : ↥(TwoChartIntegralModel R F jF))
        (ϖz : (TwoChartIntegralModel R F jF).presheaf.stalk z),
        ϖz = ((TwoChartIntegralModel R F jF).presheaf.germ ⊤ z trivial).hom
           (((TwoChartIntegralModel.toBase R F jF).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) →
        ϖz ∈ maximalIdeal ((TwoChartIntegralModel R F jF).presheaf.stalk z) →
        (∀ y : ↥(TwoChartIntegralModel.XFin R F jF), (TwoChartIntegralModel.ιFin R F jF).base y = z →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgFin R F jF), PF (b : F) → b ∈ y.asIdeal) →
        (∀ y : ↥(TwoChartIntegralModel.XInf R F jF), (TwoChartIntegralModel.ιInf R F jF).base y = z →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgInf R F jF), PF (b : F) → b ∈ y.asIdeal) →
        (∀ y : ↥(TwoChartIntegralModel.XFin R F jF), (TwoChartIntegralModel.ιFin R F jF).base y = z →
          ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
            (φ : ↥(TwoChartIntegralModel.chartAlgFin R F jF) →+* Ω), RingHom.ker φ = y.asIdeal →
              φ (TwoChartIntegralModel.jChartFin R F jF) ∉ ModularCurve.ssJSet q Ω) →
        ∃ U : (TwoChartIntegralModel R F jF).Opens, z ∈ U ∧ Smooth (U.ι ≫ TwoChartIntegralModel.toBase R F jF)) :
    ∃ U : (TwoChartIntegralModel R F' jF').Opens, x ∈ U ∧ Smooth (U.ι ≫ TwoChartIntegralModel.toBase R F' jF') := by
  have hT := exists_iso_goodPt_transport q jF jF' σ hσj PF PF' hP x hGbase hGFin hGInf hGord
  obtain ⟨w, hwbase, hwx, hzbase, hzFin, hzInf, hord⟩ := hT
  have hz := germ_appTop_mem_maximalIdeal (AlgebraicCurve.TwoChartIntegralModel.toBase R F jF)
    (w.inv.base x) hzbase ϖ hϖ
  obtain ⟨U, hzU, hU⟩ := hX (w.inv.base x) _ rfl hz hzFin hzInf hord
  obtain ⟨V, hxV, hV⟩ := exists_opens_smooth_of_iso w _ _ hwbase (w.inv.base x) U hzU hU
  rw [hwx] at hxV
  exact ⟨V, hxV, hV⟩

end E142P3

open E142P3

theorem E142P3.isAlgebraic_rat_intermediateField {k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) [inst : Algebra ℚ ↥K₁] : Algebra.IsAlgebraic ℚ ↥K₁ := by
  let f : ↥K₁ →ₐ[ℚ] AlgebraicClosure ℚ := (algebraMap ↥K₁ (AlgebraicClosure ℚ)).toRatAlgHom
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
    rfl
    rfl
  exact Algebra.IsAlgebraic.of_injective f (algebraMap ↥K₁ (AlgebraicClosure ℚ)).injective

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    ∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)), GoodPt x →
      ∃ U : (AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).Opens,
        x ∈ U ∧ Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) := by
  intro F₀ hK1 hstab hLD hRAT instAlg halg j₁ hj₁ instFact
  dsimp only
  intro x hG
  obtain ⟨hGbase, hGclosed, hGFin, hGInf, hGord⟩ := hG
  have hqprime : q.Prime := Fact.out
  have hA₁A : ∀ a : ↥A₁, ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ A := fun a => (hA₁ a).mp a.2

  have hζ₀' : IsPrimitiveRoot (algebraMap ↥K₁ (AlgebraicClosure ℚ) (algebraMap ↥k₀ ↥K₁ ζ₀)) (q * ℓ) := by
    convert hζ₀ using 2
    rfl
  obtain ⟨ζ, hζ, ⟨nζ, hζpow⟩, hι⟩ := exists_primitiveRoot_embedding q ℓ hqprime hℓ ↥K₁ (algebraMap ↥k₀ ↥K₁ ζ₀) hζ₀'
  have hζA : ∃ a : ↥A₁, algebraMap ↥A₁ ↥K₁ a = ζ := by
    suffices hmem : ζ ∈ A₁ from ⟨⟨ζ, hmem⟩, rfl⟩
    have hq1 : ζ ^ q = 1 := hζ.pow_eq_one
    rcases A₁.mem_or_inv_mem ζ with h | h
    · exact h
    · have h1 : ζ ^ (q - 1) = ζ⁻¹ := eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hqprime.ne_zero, hq1])
      have : ζ = (ζ⁻¹) ^ (q - 1) := by rw [inv_pow, h1, inv_inv]
      rw [this]
      exact pow_mem h _
  have hAq : (q : ↥A₁) ∈ maximalIdeal ↥A₁ := by
    have hA' : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
    rw [ValuationSubring.mem_nonunits_iff_or] at hA'
    rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff_or]
    right
    rcases hA' with h0 | hinv
    · exact absurd h0 (Nat.cast_ne_zero.mpr hqprime.ne_zero)
    · intro hmem
      apply hinv
      have := (hA₁ _).mp hmem
      simpa using this
  haveI : IsAlgClosed (ResidueField ↥A₁) := isAlgClosed_residueField_small K₁ A A₁ hA₁ hκ
  haveI : Algebra.IsAlgebraic ℚ ↥K₁ := E142P3.isAlgebraic_rat_intermediateField K₁

  letI algK : Algebra ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) :=
    ((algebraMap ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))).comp
      (algebraMap ↥A₁ ↥K₁)).toAlgebra
  haveI ist : IsScalarTower ↥A₁ ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) :=
    IsScalarTower.of_algebraMap_eq (R := ↥A₁) (S := ↥K₁) (A := ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) (fun _ => rfl)

  obtain ⟨e, he⟩ := ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
    q M' k₀ K₁ hK₁ F₀ hK1 (hLD K₁ hK₁) hRAT
  have hcomm : ∀ a : ↥A₁, e (algebraMap ↥A₁ _ a) = algebraMap ↥A₁ _ a := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    rw [he, halg a]
    change ModularCurve.coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (algebraMap ↥K₁ (LaurentSeries ↥K₁) (a : ↥K₁)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((a : ↥K₁) : AlgebraicClosure ℚ)
    rw [coeffMap_algebraMap']
    rfl
  let σ : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) ≃ₐ[↥A₁] _ :=
    AlgEquiv.ofRingEquiv (f := e) hcomm
  have hσ : ∀ f, σ f = e f := fun _ => rfl

  have hej : e (e.symm j₁) = j₁ := e.apply_symm_apply j₁
  have hj : ((e.symm j₁ : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) :
      LaurentSeries ↥K₁) = coeffEmb ↥K₁ jq := by
    apply coeffMap_injective (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (algebraMap ↥K₁ (AlgebraicClosure ℚ)).injective
    rw [← he, hej, hj₁]
    change coeffEmb (AlgebraicClosure ℚ) jq = _
    rw [coeffEmb, coeffEmb, ModularCurve.coeffMap_coeffMap]
    exact ModularCurve.coeffMap_congr (Subsingleton.elim _ _) _
  haveI hjfact : Fact (e.symm j₁ ≠ 0) := ⟨fun h => (Fact.out : j₁ ≠ 0) (by rw [← hej, h, map_zero])⟩
  have hσj : σ (e.symm j₁) = j₁ := by rw [hσ, hej]

  obtain ⟨W₀, hW₀, -, -, -, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) ↥K₁
      (laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) rfl ↥A₁ (e.symm j₁) hj
  have hbr := ModularCurve.mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
    k₀ K₁ A A₁ hA₁ _ W₀ hW₀ (fieldBar q M') (OIg (lineInfty q)) hIg_inf
    ((algebraMap _ ↥(fieldBar q M')).comp e.toRingHom) (fun f => he f)

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible ↥A₁
  have hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq

  have key :=
    ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic
      q hq M' hqM' ↥K₁ ζ hζ hι _ rfl ↥A₁ hAq hζA (e.symm j₁) hj ϖ hϖ W₀ hW₀
  exact core q (e.symm j₁) j₁ σ hσj (fun b => b ∈ W₀.nonunits)
    (fun c => (c : ↥(fieldBar q M')) ∈ R.integers.nonunits)
    (fun b hb => by beta_reduce; rw [hR]; exact (hbr.2 b).mp hb)
    ϖ (hϖ ▸ Ideal.mem_span_singleton_self ϖ) x hGbase hGFin hGInf hGord key

end S_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel (solution)
