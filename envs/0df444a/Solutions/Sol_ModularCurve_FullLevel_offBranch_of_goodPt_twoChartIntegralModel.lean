-- Prove2me | solution 1 for ModularCurve.FullLevel.offBranch_of_goodPt_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/22a0699a-746a-5557-88f8-4d0fc4ee966a

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
import Theorems.Thm_ModularCurve_FullLevel_isRegularLocalRing_stalk_quotient_span_of_goodPt_twoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgInf
import Theorems.Thm_ModularCurve_FullLevel_transcendental_and_finiteDimensional_adjoin_levelField
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_ModularCurve_FullLevel_mem_igusaRing_coe_levelField_and_injective_twoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_offBranch_of_goodPt_twoChartIntegralModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeRingHom ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate"
p2m_attr_erase "simp" "ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom"
p2m_attr_erase "simp" "AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_jqNGen"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E147B3

universe u

theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] (V : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (V.comap f).nonunits ↔ f x ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero_iff f f.injective]

theorem eq_of_le_of_height_eq_one {S : Type*} [CommRing S] [IsDomain S] {Q P : Ideal S} [hQ : Q.IsPrime]
    (hP : P.IsPrime) (hQ0 : Q ≠ ⊥) (hle : Q ≤ P) (hh : P.height = 1) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hle hne
  haveI := hP
  haveI : P.FiniteHeight := (Ideal.finiteHeight_iff P).mpr (Or.inr (by rw [hh]; exact ENat.one_ne_top))
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  rw [hh] at h1
  have hQh : Q.height = 0 := ENat.lt_one_iff_eq_zero.mp h1
  haveI : Q.FiniteHeight := (Ideal.finiteHeight_iff Q).mpr (Or.inr (by rw [hQh]; exact ENat.zero_ne_top))
  have hbot : (⊥ : Ideal S) < Q := bot_lt_iff_ne_bot.mpr hQ0
  haveI : (⊥ : Ideal S).IsPrime := Ideal.isPrime_bot
  have h0 := Ideal.height_strict_mono_of_isPrime_of_isPrime hbot
  rw [hQh] at h0
  simp at h0

theorem comap_span_le {S : Type*} [CommRing S] [IsDomain S] (𝔭 : Ideal S) [𝔭.IsPrime] (ϖ : S)
    (P : Ideal S) (hP : P.IsPrime) (hPle : P ≤ 𝔭) (hϖP : ϖ ∈ P) :
    (Ideal.span {algebraMap S (Localization.AtPrime 𝔭) ϖ}).comap (algebraMap S (Localization.AtPrime 𝔭)) ≤ P := by
  intro b hb
  rw [Ideal.mem_comap] at hb
  have hb' : algebraMap S (Localization.AtPrime 𝔭) b ∈
      (Ideal.span {ϖ}).map (algebraMap S (Localization.AtPrime 𝔭)) := by
    rw [Ideal.map_span, Set.image_singleton]; exact hb
  rw [IsLocalization.mem_map_algebraMap_iff 𝔭.primeCompl] at hb'
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ := hb'
  have hinj : Function.Injective (algebraMap S (Localization.AtPrime 𝔭)) :=
    IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors
  have h' : b * s = a := by
    apply hinj
    rw [map_mul]
    exact h
  have has : a ∈ P := (Ideal.span_singleton_le_iff_mem _).mpr hϖP ha
  rw [← h'] at has
  rcases hP.mem_or_mem has with hbP | hsP
  · exact hbP
  · exact absurd (hPle hsP) hs

theorem branch_inv {R F : Type*} [CommRing R] [IsLocalRing R] [Field F] [Algebra R F] (j : F)
    (V : ValuationSubring F)
    (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) :
    ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V := by
  intro P hP
  have hX : (Polynomial.X : Polynomial R).map (IsLocalRing.residue R) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  obtain ⟨hjV, hjiV⟩ := hVj Polynomial.X hX
  rw [Polynomial.aeval_X] at hjV hjiV
  rcases eq_or_ne j 0 with hj0 | hj0
  ·
    subst hj0
    rw [inv_zero]
    have h0 : Polynomial.aeval (0 : F) P = algebraMap R F (P.coeff 0) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero]

    have := hVj P hP
    rw [show (0 : F) = 0⁻¹ from inv_zero.symm] at this ⊢
    simpa using this
  ·
    have hrev : (P.reverse).map (IsLocalRing.residue R) ≠ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, (P.map (IsLocalRing.residue R)).coeff i ≠ 0 := by
        by_contra h
        push Not at h
        exact hP (Polynomial.ext (by simpa using h))
      rw [Polynomial.coeff_map] at hi
      have hid : i ≤ P.natDegree := Polynomial.le_natDegree_of_ne_zero (fun h => hi (by rw [h, map_zero]))
      intro h
      have := congrArg (fun Q => Polynomial.coeff Q (P.natDegree - i)) h
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coeff_reverse] at this
      rw [Polynomial.revAt_le (Nat.sub_le P.natDegree i), Nat.sub_sub_self hid] at this
      exact hi this
    obtain ⟨hrV, hriV⟩ := hVj P.reverse hrev
    haveI : Invertible (j⁻¹) := invertibleOfNonzero (inv_ne_zero hj0)
    have key : Polynomial.aeval j⁻¹ P = Polynomial.aeval j P.reverse * (j⁻¹) ^ P.natDegree := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval₂_reverse_mul_pow (algebraMap R F) j⁻¹ P]
      congr 2
      rw [invOf_eq_inv, inv_inv]
    refine ⟨?_, ?_⟩
    · rw [key]; exact V.mul_mem _ _ hrV (V.toSubring.pow_mem hjiV P.natDegree)
    · rw [key, mul_inv, ← inv_pow, inv_inv]; exact V.mul_mem _ _ hriV (V.toSubring.pow_mem hjV P.natDegree)

end E147B3

namespace E147B3

universe u

theorem exists_mem_nonunits_and_not_mem
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (V V' : ValuationSubring F)
    (hVA : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits)
    (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
    (hVA' : ∀ a : R, algebraMap R F a ∈ V')
    (hVm' : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V'.nonunits)
    (hVj' : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V')
    (hne : V ≠ V')
    (𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlgFin R F j)) [𝔭.IsPrime]
    (hdom : IsDomain (Localization.AtPrime 𝔭 ⧸ Ideal.span
      {algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime 𝔭)
        (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ)}))
    (hV𝔭 : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin R F j), (b : F) ∈ V.nonunits → b ∈ 𝔭) :
    ∃ b : ↥(TwoChartIntegralModel.chartAlgFin R F j), (b : F) ∈ V'.nonunits ∧ b ∉ 𝔭 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, ⟨P, hPpr, hPh, hPmem, hPϖ, -⟩, hd⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      R K₀ F j htj hFD hsep V hVA hVm hVj
  obtain ⟨-, ⟨P', hP'pr, hP'h, hP'mem, hP'ϖ, -⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      R K₀ F j htj hFD hsep V' hVA' hVm' hVj'
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have hϖP : algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ ∈ P := hPϖ ϖ hϖm
  have hϖP' : algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ ∈ P' := hP'ϖ ϖ hϖm
  have hPle : P ≤ 𝔭 := fun b hb => hV𝔭 b ((hPmem b).mp hb)
  have hP'le : P' ≤ 𝔭 := fun b hb => hcon b ((hP'mem b).mp hb)
  have hϖ0 : algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ ≠ 0 := by
    intro h0
    have h1 : algebraMap R F ϖ = 0 := by
      have := congrArg (fun b : ↥(TwoChartIntegralModel.chartAlgFin R F j) => (b : F)) h0
      simpa using this
    rw [IsScalarTower.algebraMap_apply R K₀ F, map_eq_zero_iff _ (algebraMap K₀ F).injective,
      map_eq_zero_iff _ (IsFractionRing.injective R K₀)] at h1
    apply IsDiscreteValuationRing.not_a_field R
    rw [hϖ, h1, Ideal.span_singleton_eq_bot]
  haveI hspan : (Ideal.span {algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime 𝔭)
      (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ)}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  haveI hQ : ((Ideal.span {algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime 𝔭)
      (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ)}).comap
      (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime 𝔭))).IsPrime :=
    Ideal.comap_isPrime _ _
  have hQ0 : (Ideal.span {algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime 𝔭)
      (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ)}).comap
      (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime 𝔭)) ≠ ⊥ := by
    intro h
    apply hϖ0
    have : algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ ∈ (⊥ : Ideal ↥(TwoChartIntegralModel.chartAlgFin R F j)) := by
      rw [← h, Ideal.mem_comap]
      exact Ideal.mem_span_singleton_self _
    exact (Submodule.mem_bot _).mp this
  have hQP := eq_of_le_of_height_eq_one hPpr hQ0 (comap_span_le 𝔭 _ P hPpr hPle hϖP) hPh
  have hQP' := eq_of_le_of_height_eq_one hP'pr hQ0 (comap_span_le 𝔭 _ P' hP'pr hP'le hϖP') hP'h
  obtain ⟨b, hbV', hbV⟩ := hd V' hVA' hVm' hVj' hne
  apply hbV
  rw [← hPmem b, ← hQP, hQP', hP'mem b]
  exact hbV'

end E147B3

namespace E147B3

universe u

theorem isDomain_fin {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(TwoChartIntegralModel.XFin R F j)) (z : ↥(TwoChartIntegralModel R F j))
    (hy : (TwoChartIntegralModel.ιFin R F j).base y = z) (ϖ : R)
    (hreg : IsRegularLocalRing (↑((TwoChartIntegralModel R F j).presheaf.stalk z) ⧸ Ideal.span
      {((TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))})) :
    IsDomain (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgFin R F j) _ y.asIdeal _ ⧸ Ideal.span
      {algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgFin R F j) _ y.asIdeal _)
        (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ)}) := by
  subst hy
  obtain ⟨e, he, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin R F j y ⟨y, trivial, rfl⟩
  let ε : ↑((TwoChartIntegralModel R F j).presheaf.stalk ((TwoChartIntegralModel.ιFin R F j).base y)) ≃+* @Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgFin R F j) _ y.asIdeal _ :=
    e.commRingCatIsoToRingEquiv
  have hε : ε (((TwoChartIntegralModel R F j).presheaf.germ ⊤ ((TwoChartIntegralModel.ιFin R F j).base y) trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))) =
      algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgFin R F j) _ y.asIdeal _)
        (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ) := by
    rw [← IsScalarTower.algebraMap_apply]; exact he ϖ
  haveI := hreg
  have hreg' : IsRegularLocalRing (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgFin R F j) _ y.asIdeal _ ⧸ Ideal.span
      {algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgFin R F j) _ y.asIdeal _)
        (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ)}) := IsRegularLocalRing.of_ringEquiv
    (Ideal.quotientEquiv
      (Ideal.span {((TwoChartIntegralModel R F j).presheaf.germ ⊤ ((TwoChartIntegralModel.ιFin R F j).base y) trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))})
      (Ideal.span {algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgFin R F j) _ y.asIdeal _)
        (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ)}) ε
      (by rw [Ideal.map_span, Set.image_singleton]; exact congrArg (fun a => Ideal.span {a}) hε.symm))
  exact @IsRegularLocalRing.isDomain _ _ hreg'

theorem isDomain_inf {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(TwoChartIntegralModel.XInf R F j)) (z : ↥(TwoChartIntegralModel R F j))
    (hy : (TwoChartIntegralModel.ιInf R F j).base y = z) (ϖ : R)
    (hreg : IsRegularLocalRing (↑((TwoChartIntegralModel R F j).presheaf.stalk z) ⧸ Ideal.span
      {((TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))})) :
    IsDomain (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgInf R F j) _ y.asIdeal _ ⧸ Ideal.span
      {algebraMap ↥(TwoChartIntegralModel.chartAlgInf R F j) (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgInf R F j) _ y.asIdeal _)
        (algebraMap R ↥(TwoChartIntegralModel.chartAlgInf R F j) ϖ)}) := by
  subst hy
  obtain ⟨e, he, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgInf R F j y ⟨y, trivial, rfl⟩
  let ε : ↑((TwoChartIntegralModel R F j).presheaf.stalk ((TwoChartIntegralModel.ιInf R F j).base y)) ≃+* @Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgInf R F j) _ y.asIdeal _ :=
    e.commRingCatIsoToRingEquiv
  have hε : ε (((TwoChartIntegralModel R F j).presheaf.germ ⊤ ((TwoChartIntegralModel.ιInf R F j).base y) trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))) =
      algebraMap ↥(TwoChartIntegralModel.chartAlgInf R F j) (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgInf R F j) _ y.asIdeal _)
        (algebraMap R ↥(TwoChartIntegralModel.chartAlgInf R F j) ϖ) := by
    rw [← IsScalarTower.algebraMap_apply]; exact he ϖ
  haveI := hreg
  have hreg' : IsRegularLocalRing (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgInf R F j) _ y.asIdeal _ ⧸ Ideal.span
      {algebraMap ↥(TwoChartIntegralModel.chartAlgInf R F j) (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgInf R F j) _ y.asIdeal _)
        (algebraMap R ↥(TwoChartIntegralModel.chartAlgInf R F j) ϖ)}) := IsRegularLocalRing.of_ringEquiv
    (Ideal.quotientEquiv
      (Ideal.span {((TwoChartIntegralModel R F j).presheaf.germ ⊤ ((TwoChartIntegralModel.ιInf R F j).base y) trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))})
      (Ideal.span {algebraMap ↥(TwoChartIntegralModel.chartAlgInf R F j) (@Localization.AtPrime ↥(TwoChartIntegralModel.chartAlgInf R F j) _ y.asIdeal _)
        (algebraMap R ↥(TwoChartIntegralModel.chartAlgInf R F j) ϖ)}) ε
      (by rw [Ideal.map_span, Set.image_singleton]; exact congrArg (fun a => Ideal.span {a}) hε.symm))
  exact @IsRegularLocalRing.isDomain _ _ hreg'

abbrev fieldOf {K L : Type*} [Field K] [Field L] [Algebra K L] {S : IntermediateField K L} (_x : ↥S) :
    IntermediateField K L := S

theorem adjoin_inv_eq {K L : Type*} [Field K] [Field L] [Algebra K L] (x : L) :
    IntermediateField.adjoin K ({x⁻¹} : Set L) = IntermediateField.adjoin K ({x} : Set L) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
    rwa [inv_inv] at this

end E147B3

namespace E147B3

universe u

theorem offBranch_fin
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (V V' : ValuationSubring F)
    (hVA : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits)
    (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
    (hVA' : ∀ a : R, algebraMap R F a ∈ V')
    (hVm' : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V'.nonunits)
    (hVj' : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V')
    (hne : V ≠ V')
    (y : ↥(TwoChartIntegralModel.XFin R F j)) (z : ↥(TwoChartIntegralModel R F j))
    (hy : (TwoChartIntegralModel.ιFin R F j).base y = z)
    (hreg : IsRegularLocalRing (↑((TwoChartIntegralModel R F j).presheaf.stalk z) ⧸ Ideal.span
      {((TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))}))
    (hV𝔭 : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) :
    ∃ b : ↥(TwoChartIntegralModel.chartAlgFin R F j), (b : F) ∈ V'.nonunits ∧ b ∉ y.asIdeal := by
  have hdom := isDomain_fin j y z hy ϖ hreg
  exact exists_mem_nonunits_and_not_mem R K₀ F j htj hFD hsep ϖ hϖ V V' hVA hVm hVj hVA' hVm' hVj' hne
    y.asIdeal hdom hV𝔭

theorem offBranch_inf
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (V V' : ValuationSubring F)
    (hVA : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits)
    (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
    (hVA' : ∀ a : R, algebraMap R F a ∈ V')
    (hVm' : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V'.nonunits)
    (hVj' : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V')
    (hne : V ≠ V')
    (y : ↥(TwoChartIntegralModel.XInf R F j)) (z : ↥(TwoChartIntegralModel R F j))
    (hy : (TwoChartIntegralModel.ιInf R F j).base y = z)
    (hreg : IsRegularLocalRing (↑((TwoChartIntegralModel R F j).presheaf.stalk z) ⧸ Ideal.span
      {((TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))}))
    (hV𝔭 : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) :
    ∃ b : ↥(TwoChartIntegralModel.chartAlgInf R F j), (b : F) ∈ V'.nonunits ∧ b ∉ y.asIdeal := by
  have hdom := isDomain_inf j y z hy ϖ hreg
  haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩
  have htj' : Transcendental R j⁻¹ := by
    intro h
    apply htj
    have h' : IsAlgebraic K₀ j⁻¹ := (IsFractionRing.isAlgebraic_iff R K₀ F).mp h
    exact (IsFractionRing.isAlgebraic_iff R K₀ F).mpr (IsAlgebraic.inv_iff.mp h')
  have hadj := adjoin_inv_eq (K := K₀) j
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hadj]; exact hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hadj]; exact hsep
  exact exists_mem_nonunits_and_not_mem R K₀ F j⁻¹ htj' hFD' hsep' ϖ hϖ V V' hVA hVm (branch_inv j V hVj)
    hVA' hVm' (branch_inv j V' hVj') hne y.asIdeal hdom hV𝔭

end E147B3

namespace E147B3

universe u

theorem offBranch_fin'
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (V V' : ValuationSubring F)
    (hVA : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits)
    (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
    (hVA' : ∀ a : R, algebraMap R F a ∈ V')
    (hVm' : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V'.nonunits)
    (hVj' : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V')
    (hne : V ≠ V')
    (P P' : F → Prop) (hP : ∀ f : F, f ∈ V.nonunits → P f) (hP' : ∀ f : F, f ∈ V'.nonunits → P' f)
    (y : ↥(TwoChartIntegralModel.XFin R F j)) (z : ↥(TwoChartIntegralModel R F j))
    (hy : (TwoChartIntegralModel.ιFin R F j).base y = z)
    (hreg : IsRegularLocalRing (↑((TwoChartIntegralModel R F j).presheaf.stalk z) ⧸ Ideal.span
      {((TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))}))
    (hV𝔭 : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin R F j), P (b : F) → b ∈ y.asIdeal) :
    ∃ b : ↥(TwoChartIntegralModel.chartAlgFin R F j), P' (b : F) ∧ b ∉ y.asIdeal := by
  obtain ⟨b, hb1, hb2⟩ := offBranch_fin R K₀ F j htj hFD hsep ϖ hϖ V V' hVA hVm hVj hVA' hVm' hVj' hne y z hy hreg
    (fun b hb => hV𝔭 b (hP _ hb))
  exact ⟨b, hP' _ hb1, hb2⟩

theorem offBranch_inf'
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (V V' : ValuationSubring F)
    (hVA : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits)
    (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
    (hVA' : ∀ a : R, algebraMap R F a ∈ V')
    (hVm' : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V'.nonunits)
    (hVj' : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V')
    (hne : V ≠ V')
    (P P' : F → Prop) (hP : ∀ f : F, f ∈ V.nonunits → P f) (hP' : ∀ f : F, f ∈ V'.nonunits → P' f)
    (y : ↥(TwoChartIntegralModel.XInf R F j)) (z : ↥(TwoChartIntegralModel R F j))
    (hy : (TwoChartIntegralModel.ιInf R F j).base y = z)
    (hreg : IsRegularLocalRing (↑((TwoChartIntegralModel R F j).presheaf.stalk z) ⧸ Ideal.span
      {((TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((TwoChartIntegralModel.toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))}))
    (hV𝔭 : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf R F j), P (b : F) → b ∈ y.asIdeal) :
    ∃ b : ↥(TwoChartIntegralModel.chartAlgInf R F j), P' (b : F) ∧ b ∉ y.asIdeal := by
  obtain ⟨b, hb1, hb2⟩ := offBranch_inf R K₀ F j htj hFD hsep ϖ hϖ V V' hVA hVm hVj hVA' hVm' hVj' hne y z hy hreg
    (fun b hb => hV𝔭 b (hP _ hb))
  exact ⟨b, hP' _ hb1, hb2⟩

end E147B3

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

    ∀ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))),
      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) →

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

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

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    let OffBranch : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      ∀ ℓ : CuspidalType.ProjLine q, ℓ ≠ lineInfty q →
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal) ∧
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal)

    ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x → OffBranch x := by
  intro F₀ hK1 hstab hLD hRAT instAlg hconst j₁ hj₁ instFact NIg hN
  intro InStalk InMax Centred GoodPt Reads OffBranch x hG
  obtain ⟨hGbase, hGclosed, hGFin, hGInf, hGord⟩ := hG
  have hqprime : q.Prime := Fact.out

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible ↥A₁
  have hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  have hreg := ModularCurve.FullLevel.isRegularLocalRing_stalk_quotient_span_of_goodPt_twoChartIntegralModel
    q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K₁ hK₁ A₁ hA₁ F₀ hK1 hstab hLD hRAT hconst j₁ hj₁ x ⟨hGbase, hGclosed, hGFin, hGInf, hGord⟩ ϖ hϖ _ rfl

  obtain ⟨hR1, hR2, hR3, hR4⟩ := ModularCurve.FullLevel.mem_igusaRing_coe_levelField_and_injective_twoChartIntegralModel
    q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K₁ hK₁ A₁ hA₁ F₀ hK1 hstab hLD hRAT hconst j₁ hj₁

  letI algK₁ : Algebra ↥K₁ ↥(E147B3.fieldOf j₁) :=
    (((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥K₁ (AlgebraicClosure ℚ))).codRestrict
      (E147B3.fieldOf j₁)
      (fun c => le_sup_left (α := IntermediateField ↥k₀ ↥(fieldBar q M'))
        (IntermediateField.subset_adjoin ↥k₀ _ ⟨(c : AlgebraicClosure ℚ), c.2, rfl⟩))).toAlgebra
  have hK₁T : ∀ c : ↥K₁, ((algebraMap ↥K₁ ↥(E147B3.fieldOf j₁) c : ↥(E147B3.fieldOf j₁)) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) := fun _ => rfl
  haveI ist : IsScalarTower ↥A₁ ↥K₁ ↥(E147B3.fieldOf j₁) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    apply Subtype.ext
    exact ((hK₁T _).trans (hconst a).symm).symm
  obtain ⟨htj, hFD⟩ := ModularCurve.FullLevel.transcendental_and_finiteDimensional_adjoin_levelField
    q M' k₀ K₁ hK₁ F₀ hK1 (hLD K₁ hK₁) hRAT hK₁T j₁ (by rw [hj₁]; rfl)
  have hinjA : Function.Injective (algebraMap ↥A₁ ↥K₁) := fun a b h => Subtype.ext h
  have htjA : Transcendental ↥A₁ j₁ := htj.restrictScalars hinjA
  haveI : CharZero ↥k₀ := charZero_of_injective_ringHom (algebraMap ℚ ↥k₀).injective
  haveI : CharZero ↥K₁ := charZero_of_injective_ringHom (algebraMap ↥k₀ ↥K₁).injective
  haveI : CharZero ↥(IntermediateField.adjoin ↥K₁ ({j₁} : Set ↥(E147B3.fieldOf j₁))) :=
    charZero_of_injective_ringHom (algebraMap ↥K₁ _).injective
  haveI := hFD
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ↥K₁ ({j₁} : Set ↥(E147B3.fieldOf j₁))) ↥(E147B3.fieldOf j₁) := inferInstance

  let V : CuspidalType.ProjLine q → ValuationSubring ↥(E147B3.fieldOf j₁) := fun l =>
    (OIg l).comap (algebraMap ↥(E147B3.fieldOf j₁) ↥(fieldBar q M'))
  have hVmem : ∀ (l : CuspidalType.ProjLine q) (f : ↥(E147B3.fieldOf j₁)), f ∈ V l ↔ (f : ↥(fieldBar q M')) ∈ OIg l :=
    fun _ _ => ValuationSubring.mem_comap
  have hVnu : ∀ (l : CuspidalType.ProjLine q) (f : ↥(E147B3.fieldOf j₁)), f ∈ (V l).nonunits ↔ (f : ↥(fieldBar q M')) ∈ (OIg l).nonunits :=
    fun l f => E147B3.mem_nonunits_comap_iff (OIg l) _ f
  have hVA : ∀ (l : CuspidalType.ProjLine q) (a : ↥A₁), algebraMap ↥A₁ ↥(E147B3.fieldOf j₁) a ∈ V l :=
    fun l a => (hVmem l _).mpr (hR1 l a)
  have hVm : ∀ (l : CuspidalType.ProjLine q), ∀ a ∈ maximalIdeal ↥A₁, algebraMap ↥A₁ ↥(E147B3.fieldOf j₁) a ∈ (V l).nonunits :=
    fun l a ha => (hVnu l _).mpr (hR2 l a ha)
  have hVj : ∀ (l : CuspidalType.ProjLine q) (P : Polynomial ↥A₁), P.map (IsLocalRing.residue ↥A₁) ≠ 0 →
      Polynomial.aeval j₁ P ∈ V l ∧ (Polynomial.aeval j₁ P)⁻¹ ∈ V l :=
    fun l P hP => ⟨(hVmem l _).mpr (hR3 l P hP).1, (hVmem l _).mpr (hR3 l P hP).2⟩
  have hVne : ∀ l : CuspidalType.ProjLine q, l ≠ lineInfty q → V (lineInfty q) ≠ V l := by
    intro l hl hEq
    apply hl
    refine (hR4 (lineInfty q) l (fun f => ?_)).symm
    rw [← hVmem, ← hVmem, hEq]

  intro l hl
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · exact E147B3.offBranch_fin' ↥A₁ ↥K₁ _ j₁ htjA hFD hsep ϖ hϖ (V (lineInfty q)) (V l)
      (hVA _) (hVm _) (hVj _) (hVA _) (hVm _) (hVj _) (hVne l hl)
      (fun f => (f : ↥(fieldBar q M')) ∈ R.integers.nonunits) (fun f => (f : ↥(fieldBar q M')) ∈ (OIg l).nonunits)
      (fun f hf => by rw [hR]; exact (hVnu (lineInfty q) f).mp hf) (fun f hf => (hVnu l f).mp hf)
      y x hy hreg (hGFin y hy)
  · exact E147B3.offBranch_inf' ↥A₁ ↥K₁ _ j₁ htjA hFD hsep ϖ hϖ (V (lineInfty q)) (V l)
      (hVA _) (hVm _) (hVj _) (hVA _) (hVm _) (hVj _) (hVne l hl)
      (fun f => (f : ↥(fieldBar q M')) ∈ R.integers.nonunits) (fun f => (f : ↥(fieldBar q M')) ∈ (OIg l).nonunits)
      (fun f hf => by rw [hR]; exact (hVnu (lineInfty q) f).mp hf) (fun f hf => (hVnu l f).mp hf)
      y x hy hreg (hGInf y hy)

end S_ModularCurve_FullLevel_offBranch_of_goodPt_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_offBranch_of_goodPt_twoChartIntegralModel (solution)
