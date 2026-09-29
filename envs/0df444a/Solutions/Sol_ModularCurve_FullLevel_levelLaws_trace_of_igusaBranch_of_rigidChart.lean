-- Prove2me | solution 1 for ModularCurve.FullLevel.levelLaws_trace_of_igusaBranch_of_rigidChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/6d1c8579-4f96-5c53-9d6a-f11d6ea62cb9

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff

import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ValuationSubring_forall_monic_aeval_not_mem_maximalIdeal_iff_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_mem_maximalIdeal_iff_residue_eq_zero_of_forall_aeval_jqNModC_mem
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd
import Theorems.Thm_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_levelLaws_trace_of_igusaBranch_of_rigidChart
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim"
p2m_attr_erase "instance" "ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst ModularCurve.CharPModel.FibreModel.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace S3C4Pernode

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section PartB

variable (G : Subgroup (K ≃ₐ[k] K))
  (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
  (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
  (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)

include hBG hBÕ hloc

theorem exists_invariant_fraction [Finite ↥G] (f : K) (hfÕ : f ∈ Õ) (hfG : ∀ σ : ↥G, σ • f = f) :
    ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ σ : ↥G, σ • g = g) ∧ (∀ σ : ↥G, σ • h = h) ∧
      (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g := by
  classical
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  have hBG' : ∀ (σ : ↥G) (b : K), b ∈ B → σ • b ∈ B := fun σ b hb => hBG σ σ.2 b hb

  let I : Ideal ↥B :=
    { carrier := {h | f * (h : K) ∈ B}
      add_mem' := fun {a b} ha hb => by
        change f * ((a : K) + b) ∈ B
        rw [mul_add]; exact B.add_mem ha hb
      zero_mem' := by change f * (0 : K) ∈ B; rw [mul_zero]; exact B.zero_mem
      smul_mem' := fun c {a} ha => by
        change f * ((c : K) * a) ∈ B
        rw [mul_left_comm]; exact B.mul_mem c.2 ha }
  have memI : ∀ h : ↥B, h ∈ I ↔ f * (h : K) ∈ B := fun _ => Iff.rfl

  let φ : ↥G → (↥B →+* ↥Õ) := fun σ =>
    { toFun := fun b => ⟨σ • (b : K), hBÕ (hBG' σ _ b.2)⟩
      map_one' := Subtype.ext (by change σ • ((1 : ↥B) : K) = 1; rw [OneMemClass.coe_one, smul_one])
      map_mul' := fun a b => Subtype.ext (by change σ • ((a : K) * b) = σ • (a : K) * σ • (b : K); rw [smul_mul'])
      map_zero' := Subtype.ext (by change σ • ((0 : ↥B) : K) = 0; rw [ZeroMemClass.coe_zero, smul_zero])
      map_add' := fun a b => Subtype.ext (by change σ • ((a : K) + b) = σ • (a : K) + σ • (b : K); rw [smul_add]) }
  let Q : ↥G → Ideal ↥B := fun σ => Ideal.comap (φ σ) (IsLocalRing.maximalIdeal ↥Õ)
  have hQprime : ∀ σ, (Q σ).IsPrime := fun σ => Ideal.comap_isPrime (φ σ) _
  have memQ : ∀ (σ : ↥G) (b : ↥B), b ∈ Q σ ↔ (⟨σ • (b : K), hBÕ (hBG' σ _ b.2)⟩ : ↥Õ) ∈ IsLocalRing.maximalIdeal ↥Õ :=
    fun _ _ => Iff.rfl

  obtain ⟨g₁, h₁, hg₁B, hh₁B, hh₁u, hfh₁⟩ := (hloc f).mp hfÕ
  have hnot : ∀ σ : ↥G, ¬ (I ≤ Q σ) := by
    intro σ hle
    have hmem : (⟨σ⁻¹ • h₁, hBG' _ _ hh₁B⟩ : ↥B) ∈ I := by
      rw [memI]
      change f * (σ⁻¹ • h₁) ∈ B
      have : f * (σ⁻¹ • h₁) = σ⁻¹ • (f * h₁) := by rw [smul_mul', hfG σ⁻¹]
      rw [this, hfh₁]; exact hBG' _ _ hg₁B
    have h2 := hle hmem
    rw [memQ] at h2
    apply (IsLocalRing.mem_maximalIdeal _).mp ?_ (hh₁u (hBÕ hh₁B))
    have e : (⟨σ • ((⟨σ⁻¹ • h₁, hBG' _ _ hh₁B⟩ : ↥B) : K), hBÕ (hBG' σ _ (hBG' _ _ hh₁B))⟩ : ↥Õ) = ⟨h₁, hBÕ hh₁B⟩ := by
      apply Subtype.ext; change σ • σ⁻¹ • h₁ = h₁; rw [smul_inv_smul]
    rw [← e]; exact h2

  have havoid : ¬ ((I : Set ↥B) ⊆ ⋃ σ ∈ (↑(Finset.univ : Finset ↥G) : Set ↥G), ((Q σ) : Set ↥B)) := by
    rw [Ideal.subset_union_prime (1 : ↥G) (1 : ↥G) (fun σ _ _ _ => hQprime σ)]
    rintro ⟨σ, -, hle⟩
    exact hnot σ hle
  rw [Set.not_subset] at havoid
  obtain ⟨h, hhI, hhQ⟩ := havoid
  have hhQ' : ∀ σ : ↥G, h ∉ Q σ := by
    intro σ hσ
    apply hhQ
    rw [Set.mem_iUnion₂]
    exact ⟨σ, Finset.mem_coe.mpr (Finset.mem_univ σ), hσ⟩
  have hfhB : f * (h : K) ∈ B := (memI h).mp hhI

  have hσhB : ∀ σ : ↥G, σ • (h : K) ∈ B := fun σ => hBG' σ _ h.2
  have hσhu : ∀ σ : ↥G, (⟨σ • (h : K), hBÕ (hσhB σ)⟩ : ↥Õ) ∉ IsLocalRing.maximalIdeal ↥Õ :=
    fun σ hσ => hhQ' σ ((memQ σ h).mpr hσ)
  set hp : K := ∏ σ : ↥G, σ • (h : K) with hhp
  have hp_B : hp ∈ B := Subring.prod_mem B (fun σ _ => hσhB σ)
  have hp_Õ : hp ∈ Õ := hBÕ hp_B
  have hpÕ_eq : ∀ hh : hp ∈ Õ, (⟨hp, hh⟩ : ↥Õ) = ∏ σ : ↥G, (⟨σ • (h : K), hBÕ (hσhB σ)⟩ : ↥Õ) := by
    intro hh
    apply Subtype.ext
    change hp = Õ.subtype (∏ σ : ↥G, (⟨σ • (h : K), hBÕ (hσhB σ)⟩ : ↥Õ))
    rw [map_prod, hhp]
    rfl
  have hp_unit : ∀ hh : hp ∈ Õ, IsUnit (⟨hp, hh⟩ : ↥Õ) := by
    intro hh
    rw [hpÕ_eq hh]
    apply Finset.prod_induction (p := fun x : ↥Õ => IsUnit x)
    · intro a b ha hb; exact ha.mul hb
    · exact isUnit_one
    · intro σ _
      have := hσhu σ
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at this
  have hpG : ∀ τ : ↥G, τ • hp = hp := by
    intro τ
    rw [hhp, Finset.smul_prod']
    simp_rw [smul_smul]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  have hg'B : f * hp ∈ B := by
    have : hp = (h : K) * ∏ σ ∈ (Finset.univ : Finset ↥G).erase 1, σ • (h : K) := by
      rw [hhp, ← Finset.mul_prod_erase (Finset.univ : Finset ↥G) (fun σ => σ • (h : K)) (Finset.mem_univ 1), one_smul]
    rw [this, ← mul_assoc]
    exact B.mul_mem hfhB (Subring.prod_mem B (fun σ _ => hσhB σ))
  refine ⟨f * hp, hp, hg'B, hp_B, fun σ => ?_, hpG, hp_unit, rfl⟩
  rw [smul_mul', hfG, hpG]

end PartB

theorem mem_iff_exists_frac_invariant
    (G : Subgroup (K ≃ₐ[k] K)) (hG : Finite ↥G)
    (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (BG : Subring K) (hBGdef : ∀ f : K, f ∈ BG ↔ f ∈ B ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f)
    (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
    (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)
    (O₀ : Subring K) (hO₀ : ∀ f : K, f ∈ O₀ ↔ f ∈ Õ ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) :
    BG ≤ O₀ ∧ (∀ f : ↥O₀, IsUnit f ↔ IsUnit (⟨(f : K), ((hO₀ f).mp f.2).1⟩ : ↥Õ)) ∧
    ∀ f : K, f ∈ O₀ ↔ ∃ g h : K, g ∈ BG ∧ h ∈ BG ∧ (∀ hh : h ∈ O₀, IsUnit (⟨h, hh⟩ : ↥O₀)) ∧ f * h = g := by
  classical
  haveI : Finite ↥G := hG
  have hle : O₀ ≤ Õ := fun f hf => ((hO₀ f).mp hf).1
  have hBGB : BG ≤ B := fun f hf => ((hBGdef f).mp hf).1
  have hBGO₀ : BG ≤ O₀ := fun f hf => (hO₀ f).mpr ⟨hBÕ (hBGB hf), ((hBGdef f).mp hf).2⟩

  have hunits : ∀ f : ↥O₀, IsUnit f ↔ IsUnit (⟨(f : K), hle f.2⟩ : ↥Õ) := by
    intro f
    constructor
    · intro h; exact h.map (Subring.inclusion hle)
    · intro h
      obtain ⟨u, hu⟩ := h
      set g : ↥Õ := ↑u⁻¹ with hg
      have hfg : (f : K) * (g : K) = 1 := by
        have := congrArg (fun z : ↥Õ => (z : K)) u.mul_inv
        rw [hu] at this
        simpa using this
      have hf0 : (f : K) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hfg; exact zero_ne_one hfg
      have hgeq : (g : K) = (f : K)⁻¹ := by
        calc (g : K) = (f : K)⁻¹ * ((f : K) * (g : K)) := by rw [← mul_assoc, inv_mul_cancel₀ hf0, one_mul]
          _ = (f : K)⁻¹ := by rw [hfg, mul_one]
      have hginv : ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ (g : K) = (g : K) := by
        intro σ hσ
        rw [hgeq, map_inv₀, ((hO₀ f).mp f.2).2 σ hσ]
      have hgO₀ : (g : K) ∈ O₀ := (hO₀ _).mpr ⟨g.2, hginv⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨(g : K), hgO₀⟩, Subtype.ext ?_⟩
      simpa using hfg
  refine ⟨hBGO₀, hunits, fun f => ?_⟩
  constructor
  · intro hf
    obtain ⟨g, h, hgB, hhB, hgG, hhG, hhu, e⟩ :=
      exists_invariant_fraction G B hBG Õ hBÕ hloc f (hle hf) (fun σ => ((hO₀ f).mp hf).2 σ σ.2)
    refine ⟨g, h, (hBGdef g).mpr ⟨hgB, fun σ hσ => hgG ⟨σ, hσ⟩⟩, (hBGdef h).mpr ⟨hhB, fun σ hσ => hhG ⟨σ, hσ⟩⟩,
      fun hh => (hunits ⟨h, hh⟩).mpr (hhu (hle hh)), e⟩
  · rintro ⟨g, h, hg, hh, hhu, e⟩
    obtain ⟨u, hu⟩ := hhu (hBGO₀ hh)
    have hinv : (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * h = 1 := by
      have := congrArg (fun z : ↥O₀ => (z : K)) u.inv_mul
      rw [hu] at this; exact this
    have : f = g * (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) := by
      calc f = f * ((((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * h) := by rw [hinv, mul_one]
        _ = (f * h) * (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) := by ring
        _ = g * (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) := by rw [e]
    rw [this]
    exact O₀.mul_mem (hBGO₀ hg) ((u⁻¹ : (↥O₀)ˣ) : ↥O₀).2

end S3C4Pernode

namespace S3C4Glue

open IsLocalRing Polynomial

@[reducible] noncomputable def traceNode {k₀ : Type} [Field k₀] {Kℓ : Type} [Field Kℓ] [Algebra k₀ Kℓ]
    (K₀ : IntermediateField k₀ Kℓ) (O : Subring Kℓ) : Subring ↥K₀ :=
  O.comap (algebraMap ↥K₀ Kℓ)

theorem mem_traceNode {k₀ : Type} [Field k₀] {Kℓ : Type} [Field Kℓ] [Algebra k₀ Kℓ]
    (K₀ : IntermediateField k₀ Kℓ) (O : Subring Kℓ) (f : ↥K₀) :
    f ∈ traceNode K₀ O ↔ (f : Kℓ) ∈ O := Iff.rfl

theorem isUnit_mk_iff {K : Type} [Field K] (O : Subring K) (x : K) (hx : x ∈ O) :
    IsUnit (⟨x, hx⟩ : ↥O) ↔ ∃ y : K, y ∈ O ∧ x * y = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨((u⁻¹ : (↥O)ˣ) : ↥O), ((u⁻¹ : (↥O)ˣ) : ↥O).2, ?_⟩
    have h := congrArg (fun z : ↥O => (z : K)) u.mul_inv
    rw [hu] at h
    simpa using h
  · rintro ⟨y, hy, hxy⟩
    exact IsUnit.of_mul_eq_one (b := (⟨y, hy⟩ : ↥O)) (Subtype.ext hxy)

theorem isUnit_trace_iff {k K : Type} [Field k] [Field K] [Algebra k K] (K₀ : IntermediateField k K)
    (O : Subring K) (f : ↥K₀) (hf : f ∈ traceNode K₀ O) :
    IsUnit (⟨f, hf⟩ : ↥(traceNode K₀ O)) ↔ IsUnit (⟨(f : K), hf⟩ : ↥O) := by
  rw [isUnit_mk_iff, isUnit_mk_iff]
  constructor
  · rintro ⟨y, hy, hfy⟩
    exact ⟨(y : K), hy, by exact_mod_cast congrArg (fun z : ↥K₀ => (z : K)) hfy⟩
  · rintro ⟨y, hy, hfy⟩
    have hf0 : (f : K) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hfy; exact zero_ne_one hfy
    have hyeq : y = (f : K)⁻¹ := (eq_inv_of_mul_eq_one_right hfy)
    have hyK₀ : y ∈ K₀ := by rw [hyeq]; exact K₀.inv_mem f.2
    refine ⟨⟨y, hyK₀⟩, hy, Subtype.ext ?_⟩
    simpa using hfy

theorem mem_maximalIdeal_iff_lt {K : Type} [Field K] (V : ValuationSubring K) (x : K) (hx : x ∈ V) :
    (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V ↔ V.valuation x < 1 :=
  V.valuation_lt_one_iff ⟨x, hx⟩

theorem exists_valuationSubring_extension {k K : Type} [Field k] [Field K] [Algebra k K]
    (K₀ : IntermediateField k K) (V₀ : ValuationSubring ↥K₀) :
    ∃ V : ValuationSubring K, (∀ f : ↥K₀, f ∈ V₀ ↔ (f : K) ∈ V) ∧
      (∀ (f : ↥K₀) (hf : f ∈ V₀) (hf' : (f : K) ∈ V),
        (⟨f, hf⟩ : ↥V₀) ∈ maximalIdeal ↥V₀ ↔ (⟨(f : K), hf'⟩ : ↥V) ∈ maximalIdeal ↥V) := by
  classical

  set A : Subring K := V₀.toSubring.map (algebraMap ↥K₀ K) with hA
  have hmemA : ∀ x : K, x ∈ A ↔ ∃ f : ↥K₀, f ∈ V₀ ∧ (f : K) = x := by
    intro x
    rw [hA, Subring.mem_map]
    simp only [ValuationSubring.mem_toSubring, IntermediateField.algebraMap_apply]

  set I : Ideal ↥A := Ideal.span {a : ↥A | ∃ (f : ↥K₀) (hf : f ∈ V₀), (⟨f, hf⟩ : ↥V₀) ∈ maximalIdeal ↥V₀ ∧ (f : K) = (a : K)} with hI

  have hinj : Function.Injective (algebraMap ↥K₀ K) := (algebraMap ↥K₀ K).injective
  let e : ↥V₀ →+* ↥A :=
    { toFun := fun f => ⟨((f : ↥K₀) : K), (hmemA _).mpr ⟨f, f.2, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have he : ∀ f : ↥V₀, ((e f : ↥A) : K) = ((f : ↥K₀) : K) := fun _ => rfl
  have hesurj : Function.Surjective e := by
    intro a
    have hob1 := (hmemA a).mp a.2
    obtain ⟨f, hf, hfa⟩ := hob1
    exact ⟨⟨f, hf⟩, Subtype.ext hfa⟩
  have heinj : Function.Injective e := by
    intro a b hab
    have h1 : ((a : ↥K₀) : K) = ((b : ↥K₀) : K) := by rw [← he, ← he, hab]
    exact Subtype.ext (Subtype.ext h1)

  have hIle : I ≤ (maximalIdeal ↥V₀).map e := by
    rw [hI, Ideal.span_le]
    rintro a ⟨f, hf, hm, hfa⟩
    have : a = e ⟨f, hf⟩ := Subtype.ext (by rw [he]; exact hfa.symm)
    rw [this]
    exact Ideal.mem_map_of_mem _ hm
  have hItop : I ≠ ⊤ := by
    intro htop
    have h1 : (maximalIdeal ↥V₀).map e = ⊤ := top_le_iff.mp (htop ▸ hIle)
    have h2 : (1 : ↥A) ∈ (maximalIdeal ↥V₀).map e := h1 ▸ Submodule.mem_top
    rw [Ideal.mem_map_iff_of_surjective e hesurj] at h2
    obtain ⟨x, hx, hx1⟩ := h2
    have : x = 1 := heinj (by rw [hx1, map_one])
    rw [this] at hx
    exact (maximalIdeal.isMaximal ↥V₀).ne_top (Ideal.eq_top_of_isUnit_mem _ hx isUnit_one)
  have hob2 := Ideal.image_subset_nonunits_valuationSubring I hItop
  obtain ⟨V, hAV, hIV⟩ := hob2

  have hsub : ∀ f : ↥K₀, f ∈ V₀ → (f : K) ∈ V := fun f hf => hAV ((hmemA _).mpr ⟨f, hf, rfl⟩)
  have hmax : ∀ (f : ↥K₀) (hf : f ∈ V₀), (⟨f, hf⟩ : ↥V₀) ∈ maximalIdeal ↥V₀ → V.valuation (f : K) < 1 := by
    intro f hf hm
    have ha : (⟨(f : K), (hmemA _).mpr ⟨f, hf, rfl⟩⟩ : ↥A) ∈ I := by
      rw [hI]
      exact Ideal.subset_span ⟨f, hf, hm, rfl⟩
    have := hIV ⟨_, ha, rfl⟩
    exact (V.mem_nonunits_iff).mp this
  refine ⟨V, ?_, ?_⟩
  · intro f
    refine ⟨hsub f, fun hfV => ?_⟩

    by_contra hf
    have hf0 : f ≠ 0 := fun h0 => hf (h0 ▸ V₀.zero_mem)
    have hinv : f⁻¹ ∈ V₀ := by
      rcases V₀.mem_or_inv_mem f with h | h
      · exact (hf h).elim
      · exact h
    have hinvm : (⟨f⁻¹, hinv⟩ : ↥V₀) ∈ maximalIdeal ↥V₀ := by
      rw [mem_maximalIdeal_iff_lt]
      rcases V₀.valuation_lt_one_or_eq_one ⟨f⁻¹, hinv⟩ with h | h
      · exact h
      · exfalso
        apply hf
        have hu : IsUnit (⟨f⁻¹, hinv⟩ : ↥V₀) := (V₀.valuation_eq_one_iff _).mpr h
        obtain ⟨y, hy, hy1⟩ : ∃ y : ↥K₀, y ∈ V₀ ∧ f⁻¹ * y = 1 := by
          obtain ⟨u, hu⟩ := hu
          refine ⟨((u⁻¹ : (↥V₀)ˣ) : ↥V₀), ((u⁻¹ : (↥V₀)ˣ) : ↥V₀).2, ?_⟩
          have h := congrArg (fun z : ↥V₀ => (z : ↥K₀)) u.mul_inv
          rw [hu] at h
          simpa using h
        have : y = f := by
          have := eq_inv_of_mul_eq_one_right hy1
          rw [this, inv_inv]
        exact this ▸ hy
    have h1 := hmax _ hinv hinvm
    have h2 : V.valuation (f : K) ≤ 1 := (V.valuation_le_one_iff _).mpr hfV
    have h3 : V.valuation ((f⁻¹ : ↥K₀) : K) * V.valuation ((f : ↥K₀) : K) = 1 := by
      rw [← map_mul, ← Subsemiring.coe_mul]
      push_cast
      rw [inv_mul_cancel₀ (by exact_mod_cast hf0 : ((f : ↥K₀) : K) ≠ 0), map_one]
    have h4 : V.valuation ((f⁻¹ : ↥K₀) : K) * V.valuation ((f : ↥K₀) : K) < 1 :=
      mul_lt_one_of_lt_of_le h1 h2
    rw [h3] at h4
    exact lt_irrefl _ h4
  · intro f hf hf'
    constructor
    · intro hm
      rw [mem_maximalIdeal_iff_lt]
      exact hmax f hf hm
    · intro hm

      rw [mem_maximalIdeal_iff_lt] at hm
      by_contra hnm
      have hu : IsUnit (⟨f, hf⟩ : ↥V₀) := by
        rcases V₀.valuation_lt_one_or_eq_one ⟨f, hf⟩ with h | h
        · exact (hnm ((mem_maximalIdeal_iff_lt V₀ f hf).mpr h)).elim
        · exact (V₀.valuation_eq_one_iff _).mpr h
      obtain ⟨u, hu⟩ := hu
      have hinv : (((u⁻¹ : (↥V₀)ˣ) : ↥V₀) : ↥K₀) ∈ V₀ := ((u⁻¹ : (↥V₀)ˣ) : ↥V₀).2
      have hK : (f : K) * ((((u⁻¹ : (↥V₀)ˣ) : ↥V₀) : ↥K₀) : K) = 1 := by
        have h := congrArg (fun z : ↥V₀ => ((z : ↥K₀) : K)) u.mul_inv
        rw [hu] at h
        simpa using h
      have hv1 : V.valuation ((((u⁻¹ : (↥V₀)ˣ) : ↥V₀) : ↥K₀) : K) ≤ 1 :=
        (V.valuation_le_one_iff _).mpr (hsub _ hinv)
      have := mul_lt_one_of_lt_of_le hm hv1
      rw [← map_mul, hK, map_one] at this
      exact lt_irrefl _ this

theorem mem_maximalIdeal_comap_algEquiv_iff {k K : Type} [Field k] [Field K] [Algebra k K]
    (τ : K ≃ₐ[k] K) (V : ValuationSubring K) (x : K) (hx : x ∈ V.comap (τ : K →+* K)) (hx' : τ x ∈ V) :
    (⟨x, hx⟩ : ↥(V.comap (τ : K →+* K))) ∈ maximalIdeal ↥(V.comap (τ : K →+* K)) ↔
      (⟨τ x, hx'⟩ : ↥V) ∈ maximalIdeal ↥V := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  have key : ∀ (y : K) (hy : y ∈ V.comap (τ : K →+* K)) (hy' : τ y ∈ V),
      IsUnit (⟨y, hy⟩ : ↥(V.comap (τ : K →+* K))) ↔ ∃ z : K, τ z ∈ V ∧ y * z = 1 := by
    intro y hy hy'
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨((u⁻¹ : (↥(V.comap (τ : K →+* K)))ˣ) : ↥(V.comap (τ : K →+* K))), ?_, ?_⟩
      · exact ((u⁻¹ : (↥(V.comap (τ : K →+* K)))ˣ) : ↥(V.comap (τ : K →+* K))).2
      · have h := congrArg (fun z : ↥(V.comap (τ : K →+* K)) => (z : K)) u.mul_inv
        rw [hu] at h
        simpa using h
    · rintro ⟨z, hz, hyz⟩
      exact IsUnit.of_mul_eq_one (b := (⟨z, hz⟩ : ↥(V.comap (τ : K →+* K)))) (Subtype.ext hyz)
  rw [key x hx hx']
  constructor
  · rintro ⟨z, hz, hxz⟩
    exact IsUnit.of_mul_eq_one (b := (⟨τ z, hz⟩ : ↥V)) (Subtype.ext (by
      show τ x * τ z = 1
      rw [← map_mul, hxz, map_one]))
  · rintro ⟨u, hu⟩
    refine ⟨τ.symm (((u⁻¹ : (↥V)ˣ) : ↥V) : K), ?_, ?_⟩
    · show τ (τ.symm _) ∈ V
      rw [AlgEquiv.apply_symm_apply]
      exact ((u⁻¹ : (↥V)ˣ) : ↥V).2
    · apply τ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_one]
      have h := congrArg (fun z : ↥V => (z : K)) u.mul_inv
      rw [hu] at h
      simpa using h

theorem mem_valuationSubring_of_isIntegral {K : Type} [Field K] {R : Type} [CommRing R] [Algebra R K]
    (V : ValuationSubring K) (S : Set K) (hS : ∀ s : K, s ∈ S → s ∈ V) (hR : ∀ r : R, algebraMap R K r ∈ V)
    (x : K) (hx : IsIntegral ↥(Algebra.adjoin R S) x) : x ∈ V := by
  have hle : ∀ z : K, z ∈ Algebra.adjoin R S → z ∈ V := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz => exact hS z hz
    | algebraMap r => exact hR r
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  have hT : ∀ z : K, z ∈ V.valuation.integer ↔ z ∈ V := by
    intro z
    rw [ValuationSubring.integer_valuation]
    exact V.mem_toSubring z
  let φ : ↥(Algebra.adjoin R S) →+* ↥(V.valuation.integer) :=
    { toFun := fun z => ⟨(z : K), (hT _).mpr (hle z z.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hx' : IsIntegral ↥(V.valuation.integer) x :=
    IsIntegral.map_of_comp_eq (R := ↥(Algebra.adjoin R S)) (S := K) (T := ↥(V.valuation.integer)) (U := K)
      φ (RingHom.id K) (by ext z; rfl) hx
  exact (hT x).mp ((Valuation.integer.integers V.valuation).mem_of_integral hx')

theorem isIntegral_adjoin_singleton_trans {K R : Type} [Field K] [CommRing R] [Algebra R K] (x j z : K)
    (hj : IsIntegral ↥(Algebra.adjoin R ({x} : Set K)) j)
    (hz : IsIntegral ↥(Algebra.adjoin R ({j} : Set K)) z) :
    IsIntegral ↥(Algebra.adjoin R ({x} : Set K)) z := by
  let A₁ : Subalgebra ↥(Algebra.adjoin R ({x} : Set K)) K :=
    Algebra.adjoin ↥(Algebra.adjoin R ({x} : Set K)) ({j} : Set K)
  haveI : Algebra.IsIntegral ↥(Algebra.adjoin R ({x} : Set K)) ↥A₁ :=
    Algebra.IsIntegral.adjoin (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hj)
  have hle : ∀ y : K, y ∈ Algebra.adjoin R ({j} : Set K) → y ∈ A₁ := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap r =>
      have h := A₁.algebraMap_mem (algebraMap R ↥(Algebra.adjoin R ({x} : Set K)) r)
      rwa [← IsScalarTower.algebraMap_apply] at h
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  let φ : ↥(Algebra.adjoin R ({j} : Set K)) →+* ↥A₁ :=
    { toFun := fun y => ⟨(y : K), hle y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hz' : IsIntegral ↥A₁ z :=
    IsIntegral.map_of_comp_eq (R := ↥(Algebra.adjoin R ({j} : Set K))) (S := K) (T := ↥A₁) (U := K)
      φ (RingHom.id K) (by ext y; rfl) hz
  exact isIntegral_trans (R := ↥(Algebra.adjoin R ({x} : Set K))) (A := ↥A₁) z hz'

theorem isMaximal_of_mem_of_isIntegral {K R : Type} [Field K] [CommRing R] [IsLocalRing R] [Algebra R K]
    (π : R) (hπ : maximalIdeal R = Ideal.span {π})
    (C : Subalgebra R K) (x : K) (hxC : x ∈ C)
    (hint : ∀ z : K, z ∈ C → IsIntegral ↥(Algebra.adjoin R ({x} : Set K)) z)
    (Q : Ideal ↥C) [hQ : Q.IsPrime] (hπQ : algebraMap R ↥C π ∈ Q)
    (c : R) (hcQ : (⟨x, hxC⟩ : ↥C) - algebraMap R ↥C c ∈ Q) : Q.IsMaximal := by
  classical
  have hDC : Algebra.adjoin R ({x} : Set K) ≤ C := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxC)
  let f : ↥(Algebra.adjoin R ({x} : Set K)) →+* ↥C := (Subalgebra.inclusion hDC).toRingHom
  have hfcoe : ∀ z : ↥(Algebra.adjoin R ({x} : Set K)), ((f z : ↥C) : K) = (z : K) := fun _ => rfl
  have hfalg : ∀ r : R, f (algebraMap R _ r) = algebraMap R ↥C r := fun r => (Subalgebra.inclusion hDC).commutes r

  have hf : f.IsIntegral := by
    intro z
    have hob3 := hint (z : K) z.2
    obtain ⟨p, hp, hpz⟩ := hob3
    refine ⟨p, hp, ?_⟩
    apply Subtype.ext
    have h1 := Polynomial.hom_eval₂ p f (algebraMap ↥C K) z
    have h2 : (algebraMap ↥C K).comp f = algebraMap ↥(Algebra.adjoin R ({x} : Set K)) K := RingHom.ext fun _ => rfl
    rw [h2] at h1
    change (algebraMap ↥C K) (Polynomial.eval₂ f z p) = ((0 : ↥C) : K)
    rw [h1]
    simpa using hpz

  set 𝔫 : Ideal ↥(Algebra.adjoin R ({x} : Set K)) := Q.comap f with h𝔫
  have hπ𝔫 : algebraMap R _ π ∈ 𝔫 := by
    rw [h𝔫, Ideal.mem_comap, hfalg]; exact hπQ
  have hx𝔫 : (⟨x, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin R ({x} : Set K))) - algebraMap R _ c ∈ 𝔫 := by
    rw [h𝔫, Ideal.mem_comap, map_sub, hfalg]
    exact hcQ
  have hred : ∀ (y : K) (hy : y ∈ Algebra.adjoin R ({x} : Set K)),
      ∃ r : R, (⟨y, hy⟩ : ↥(Algebra.adjoin R ({x} : Set K))) - algebraMap R _ r ∈ 𝔫 := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      refine ⟨c, ?_⟩
      have : y = x := Set.mem_singleton_iff.mp hy
      subst this
      exact hx𝔫
    | algebraMap r => exact ⟨r, by rw [show (⟨algebraMap R K r, _⟩ : ↥(Algebra.adjoin R ({x} : Set K))) = algebraMap R _ r from Subtype.ext rfl, sub_self]; exact 𝔫.zero_mem⟩
    | add y z hy hz ihy ihz =>
      obtain ⟨r, hr⟩ := ihy
      obtain ⟨s, hs⟩ := ihz
      refine ⟨r + s, ?_⟩
      have : (⟨y + z, add_mem hy hz⟩ : ↥(Algebra.adjoin R ({x} : Set K))) - algebraMap R _ (r + s) =
          ((⟨y, hy⟩ : ↥(Algebra.adjoin R ({x} : Set K))) - algebraMap R _ r) + ((⟨z, hz⟩ : ↥(Algebra.adjoin R ({x} : Set K))) - algebraMap R _ s) := by
        rw [map_add]; apply Subtype.ext; simp only [Subalgebra.coe_add, Subalgebra.coe_sub]; ring
      rw [this]
      exact 𝔫.add_mem hr hs
    | mul y z hy hz ihy ihz =>
      obtain ⟨r, hr⟩ := ihy
      obtain ⟨s, hs⟩ := ihz
      refine ⟨r * s, ?_⟩
      have : (⟨y * z, mul_mem hy hz⟩ : ↥(Algebra.adjoin R ({x} : Set K))) - algebraMap R _ (r * s) =
          (⟨y, hy⟩ : ↥(Algebra.adjoin R ({x} : Set K))) * ((⟨z, hz⟩ : ↥(Algebra.adjoin R ({x} : Set K))) - algebraMap R _ s) +
          ((⟨y, hy⟩ : ↥(Algebra.adjoin R ({x} : Set K))) - algebraMap R _ r) * algebraMap R _ s := by
        rw [map_mul]; apply Subtype.ext; simp only [Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_mul]; ring
      rw [this]
      exact 𝔫.add_mem (𝔫.mul_mem_left _ hs) (𝔫.mul_mem_right _ hr)
  haveI : 𝔫.IsPrime := by rw [h𝔫]; exact Ideal.comap_isPrime f Q
  have h𝔫max : 𝔫.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one), ?_⟩
    intro J y hJ hy𝔫 hyJ
    have hob4 := hred (y : K) y.2
    obtain ⟨r, hr⟩ := hob4
    have hy : (⟨(y : K), y.2⟩ : ↥(Algebra.adjoin R ({x} : Set K))) = y := Subtype.ext rfl
    rw [hy] at hr

    have hru : IsUnit r := by
      by_contra hru
      apply hy𝔫
      have hrm : r ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hru
      rw [hπ, Ideal.mem_span_singleton] at hrm
      obtain ⟨a, ha⟩ := hrm
      have hra : algebraMap R (↥(Algebra.adjoin R ({x} : Set K))) r ∈ 𝔫 := by
        rw [ha, map_mul]
        exact 𝔫.mul_mem_right _ hπ𝔫
      have : y = (y - algebraMap R _ r) + algebraMap R _ r := by ring
      rw [this]
      exact 𝔫.add_mem hr hra

    have hrJ : algebraMap R (↥(Algebra.adjoin R ({x} : Set K))) r ∈ J := by
      have : algebraMap R (↥(Algebra.adjoin R ({x} : Set K))) r = y - (y - algebraMap R _ r) := by ring
      rw [this]
      exact J.sub_mem hyJ (hJ hr)
    exact J.eq_top_of_isUnit_mem hrJ (hru.map _) ▸ Submodule.mem_top
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf Q (by rw [← h𝔫]; exact h𝔫max)

noncomputable def toVal {K R : Type} [Field K] [CommRing R] [Algebra R K] (C : Subalgebra R K)
    (V : ValuationSubring K) (hCV : ∀ b : ↥C, (b : K) ∈ V) : ↥C →+* ↥V where
  toFun b := ⟨(b : K), hCV b⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem toVal_apply {K R : Type} [Field K] [CommRing R] [Algebra R K] (C : Subalgebra R K)
    (V : ValuationSubring K) (hCV : ∀ b : ↥C, (b : K) ∈ V) (b : ↥C) :
    toVal C V hCV b = ⟨(b : K), hCV b⟩ := rfl

theorem mk_mem_maximalIdeal_congr {K : Type} [Field K] (V : ValuationSubring K) (x y : K) (h : x = y)
    (hx : x ∈ V) (hy : y ∈ V) :
    (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V ↔ (⟨y, hy⟩ : ↥V) ∈ maximalIdeal ↥V := by
  subst h; exact Iff.rfl

theorem cover_case {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra R k] [Algebra R K] [IsScalarTower R k K]
    (hRk : Function.Injective (algebraMap R k))
    (π : R) (hπ : maximalIdeal R = Ideal.span {π})
    (G : Subgroup (K ≃ₐ[k] K)) (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (C : Subalgebra R K)
    (y : Ideal ↥C)
    (B B₀ : Subalgebra R K) (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ B ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    [DecidableEq (Subring ↥K₀)] (ends : Finset (Subring K))
    (h79 : ∀ V : ValuationSubring K, (∀ x : k, algebraMap k K x ∈ V ↔ ∃ a : R, algebraMap R k a = x) →
      (∀ b : ↥C, (b : K) ∈ V) →
      (∀ b : ↥C, b ∈ y → ∀ hb : (b : K) ∈ V, (⟨(b : K), hb⟩ : ↥V) ∈ maximalIdeal ↥V) →
      (∀ f : K, f ∈ B → f ∈ V) ∨
      (∃ O ∈ ends, ∀ (f : K) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V)))
    (OverS : Ideal ↥C → Prop)
    (hOrbit : ∀ y' : Ideal ↥C, y'.IsMaximal → algebraMap R ↥C π ∈ y' → OverS y' →
      ∃ τ : K ≃ₐ[k] K, τ ∈ G ∧ (∀ f : K, f ∈ C → τ f ∈ C) ∧
        ∀ (f : K) (hf : f ∈ C) (hf' : τ f ∈ C), (⟨f, hf⟩ : ↥C) ∈ y ↔ (⟨τ f, hf'⟩ : ↥C) ∈ y')
    (V₀ : ValuationSubring ↥K₀)
    (hconst : ∀ x : k, (∃ a : R, algebraMap R k a = x) ↔ algebraMap k ↥K₀ x ∈ V₀)
    (jsharp : K) (hjC : jsharp ∈ C) (hjK₀ : jsharp ∈ K₀) (hjV : (⟨jsharp, hjK₀⟩ : ↥K₀) ∈ V₀)
    (c : k) (hc : ∃ a : R, algebraMap R k a = c)
    (hjc : ∃ hm : (⟨jsharp, hjK₀⟩ : ↥K₀) - algebraMap k ↥K₀ c ∈ V₀, (⟨_, hm⟩ : ↥V₀) ∈ maximalIdeal ↥V₀)
    (hint : ∀ z : K, z ∈ C → IsIntegral ↥(Algebra.adjoin R ({jsharp} : Set K)) z)
    (hOverS : ∀ (V₁ : ValuationSubring K) (hCV : ∀ b : ↥C, (b : K) ∈ V₁),
      (∀ f : ↥K₀, f ∈ V₀ ↔ (f : K) ∈ V₁) →
      (∀ (f : ↥K₀) (hf : f ∈ V₀) (hf' : (f : K) ∈ V₁),
        (⟨f, hf⟩ : ↥V₀) ∈ maximalIdeal ↥V₀ ↔ (⟨(f : K), hf'⟩ : ↥V₁) ∈ maximalIdeal ↥V₁) →
      OverS ((maximalIdeal ↥V₁).comap (toVal C V₁ hCV))) :
    (∀ f : K, f ∈ B₀ → ∃ hf : f ∈ K₀, (⟨f, hf⟩ : ↥K₀) ∈ V₀) ∨
    (∃ O ∈ ends.image (traceNode K₀), ∀ (f : ↥K₀) (hfO : f ∈ O), f ∈ V₀ ∧
      (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V₀, (⟨f, hfV⟩ : ↥V₀) ∈ maximalIdeal ↥V₀)) := by
  classical

  have hfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ K₀ → σ f = f := by
    intro σ hσ f hf
    rw [hK₀, IntermediateField.mem_fixedField_iff] at hf
    exact hf σ hσ
  have hcoeK₀ : ∀ x : k, ((algebraMap k ↥K₀ x : ↥K₀) : K) = algebraMap k K x := fun _ => rfl

  have hob5 := exists_valuationSubring_extension K₀ V₀
  obtain ⟨V₁, htr, htrm⟩ := hob5

  have hkV₁ : ∀ x : k, algebraMap k K x ∈ V₁ ↔ ∃ a : R, algebraMap R k a = x := by
    intro x
    rw [hconst, htr, hcoeK₀]
  have hRV₁ : ∀ r : R, algebraMap R K r ∈ V₁ := by
    intro r
    rw [IsScalarTower.algebraMap_apply R k K, hkV₁]
    exact ⟨r, rfl⟩

  have hjV₁ : jsharp ∈ V₁ := (htr ⟨jsharp, hjK₀⟩).mp hjV
  have hCV₁ : ∀ b : ↥C, (b : K) ∈ V₁ := fun b =>
    mem_valuationSubring_of_isIntegral V₁ ({jsharp} : Set K) (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact hjV₁)
      hRV₁ (b : K) (hint (b : K) b.2)

  haveI hprime : ((maximalIdeal ↥V₁).comap (toVal C V₁ hCV₁)).IsPrime := Ideal.comap_isPrime _ _

  have hπk : algebraMap k K (algebraMap R k π) ∈ V₁ := (hkV₁ _).mpr ⟨π, rfl⟩
  have hπm : (⟨algebraMap R K π, hRV₁ π⟩ : ↥V₁) ∈ maximalIdeal ↥V₁ := by
    by_contra hu
    have hu' : IsUnit (⟨algebraMap R K π, hRV₁ π⟩ : ↥V₁) := by
      by_contra h; exact hu ((IsLocalRing.mem_maximalIdeal _).mpr h)

    have hπmax : π ∈ maximalIdeal R := by rw [hπ]; exact Ideal.mem_span_singleton_self π
    apply (IsLocalRing.mem_maximalIdeal π).mp hπmax
    by_cases hπ0 : algebraMap R k π = 0
    · exfalso
      have : (⟨algebraMap R K π, hRV₁ π⟩ : ↥V₁) = 0 := by
        apply Subtype.ext
        show algebraMap R K π = 0
        rw [IsScalarTower.algebraMap_apply R k K, hπ0, map_zero]
      rw [this] at hu'
      exact not_isUnit_zero hu'
    · obtain ⟨u, hu⟩ := hu'
      have hinvV : ((((u⁻¹ : (↥V₁)ˣ) : ↥V₁)) : K) ∈ V₁ := ((u⁻¹ : (↥V₁)ˣ) : ↥V₁).2
      have hprod : algebraMap R K π * ((((u⁻¹ : (↥V₁)ˣ) : ↥V₁)) : K) = 1 := by
        have h := congrArg (fun z : ↥V₁ => (z : K)) u.mul_inv
        rw [hu] at h
        simpa using h
      have hinv_eq : ((((u⁻¹ : (↥V₁)ˣ) : ↥V₁)) : K) = algebraMap k K (algebraMap R k π)⁻¹ := by
        rw [map_inv₀, ← IsScalarTower.algebraMap_apply R k K]
        exact (eq_inv_of_mul_eq_one_right hprod)
      have hmem : algebraMap k K (algebraMap R k π)⁻¹ ∈ V₁ := hinv_eq ▸ hinvV
      have hob6 := (hkV₁ _).mp hmem
      obtain ⟨a, ha⟩ := hob6
      have : algebraMap R k (π * a) = 1 := by
        rw [map_mul, ha, mul_inv_cancel₀ hπ0]
      have h1 : π * a = 1 := hRk (by rw [this, map_one])
      exact IsUnit.of_mul_eq_one (b := a) h1
  have hπ𝔮 : algebraMap R ↥C π ∈ (maximalIdeal ↥V₁).comap (toVal C V₁ hCV₁) := by
    rw [Ideal.mem_comap, toVal_apply]
    have : (⟨((algebraMap R ↥C π : ↥C) : K), hCV₁ _⟩ : ↥V₁) = ⟨algebraMap R K π, hRV₁ π⟩ :=
      Subtype.ext rfl
    rw [this]
    exact hπm

  obtain ⟨a, ha⟩ := hc
  obtain ⟨hm0, hm⟩ := hjc
  have hjc𝔮 : (⟨jsharp, hjC⟩ : ↥C) - algebraMap R ↥C a ∈ (maximalIdeal ↥V₁).comap (toVal C V₁ hCV₁) := by
    rw [Ideal.mem_comap, toVal_apply]
    have h1 := (htrm _ hm0 ((htr _).mp hm0)).mp hm
    have heq : (((⟨jsharp, hjK₀⟩ : ↥K₀) - algebraMap k ↥K₀ c : ↥K₀) : K) =
        (((⟨jsharp, hjC⟩ : ↥C) - algebraMap R ↥C a : ↥C) : K) := by
      have e1 : (((⟨jsharp, hjK₀⟩ : ↥K₀) - algebraMap k ↥K₀ c : ↥K₀) : K) = jsharp - algebraMap k K c := rfl
      have e2 : (((⟨jsharp, hjC⟩ : ↥C) - algebraMap R ↥C a : ↥C) : K) = jsharp - algebraMap R K a := rfl
      rw [e1, e2, IsScalarTower.algebraMap_apply R k K a, ha]
    exact (mk_mem_maximalIdeal_congr V₁ _ _ heq _ _).mp h1

  have hmax : ((maximalIdeal ↥V₁).comap (toVal C V₁ hCV₁)).IsMaximal :=
    isMaximal_of_mem_of_isIntegral π hπ C jsharp hjC hint _ hπ𝔮 a hjc𝔮
  have hob7 := hOrbit _ hmax hπ𝔮 (hOverS V₁ hCV₁ htr htrm)
  obtain ⟨τ, hτG, hτC, hτy⟩ := hob7

  set W : ValuationSubring K := V₁.comap (τ : K →+* K) with hW
  have hmemW : ∀ f : K, f ∈ W ↔ τ f ∈ V₁ := fun f => ValuationSubring.mem_comap

  have hWk : ∀ x : k, algebraMap k K x ∈ W ↔ ∃ a : R, algebraMap R k a = x := by
    intro x
    rw [hmemW, AlgEquiv.commutes, hkV₁]
  have hWC : ∀ b : ↥C, (b : K) ∈ W := fun b => (hmemW _).mpr (hCV₁ ⟨τ b, hτC _ b.2⟩)
  have hWy : ∀ b : ↥C, b ∈ y → ∀ hb : (b : K) ∈ W, (⟨(b : K), hb⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro b hb hbW
    have h1 : (⟨τ (b : K), hτC _ b.2⟩ : ↥C) ∈ (maximalIdeal ↥V₁).comap (toVal C V₁ hCV₁) := by
      rw [← hτy (b : K) b.2 (hτC _ b.2)]
      simpa using hb
    rw [Ideal.mem_comap, toVal_apply] at h1
    exact (mem_maximalIdeal_comap_algEquiv_iff τ V₁ (b : K) hbW (hCV₁ ⟨τ b, hτC _ b.2⟩)).mpr h1
  rcases h79 W hWk hWC hWy with hBW | ⟨O, hO, hdom⟩
  ·
    left
    intro f hf
    have hob8 := (hB₀ f).mp hf
    obtain ⟨hfB, hfG⟩ := hob8
    have hfK₀ : f ∈ K₀ := by
      rw [hK₀, IntermediateField.mem_fixedField_iff]
      exact hfG
    refine ⟨hfK₀, (htr ⟨f, hfK₀⟩).mpr ?_⟩
    have h1 := (hmemW f).mp (hBW f hfB)
    rwa [hfG τ hτG] at h1
  ·
    right
    refine ⟨traceNode K₀ O, Finset.mem_image_of_mem _ hO, ?_⟩
    intro f hfO
    rw [mem_traceNode] at hfO
    have hob9 := hdom (f : K) hfO
    obtain ⟨hfW, hfm⟩ := hob9
    have hτf : τ (f : K) = (f : K) := hfix τ hτG (f : K) f.2
    have hfV₁ : (f : K) ∈ V₁ := by
      have h1 := (hmemW _).mp hfW
      rwa [hτf] at h1
    refine ⟨(htr f).mpr hfV₁, ?_⟩
    intro hnu hfV
    have hnu' : ¬ IsUnit (⟨(f : K), hfO⟩ : ↥O) := by
      intro hu; apply hnu
      exact (isUnit_trace_iff K₀ O f hfO).mpr hu
    have h2 := hfm hnu' hfW
    have h3 := (mem_maximalIdeal_comap_algEquiv_iff τ V₁ (f : K) hfW ((hmemW _).mp hfW)).mp h2
    have h4 := (mk_mem_maximalIdeal_congr V₁ _ _ hτf _ hfV₁).mp h3
    exact (htrm f hfV hfV₁).mpr h4

theorem trans_case {k K : Type} [Field k] [Field K] [Algebra k K] (K₀ : IntermediateField k K)
    [DecidableEq (Subring ↥K₀)] (ends : Finset (Subring K)) {Γ : Type} [Group Γ] (S : Subgroup Γ)
    (Att : Γ → (K ≃ₐ[k] K) → Prop) (PW : (K ≃ₐ[k] K) → Prop)
    (h75 : ∀ O ∈ ends, ∀ O' ∈ ends, ∃ (γ : Γ) (_ : γ ∈ S) (τ : K ≃ₐ[k] K) (_ : Att γ τ),
      PW τ ∧ ∀ f : K, f ∈ O ↔ τ f ∈ O') :
    ∀ O ∈ ends.image (traceNode K₀), ∀ O' ∈ ends.image (traceNode K₀),
      ∃ (γ : Γ) (_ : γ ∈ S) (τ : K ≃ₐ[k] K) (_ : Att γ τ),
        ∀ (f : K) (hf : f ∈ K₀) (hf' : τ f ∈ K₀), (⟨f, hf⟩ : ↥K₀) ∈ O ↔ (⟨_, hf'⟩ : ↥K₀) ∈ O' := by
  classical
  intro O hO O' hO'
  have hob10 := Finset.mem_image.mp hO
  obtain ⟨U, hU, rfl⟩ := hob10
  have hob11 := Finset.mem_image.mp hO'
  obtain ⟨U', hU', rfl⟩ := hob11
  have hob12 := h75 U hU U' hU'
  obtain ⟨γ, hγ, τ, hτ, -, hiff⟩ := hob12
  refine ⟨γ, hγ, τ, hτ, ?_⟩
  intro f hf hf'
  rw [mem_traceNode, mem_traceNode]
  exact hiff f

noncomputable def restrictTo {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (B : Subalgebra R K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ B → σ f ∈ B) : ↥B →+* ↥W where
  toFun b := ⟨σ (b : K), hBW _ (hσ _ b.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem restrictTo_apply_coe {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (B : Subalgebra R K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ B → σ f ∈ B) (b : ↥B) :
    ((restrictTo B W hBW σ hσ b : ↥W) : K) = σ (b : K) := rfl

theorem mem_iff_map_mem_of_pow_eq_one {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    (B : Subalgebra R K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ IsLocalRing.maximalIdeal ↥W ∧ f * (h : K) = (g : K))
    (α : K ≃ₐ[k] K) (hαB : ∀ f : K, f ∈ B → α f ∈ B) (hαB' : ∀ f : K, f ∈ B → α⁻¹ f ∈ B)
    (N : ℕ) (hN : 0 < N) (hαN : α ^ N = 1)
    (hP : ∀ b : ↥B, (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W →
      ∀ hb : α (b : K) ∈ B, (⟨α (b : K), hBW _ hb⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W) :
    ∀ f : K, f ∈ W ↔ α f ∈ W := by
  have hPv : ∀ b : K, b ∈ B → W.valuation b < 1 → W.valuation (α b) < 1 := by
    intro b hb hvb
    have h1 : (⟨b, hBW b hb⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W := (W.valuation_lt_one_iff _).mpr hvb
    exact (W.valuation_lt_one_iff _).mp (hP ⟨b, hb⟩ h1 (hαB b hb))
  have hiter : ∀ n : ℕ, ∀ b : K, b ∈ B → W.valuation b < 1 → (α ^ n) b ∈ B ∧ W.valuation ((α ^ n) b) < 1 := by
    intro n
    induction n with
    | zero =>
      intro b hb hv
      rw [pow_zero, AlgEquiv.one_apply]
      exact ⟨hb, hv⟩
    | succ n ih =>
      intro b hb hv
      have hob13 := ih b hb hv
      obtain ⟨h1, h2⟩ := hob13
      rw [pow_succ', AlgEquiv.mul_apply]
      exact ⟨hαB _ h1, hPv _ h1 h2⟩
  have hinv : α⁻¹ = α ^ (N - 1) := by
    have h : α ^ (N - 1) * α = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hN, hαN]
    exact (inv_eq_of_mul_eq_one_left h)
  have hPinv : ∀ b : K, b ∈ B → W.valuation b < 1 → W.valuation (α⁻¹ b) < 1 := by
    intro b hb hv
    rw [hinv]
    exact (hiter (N - 1) b hb hv).2
  intro f
  constructor
  · intro hf
    have hob14 := (hloc f).mp hf
    obtain ⟨g, h, hh, hfh⟩ := hob14
    refine (hloc (α f)).mpr ⟨⟨α (g : K), hαB _ g.2⟩, ⟨α (h : K), hαB _ h.2⟩, ?_, ?_⟩
    · intro hm
      apply hh
      have hv : W.valuation (α (h : K)) < 1 := (W.valuation_lt_one_iff _).mp hm
      have h2 := hPinv (α (h : K)) (hαB _ h.2) hv
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h2
      exact (W.valuation_lt_one_iff _).mpr h2
    · show α f * α (h : K) = α (g : K)
      rw [← map_mul, hfh]
  · intro hf
    have hob15 := (hloc (α f)).mp hf
    obtain ⟨g, h, hh, hfh⟩ := hob15
    refine (hloc f).mpr ⟨⟨α⁻¹ (g : K), hαB' _ g.2⟩, ⟨α⁻¹ (h : K), hαB' _ h.2⟩, ?_, ?_⟩
    · intro hm
      apply hh
      have hv : W.valuation (α⁻¹ (h : K)) < 1 := (W.valuation_lt_one_iff _).mp hm
      have h2 := hPv (α⁻¹ (h : K)) (hαB' _ h.2) hv
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h2
      exact (W.valuation_lt_one_iff _).mpr h2
    · show f * α⁻¹ (h : K) = α⁻¹ (g : K)
      have h3 : α⁻¹ (α f * (h : K)) = α⁻¹ (g : K) := by rw [hfh]
      rw [map_mul, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h3
      exact h3

theorem eqv_case {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    (B : Subalgebra R K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (π' : R) (hπfix : ∀ σ : K ≃ₐ[k] K, σ (algebraMap R K π') = algebraMap R K π')
    (hπm : IsLocalRing.maximalIdeal ↥W = Ideal.span {(⟨algebraMap R K π', hBW _ (B.algebraMap_mem π')⟩ : ↥W)})
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ IsLocalRing.maximalIdeal ↥W ∧ f * (h : K) = (g : K))
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (huniq : ∀ γ : Γ, γ ∈ S₀ → ∀ τ τ' : K ≃ₐ[k] K, Att γ τ → Att γ τ' → τ = τ')
    (hmul : ∀ γ δ : Γ, γ ∈ S₀ → δ ∈ S₀ → ∀ τ σ : K ≃ₐ[k] K, Att γ τ → Att δ σ → Att (δ * γ) (τ * σ))
    (hone : Att 1 1)
    (hex : ∀ γ : Γ, γ ∈ S₀ → ∃ τ : K ≃ₐ[k] K, Att γ⁻¹ τ)
    (Gfull : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥Gfull)
    (hGmem : ∀ τ : K ≃ₐ[k] K, τ ∈ Gfull ↔ ∃ γ : Γ, γ ∈ S₀ ∧ Att γ⁻¹ τ)
    (G : Subgroup (K ≃ₐ[k] K))
    (hG : G = Subgroup.closure {τ : K ≃ₐ[k] K | ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ})
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (hBstab : ∀ γ : Γ, γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → ∀ f : K, f ∈ B → τ f ∈ B)
    (hperm : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap R ↥B π' ∈ Q →
      ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ ∃ τ : K ≃ₐ[k] K, Att γ⁻¹ τ ∧
        ∀ b : ↥B, (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W →
          τ (b : K) ∈ B ∧ ∀ hb : τ (b : K) ∈ B, (⟨τ (b : K), hb⟩ : ↥B) ∈ Q)
    [DecidableEq (Subring ↥K₀)] (ends : Finset (Subring K))
    (h74 : ∀ γ : Γ, γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → (∀ f : K, f ∈ W ↔ τ f ∈ W) →
      ∀ O ∈ ends, ∃ O' ∈ ends, ∀ f : K, f ∈ O ↔ τ f ∈ O') :
    ∀ γ : Γ, γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → ∀ O ∈ ends.image (traceNode K₀),
      ∃ O' ∈ ends.image (traceNode K₀),
        ∀ (f : K) (hf : f ∈ K₀) (hf' : τ f ∈ K₀), (⟨f, hf⟩ : ↥K₀) ∈ O ↔ (⟨_, hf'⟩ : ↥K₀) ∈ O' := by
  classical
  intro γ hγ τ hτ O hO
  have hob16 := Finset.mem_image.mp hO
  obtain ⟨U, hU, rfl⟩ := hob16

  have hinvAtt : ∀ γ : Γ, γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → Att γ τ⁻¹ := by
    intro γ hγ τ hτ
    have hob17 := hex γ⁻¹ (S₀.inv_mem hγ)
    obtain ⟨σ, hσ⟩ := hob17
    rw [inv_inv] at hσ
    have h1 : Att (γ * γ⁻¹) (τ * σ) := hmul γ⁻¹ γ (S₀.inv_mem hγ) hγ τ σ hτ hσ
    rw [mul_inv_cancel] at h1
    have h2 : τ * σ = 1 := huniq 1 S₀.one_mem _ _ h1 hone
    have h3 : τ⁻¹ = σ := inv_eq_of_mul_eq_one_right h2
    rw [h3]
    exact hσ

  have hfinord : ∀ τ : K ≃ₐ[k] K, (∃ γ : Γ, γ ∈ S₀ ∧ Att γ⁻¹ τ) → ∃ N : ℕ, 0 < N ∧ τ ^ N = 1 := by
    intro τ h
    have hmem : τ ∈ Gfull := (hGmem τ).mpr h
    haveI := hGfin
    have hfo : IsOfFinOrder (⟨τ, hmem⟩ : ↥Gfull) := isOfFinOrder_of_finite _
    refine ⟨orderOf (⟨τ, hmem⟩ : ↥Gfull), hfo.orderOf_pos, ?_⟩
    have h1 := congrArg Subtype.val (pow_orderOf_eq_one (⟨τ, hmem⟩ : ↥Gfull))
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h1
    exact h1

  have hstab' : ∀ γ : Γ, γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → ∀ f : K, f ∈ B → τ⁻¹ f ∈ B := by
    intro γ hγ τ hτ
    have h1 : Att (γ⁻¹)⁻¹ τ⁻¹ := by
      rw [inv_inv]
      exact hinvAtt γ hγ τ hτ
    exact hBstab γ⁻¹ (S₀.inv_mem hγ) τ⁻¹ h1
  have hτB : ∀ f : K, f ∈ B → τ f ∈ B := hBstab γ hγ τ hτ
  have hτB' : ∀ f : K, f ∈ B → τ⁻¹ f ∈ B := hstab' γ hγ τ hτ

  have hQprime : ((IsLocalRing.maximalIdeal ↥W).comap (restrictTo B W hBW τ⁻¹ hτB')).IsPrime :=
    Ideal.comap_isPrime _ _
  have hπQ : algebraMap R ↥B π' ∈ (IsLocalRing.maximalIdeal ↥W).comap (restrictTo B W hBW τ⁻¹ hτB') := by
    rw [Ideal.mem_comap]
    have h1 : restrictTo B W hBW τ⁻¹ hτB' (algebraMap R ↥B π') =
        ⟨algebraMap R K π', hBW _ (B.algebraMap_mem π')⟩ := by
      apply Subtype.ext
      rw [restrictTo_apply_coe, Subalgebra.coe_algebraMap, hπfix]
    rw [h1, hπm]
    exact Ideal.subset_span rfl
  have hob18 := hperm _ hQprime hπQ
  obtain ⟨γ₁, hγ₁S₁, hγ₁S₀, τ', hτ', hτ'Q⟩ := hob18

  have hτ'B : ∀ f : K, f ∈ B → τ' f ∈ B := hBstab γ₁ hγ₁S₀ τ' hτ'
  have hτ'B' : ∀ f : K, f ∈ B → τ'⁻¹ f ∈ B := hstab' γ₁ hγ₁S₀ τ' hτ'
  have hαB : ∀ f : K, f ∈ B → (τ⁻¹ * τ') f ∈ B := by
    intro f hf
    rw [AlgEquiv.mul_apply]
    exact hτB' _ (hτ'B _ hf)
  have hαB' : ∀ f : K, f ∈ B → (τ⁻¹ * τ')⁻¹ f ∈ B := by
    intro f hf
    rw [mul_inv_rev, inv_inv, AlgEquiv.mul_apply]
    exact hτ'B' _ (hτB _ hf)
  have hαatt : Att (γ₁⁻¹ * γ) (τ⁻¹ * τ') :=
    hmul γ γ₁⁻¹ hγ (S₀.inv_mem hγ₁S₀) τ⁻¹ τ' (hinvAtt γ hγ τ hτ) hτ'
  have hαfin : ∃ N : ℕ, 0 < N ∧ (τ⁻¹ * τ') ^ N = 1 := by
    refine hfinord (τ⁻¹ * τ') ⟨(γ₁⁻¹ * γ)⁻¹, S₀.inv_mem (S₀.mul_mem (S₀.inv_mem hγ₁S₀) hγ), ?_⟩
    rw [inv_inv]
    exact hαatt
  have hob19 := hαfin
  obtain ⟨N, hN, hαN⟩ := hob19
  have hP : ∀ b : ↥B, (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W →
      ∀ hb : (τ⁻¹ * τ') (b : K) ∈ B, (⟨(τ⁻¹ * τ') (b : K), hBW _ hb⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W := by
    intro b hbm hb
    have hob20 := hτ'Q b hbm
    obtain ⟨h1, h2⟩ := hob20
    have h3 := Ideal.mem_comap.mp (h2 h1)
    have h4 : (⟨(τ⁻¹ * τ') (b : K), hBW _ hb⟩ : ↥W) = restrictTo B W hBW τ⁻¹ hτB' ⟨τ' (b : K), h1⟩ := by
      apply Subtype.ext
      change (τ⁻¹ * τ') (b : K) = τ⁻¹ (τ' (b : K))
      exact AlgEquiv.mul_apply _ _ _
    rw [h4]
    exact h3
  have hαW : ∀ f : K, f ∈ W ↔ (τ⁻¹ * τ') f ∈ W :=
    mem_iff_map_mem_of_pow_eq_one B W hBW hloc (τ⁻¹ * τ') hαB hαB' N hN hαN hP

  have hρW : ∀ f : K, f ∈ W ↔ (τ'⁻¹ * τ) f ∈ W := by
    intro f
    have h1 := hαW ((τ'⁻¹ * τ) f)
    have h2 : τ⁻¹ * τ' * (τ'⁻¹ * τ) = 1 := by group
    rw [← AlgEquiv.mul_apply, h2, AlgEquiv.one_apply] at h1
    exact h1.symm
  have hρatt : Att (γ⁻¹ * γ₁) (τ'⁻¹ * τ) :=
    hmul γ₁ γ⁻¹ hγ₁S₀ (S₀.inv_mem hγ) τ'⁻¹ τ (hinvAtt γ₁ hγ₁S₀ τ' hτ') hτ
  have hρatt' : Att (γ₁⁻¹ * γ)⁻¹ (τ'⁻¹ * τ) := by
    rw [mul_inv_rev, inv_inv]
    exact hρatt
  have hob21 := h74 (γ₁⁻¹ * γ) (S₀.mul_mem (S₀.inv_mem hγ₁S₀) hγ) (τ'⁻¹ * τ) hρatt' hρW U hU
  obtain ⟨U', hU', hiff⟩ := hob21
  refine ⟨traceNode K₀ U', Finset.mem_image_of_mem _ hU', ?_⟩
  intro f hf hf'
  have hτ'G : τ' ∈ G := by
    rw [hG]
    exact Subgroup.subset_closure ⟨γ₁, hγ₁S₁, hγ₁S₀, hτ'⟩
  have hfix : τ'⁻¹ (τ f) = τ f := by
    have hmem : τ f ∈ IntermediateField.fixedField G := by
      rw [← hK₀]
      exact hf'
    rw [IntermediateField.mem_fixedField_iff] at hmem
    exact hmem τ'⁻¹ (G.inv_mem hτ'G)
  rw [mem_traceNode, mem_traceNode]
  change f ∈ U ↔ τ f ∈ U'
  rw [hiff f, AlgEquiv.mul_apply, hfix]

theorem att_of_mem_closure {k K : Type} [Field k] [Field K] [Algebra k K]
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (huniq : ∀ γ : Γ, γ ∈ S₀ → ∀ τ τ' : K ≃ₐ[k] K, Att γ τ → Att γ τ' → τ = τ')
    (hmul : ∀ γ δ : Γ, γ ∈ S₀ → δ ∈ S₀ → ∀ τ σ : K ≃ₐ[k] K, Att γ τ → Att δ σ → Att (δ * γ) (τ * σ))
    (hone : Att 1 1)
    (hex : ∀ γ : Γ, γ ∈ S₀ → ∃ τ : K ≃ₐ[k] K, Att γ⁻¹ τ)
    (G : Subgroup (K ≃ₐ[k] K))
    (hG : G = Subgroup.closure {τ : K ≃ₐ[k] K | ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ}) :
    ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ := by
  intro τ hτ
  rw [hG] at hτ
  refine Subgroup.closure_induction (p := fun τ _ => ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ) ?_ ?_ ?_ ?_ hτ
  · intro τ h; exact h
  · exact ⟨1, S₁.one_mem, S₀.one_mem, by rw [inv_one]; exact hone⟩
  · rintro τ σ - - ⟨γ, hγ1, hγ0, hτ⟩ ⟨δ, hδ1, hδ0, hσ⟩
    refine ⟨γ * δ, S₁.mul_mem hγ1 hδ1, S₀.mul_mem hγ0 hδ0, ?_⟩
    rw [mul_inv_rev]
    exact hmul γ⁻¹ δ⁻¹ (S₀.inv_mem hγ0) (S₀.inv_mem hδ0) τ σ hτ hσ
  · rintro τ - ⟨γ, hγ1, hγ0, hτ⟩
    have hob22 := hex γ⁻¹ (S₀.inv_mem hγ0)
    obtain ⟨σ, hσ⟩ := hob22
    rw [inv_inv] at hσ
    have h1 : Att (γ * γ⁻¹) (τ * σ) := hmul γ⁻¹ γ (S₀.inv_mem hγ0) hγ0 τ σ hτ hσ
    rw [mul_inv_cancel] at h1
    have h2 : τ * σ = 1 := huniq 1 S₀.one_mem _ _ h1 hone
    have h3 : τ⁻¹ = σ := inv_eq_of_mul_eq_one_right h2
    refine ⟨γ⁻¹, S₁.inv_mem hγ1, S₀.inv_mem hγ0, ?_⟩
    rw [inv_inv, h3]
    exact hσ

theorem exists_invariant_separator {k K : Type} [Field k] [Field K] [Algebra k K]
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (hGatt : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (O O' : Subring K) (f : K) (hf : f ∈ O) (hfu : ¬ IsUnit (⟨f, hf⟩ : ↥O))
    (hsep : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ →
      τ f ∈ O ∧ ∃ hf' : τ f ∈ O', IsUnit (⟨τ f, hf'⟩ : ↥O')) :
    ∃ (g : K) (hg : g ∈ O) (hg' : g ∈ O'), g ∈ K₀ ∧ ¬ IsUnit (⟨g, hg⟩ : ↥O) ∧ IsUnit (⟨g, hg'⟩ : ↥O') := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  have hall : ∀ σ : ↥G, (σ : K ≃ₐ[k] K) f ∈ O ∧ ∃ hf' : (σ : K ≃ₐ[k] K) f ∈ O', IsUnit (⟨(σ : K ≃ₐ[k] K) f, hf'⟩ : ↥O') := by
    intro σ
    have hob23 := hGatt σ σ.2
    obtain ⟨γ, h1, h0, hatt⟩ := hob23
    exact hsep γ h1 h0 σ hatt
  refine ⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) f, ?_, ?_, ?_, ?_, ?_⟩
  · exact prod_mem fun σ _ => (hall σ).1
  · exact prod_mem fun σ _ => (hall σ).2.1
  ·
    rw [hK₀, IntermediateField.mem_fixedField_iff]
    intro ρ hρ
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨ρ, hρ⟩ : ↥G)) _ _ ?_
    intro σ
    simp [AlgEquiv.mul_apply]
  ·
    intro hu
    apply hfu
    have hsplit : (⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) f, prod_mem fun σ _ => (hall σ).1⟩ : ↥O) =
        ⟨f, hf⟩ * ⟨∏ σ ∈ Finset.univ.erase (1 : ↥G), (σ : K ≃ₐ[k] K) f,
          prod_mem fun σ _ => (hall σ).1⟩ := by
      apply Subtype.ext
      show (∏ σ : ↥G, (σ : K ≃ₐ[k] K) f) = f * ∏ σ ∈ Finset.univ.erase (1 : ↥G), (σ : K ≃ₐ[k] K) f
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : ↥G)), mul_comm]
      simp
    rw [hsplit] at hu
    exact isUnit_of_mul_isUnit_left hu
  ·
    rw [isUnit_mk_iff]
    have hinv : ∀ σ : ↥G, ∃ y : K, y ∈ O' ∧ (σ : K ≃ₐ[k] K) f * y = 1 := by
      intro σ
      have hob24 := (hall σ).2
      obtain ⟨hf', hu⟩ := hob24
      exact (isUnit_mk_iff O' _ hf').mp hu
    choose y hy using hinv
    refine ⟨∏ σ : ↥G, y σ, prod_mem fun σ _ => (hy σ).1, ?_⟩
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun σ _ => (hy σ).2

theorem sep_and_card {k K : Type} [Field k] [Field K] [Algebra k K]
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (hGatt : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    [DecidableEq (Subring ↥K₀)] (ends : Finset (Subring K))
    (hR7sep : ∀ O ∈ ends, ∀ O' ∈ ends, O ≠ O' → ∃ (f : K) (hf : f ∈ O), ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧
      ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ →
        τ f ∈ O ∧ ∃ hf' : τ f ∈ O', IsUnit (⟨τ f, hf'⟩ : ↥O')) :
    (ends.image (traceNode K₀)).card = ends.card ∧
    (∀ O ∈ ends.image (traceNode K₀), ∀ O' ∈ ends.image (traceNode K₀), O ≠ O' →
      ∃ (f : ↥K₀) (hf : f ∈ O) (hf' : f ∈ O'), ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) := by
  classical

  have key : ∀ U ∈ ends, ∀ U' ∈ ends, U ≠ U' → ∃ (g : ↥K₀) (hg : g ∈ traceNode K₀ U) (hg' : g ∈ traceNode K₀ U'),
      ¬ IsUnit (⟨g, hg⟩ : ↥(traceNode K₀ U)) ∧ IsUnit (⟨g, hg'⟩ : ↥(traceNode K₀ U')) := by
    intro U hU U' hU' hne
    have hob25 := hR7sep U hU U' hU' hne
    obtain ⟨f, hf, hfu, hsep⟩ := hob25
    obtain ⟨g, hg, hg', hgK₀, hgu, hgu'⟩ :=
      exists_invariant_separator S₀ S₁ Att G hGfin hGatt K₀ hK₀ U U' f hf hfu hsep
    refine ⟨⟨g, hgK₀⟩, hg, hg', ?_, ?_⟩
    · rw [isUnit_trace_iff]; exact hgu
    · rw [isUnit_trace_iff]; exact hgu'
  refine ⟨?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro U hU U' hU' heq
    by_contra hne
    have hob26 := key U hU U' hU' hne
    obtain ⟨g, hg, hg', hgu, hgu'⟩ := hob26
    apply hgu
    have hob27 := (isUnit_mk_iff (traceNode K₀ U') (g : ↥K₀) hg').mp hgu'
    obtain ⟨y, hy, hgy⟩ := hob27
    have hy' : y ∈ traceNode K₀ U := by rw [heq]; exact hy
    exact (isUnit_mk_iff (traceNode K₀ U) (g : ↥K₀) hg).mpr ⟨y, hy', hgy⟩
  · intro O hO O' hO' hne
    have hob28 := Finset.mem_image.mp hO
    obtain ⟨U, hU, rfl⟩ := hob28
    have hob29 := Finset.mem_image.mp hO'
    obtain ⟨U', hU', rfl⟩ := hob29
    have hne' : U ≠ U' := fun h => hne (by rw [h])
    exact key U hU U' hU' hne'

theorem jsharp_package
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ')
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ]
    [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)] :
    ∃ (hjK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) ∈ Kℓ),
      (⟨_, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ ∧
      ∀ z : ↥Kℓ, z ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ →
        IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(⟨_, hjK⟩ : ↥Kℓ)} : Set ↥Kℓ)) z := by
  obtain ⟨hj, hj0, hjK, hjC⟩ :=
    ModularCurve.FullLevel.qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField q M' ℓ' ↥k₀ Kℓ hKℓ
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
  have ej : jℓ = ⟨_, hj⟩ := Subtype.ext hjℓ
  subst ej
  refine ⟨hjK, hjC, ?_⟩

  have hj'0 : (⟨_, hjK⟩ : ↥Kℓ) ≠ 0 := by
    intro h0
    apply hj0
    apply Subtype.ext
    have h1 : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) = 0 := congrArg Subtype.val h0
    have h2 : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) = ModularCurve.qExpand ↥k₀ ℓ' 0 := by rw [h1, map_zero]
    exact (ModularCurve.qExpand_injective (N := ℓ')) h2
  haveI : Fact ((⟨_, hjK⟩ : ↥Kℓ) ≠ 0) := ⟨hj'0⟩
  have hlt : 1 < ℓ' := by omega
  obtain ⟨-, hjint, -, -⟩ :=
    ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
      ℓ' hlt ↥k₀ Kℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨_, hj⟩ rfl ⟨_, hjK⟩
      (by rw [ModularCurve.coeffEmb_qExpand])
  intro z hz
  exact isIntegral_adjoin_singleton_trans _ _ _ ((mem_chartAlg_iff _ _).mp hjint) ((mem_chartAlg_iff _ _).mp hz)

theorem jq_residue_package
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    ∃ hgi : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ∧
      ∃ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) := by

  have heq : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    show (jqModC ↥A).map A.subtype = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [ModularCurve.map_jqModC, ModularCurve.map_jqModC]
  have hy : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [heq]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  have hob30 := hR₀ (jqModC ↥A) hy
  obtain ⟨h, hres⟩ := hob30
  have e : (⟨coeffMap A.subtype (jqModC ↥A), hy⟩ : ↥(modularFunctionFieldBar M')) =
      ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :=
    Subtype.ext heq
  have hgi : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
      ↥(modularFunctionFieldBar M')) ∈ R₀.integers := e ▸ h
  refine ⟨hgi, ?_, ?_⟩
  · have hres' : (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = jGeomGen (ResidueField A) M' := by
      have h1 : (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = R₀.residue ⟨_, h⟩ := by
        congr 1
        exact Subtype.ext e.symm
      rw [h1]
      apply Subtype.ext
      rw [hres]
      show (jqModC ↥A).map (IsLocalRing.residue ↥A) = jqModC (ResidueField A)
      rw [ModularCurve.map_jqModC]
    rw [hres']
    have hss : IsSupersingularPlace q M' (ResidueField A) (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) :=
      (hW s).mp s.2
    exact hss.2.1.1
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
      ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩))
    have hob31 := hκ (a : AlgebraicClosure ℚ) a.2
    obtain ⟨c, hcA, hac, hm⟩ := hob31
    refine ⟨c, hcA, ?_⟩
    rw [← ha]
    have hsub : (⟨(a : AlgebraicClosure ℚ) - c, hac⟩ : ↥A) = a - ⟨(c : AlgebraicClosure ℚ), hcA⟩ := Subtype.ext rfl
    rw [hsub] at hm
    have : IsLocalRing.residue ↥A a = IsLocalRing.residue ↥A ⟨(c : AlgebraicClosure ℚ), hcA⟩ := by
      rw [← sub_eq_zero, ← map_sub]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hm
    exact this.symm

theorem C3aux_exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic ℚ ↥k₀ :=
    Algebra.IsAlgebraic.of_injective (k₀.val) (k₀.val).toRingHom.injective
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / m) ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

noncomputable def twistIncl {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (Bc : Subalgebra R K) (O : Subring K) (hBO : ∀ f : K, f ∈ Bc → f ∈ O)
    (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ Bc → σ f ∈ Bc) : ↥Bc →+* ↥O where
  toFun b := ⟨σ (b : K), hBO _ (hσ _ b.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem twistIncl_apply_coe {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (Bc : Subalgebra R K) (O : Subring K) (hBO : ∀ f : K, f ∈ Bc → f ∈ O)
    (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ Bc → σ f ∈ Bc) (b : ↥Bc) :
    ((twistIncl Bc O hBO σ hσ b : ↥O) : K) = σ (b : K) := rfl

theorem mem_iff_pow_apply_mem {k K : Type} [Field k] [Field K] [Algebra k K] (O : Subring K) (τ₀ : K ≃ₐ[k] K)
    (h : ∀ f : K, f ∈ O ↔ τ₀ f ∈ O) : ∀ (m : ℕ) (f : K), f ∈ O ↔ (τ₀ ^ m) f ∈ O := by
  intro m
  induction m with
  | zero => intro f; rw [pow_zero, AlgEquiv.one_apply]
  | succ m ih => intro f; rw [pow_succ, AlgEquiv.mul_apply, ← ih (τ₀ f)]; exact h f

theorem sep_and_card_of_commonChart {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (hGatt : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ)
    (hGgen : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → τ ∈ G)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (B : Subalgebra R K) (W : ValuationSubring K)
    (hfrac : ∀ f : K, ∃ g h : ↥B, (h : K) ≠ 0 ∧ f * (h : K) = (g : K))
    (τ₀ : K ≃ₐ[k] K) (n : ℕ)
    (h72 : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → (∀ f : K, f ∈ W ↔ τ f ∈ W) →
      ∃ m : ℕ, m < n ∧ ∀ f : K, f ∈ B → τ f = (τ₀ ^ m) f)
    [DecidableEq (Subring ↥K₀)] (ends : Finset (Subring K))
    (h76 : ∀ O ∈ ends, ∀ f : K, f ∈ O ↔ τ₀ f ∈ O)
    (h77 : ∀ O ∈ ends, ∀ O' ∈ ends, O ≠ O' → ∃ (f : K) (hf : f ∈ O) (hf' : f ∈ O'),
      ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O'))
    (hOW : ∀ O ∈ ends, ∀ f : K, f ∈ O → f ∈ W)
    (hOlocal : ∀ O ∈ ends, IsLocalRing ↥O)
    (hR7one : ∀ O ∈ ends, ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ →
      (∀ f : K, f ∈ O → τ f ∈ W) → ∀ f : K, f ∈ W ↔ τ f ∈ W)
    (Bc : Subalgebra R K)
    (hBcG : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → ∀ f : K, f ∈ Bc → τ f ∈ Bc)
    (hBcO : ∀ O ∈ ends, (∀ f : K, f ∈ Bc → f ∈ O) ∧
      (∀ f : K, f ∈ O ↔ ∃ g h : K, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) :
    (ends.image (traceNode K₀)).card = ends.card ∧
    (∀ O ∈ ends.image (traceNode K₀), ∀ O' ∈ ends.image (traceNode K₀), O ≠ O' →
      ∃ (f : ↥K₀) (hf : f ∈ O) (hf' : f ∈ O'), ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  have hGBc : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bc → σ f ∈ Bc := by
    intro σ hσ
    have hob32 := hGatt σ hσ
    obtain ⟨γ, h1, h0, hatt⟩ := hob32
    exact hBcG γ h1 h0 σ hatt

  have hrigid : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ O ∈ ends, (∀ f : K, f ∈ O → σ f ∈ W) →
      ∀ O' ∈ ends, ∀ f : K, f ∈ O' ↔ σ f ∈ O' := by
    intro σ hσ O hO hinto O' hO'
    have hob33 := hGatt σ hσ
    obtain ⟨γ, h1, h0, hatt⟩ := hob33
    have hW : ∀ f : K, f ∈ W ↔ σ f ∈ W := hR7one O hO γ h1 h0 σ hatt hinto
    have hob34 := h72 γ h1 h0 σ hatt hW
    obtain ⟨m, -, hm⟩ := hob34
    have hall : ∀ f : K, σ f = (τ₀ ^ m) f := by
      intro f
      have hob35 := hfrac f
      obtain ⟨g, h, hh0, hfh⟩ := hob35
      have e1 : σ f * σ (h : K) = σ (g : K) := by rw [← map_mul, hfh]
      have e2 : (τ₀ ^ m) f * (τ₀ ^ m) (h : K) = (τ₀ ^ m) (g : K) := by rw [← map_mul, hfh]
      rw [hm _ h.2, hm _ g.2, ← e2] at e1
      have hne : (τ₀ ^ m) (h : K) ≠ 0 := by
        intro h0
        apply hh0
        have h3 := congrArg (τ₀ ^ m).symm h0
        rwa [AlgEquiv.symm_apply_apply, map_zero] at h3
      exact mul_right_cancel₀ hne e1
    intro f
    rw [hall f]
    exact mem_iff_pow_apply_mem O' τ₀ (h76 O' hO') m f

  have key : ∀ U ∈ ends, ∀ U' ∈ ends, U ≠ U' → ∃ (g : ↥K₀) (hg : g ∈ traceNode K₀ U) (hg' : g ∈ traceNode K₀ U'),
      ¬ IsUnit (⟨g, hg⟩ : ↥(traceNode K₀ U)) ∧ IsUnit (⟨g, hg'⟩ : ↥(traceNode K₀ U')) := by
    intro U hU U' hU' hne
    haveI hUloc : IsLocalRing ↥U := hOlocal U hU
    haveI hU'loc : IsLocalRing ↥U' := hOlocal U' hU'
    have hob36 := hBcO U hU
    obtain ⟨hBU, hlocU⟩ := hob36
    have hob37 := hBcO U' hU'
    obtain ⟨hBU', hlocU'⟩ := hob37

    let I : ↥G → Ideal ↥Bc := fun σ =>
      (maximalIdeal ↥U').comap (twistIncl Bc U' hBU' (σ : K ≃ₐ[k] K) (hGBc σ σ.2))
    let Q : Ideal ↥Bc := (maximalIdeal ↥U).comap (twistIncl Bc U hBU (1 : K ≃ₐ[k] K) (fun f hf => by rw [AlgEquiv.one_apply]; exact hf))
    have hIprime : ∀ σ : ↥G, (I σ).IsPrime := fun σ => Ideal.comap_isPrime _ _
    have hmemI : ∀ (σ : ↥G) (b : ↥Bc), b ∈ I σ ↔ ¬ IsUnit (⟨(σ : K ≃ₐ[k] K) (b : K), hBU' _ (hGBc σ σ.2 _ b.2)⟩ : ↥U') := by
      intro σ b
      show (twistIncl Bc U' hBU' (σ : K ≃ₐ[k] K) (hGBc σ σ.2) b) ∈ maximalIdeal ↥U' ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact Iff.rfl
    have hmemQ : ∀ b : ↥Bc, b ∈ Q ↔ ¬ IsUnit (⟨(b : K), hBU _ b.2⟩ : ↥U) := by
      intro b
      show (twistIncl Bc U hBU (1 : K ≃ₐ[k] K) _ b) ∈ maximalIdeal ↥U ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact Iff.rfl

    have hnot : ∀ σ : ↥G, ¬ (Q ≤ I σ) := by
      intro σ hle

      have hsub : ∀ f : K, f ∈ U' → (σ : K ≃ₐ[k] K)⁻¹ f ∈ U := by
        intro f hf
        have hob38 := (hlocU' f).mp hf
        obtain ⟨g, h, hg, hh, hhu, hfh⟩ := hob38

        have hh' : (σ : K ≃ₐ[k] K)⁻¹ h ∈ Bc := hGBc _ (G.inv_mem σ.2) _ hh
        have hg' : (σ : K ≃ₐ[k] K)⁻¹ g ∈ Bc := hGBc _ (G.inv_mem σ.2) _ hg
        have hnotI : (⟨(σ : K ≃ₐ[k] K)⁻¹ h, hh'⟩ : ↥Bc) ∉ I σ := by
          rw [hmemI]
          intro hnu
          apply hnu
          have : (⟨(σ : K ≃ₐ[k] K) ((σ : K ≃ₐ[k] K)⁻¹ h), hBU' _ (hGBc σ σ.2 _ hh')⟩ : ↥U') = ⟨h, hBU' _ hh⟩ := by
            apply Subtype.ext
            show (σ : K ≃ₐ[k] K) ((σ : K ≃ₐ[k] K)⁻¹ h) = h
            rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
          rw [this]
          exact hhu _
        have hnotQ : (⟨(σ : K ≃ₐ[k] K)⁻¹ h, hh'⟩ : ↥Bc) ∉ Q := fun hq => hnotI (hle hq)
        rw [hmemQ, not_not] at hnotQ
        have hob39 := (isUnit_mk_iff U _ (hBU _ hh')).mp hnotQ
        obtain ⟨y, hy, hy1⟩ := hob39
        have : (σ : K ≃ₐ[k] K)⁻¹ f = (σ : K ≃ₐ[k] K)⁻¹ g * y := by
          have e : (σ : K ≃ₐ[k] K)⁻¹ f * (σ : K ≃ₐ[k] K)⁻¹ h = (σ : K ≃ₐ[k] K)⁻¹ g := by rw [← map_mul, hfh]
          calc (σ : K ≃ₐ[k] K)⁻¹ f = (σ : K ≃ₐ[k] K)⁻¹ f * ((σ : K ≃ₐ[k] K)⁻¹ h * y) := by rw [hy1, mul_one]
            _ = (σ : K ≃ₐ[k] K)⁻¹ g * y := by rw [← mul_assoc, e]
        rw [this]
        exact U.mul_mem (hBU _ hg') hy
      have hinto : ∀ f : K, f ∈ U' → (σ : K ≃ₐ[k] K)⁻¹ f ∈ W := fun f hf => hOW U hU _ (hsub f hf)
      have hfix := hrigid _ (G.inv_mem σ.2) U' hU' hinto U' hU'

      have hU'U : ∀ f : K, f ∈ U' → f ∈ U := by
        intro f hf
        have h2 : (σ : K ≃ₐ[k] K) f ∈ U' := by
          rw [hfix, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]; exact hf
        have h1 := hsub _ h2
        rwa [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h1
      have hob40 := h77 U hU U' hU' hne
      obtain ⟨f, hfU, hfU', hnu, hu⟩ := hob40
      apply hnu
      have hob41 := (isUnit_mk_iff U' f hfU').mp hu
      obtain ⟨y, hy, hy1⟩ := hob41
      exact (isUnit_mk_iff U f hfU).mpr ⟨y, hU'U y hy, hy1⟩

    have havoid : ¬ ((Q : Set ↥Bc) ⊆ ⋃ σ ∈ (↑(Finset.univ : Finset ↥G) : Set ↥G), (I σ : Set ↥Bc)) := by
      rw [Ideal.subset_union_prime (1 : ↥G) (1 : ↥G) (fun σ _ _ _ => hIprime σ)]
      rintro ⟨σ, -, hσ⟩
      exact hnot σ hσ
    rw [Set.not_subset] at havoid
    obtain ⟨b, hbQ, hbI⟩ := havoid
    have hbI' : ∀ σ : ↥G, (b : ↥Bc) ∉ I σ := by
      intro σ hσ
      apply hbI
      simp only [Finset.coe_univ, Set.mem_iUnion, Set.mem_univ, exists_true_left]
      exact ⟨σ, hσ⟩

    have hbQ' : ¬ IsUnit (⟨((b : ↥Bc) : K), hBU _ b.2⟩ : ↥U) := (hmemQ b).mp hbQ
    have hsep : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ →
        τ ((b : ↥Bc) : K) ∈ U ∧ ∃ hf' : τ ((b : ↥Bc) : K) ∈ U', IsUnit (⟨τ ((b : ↥Bc) : K), hf'⟩ : ↥U') := by
      intro γ h1 h0 τ hatt
      have hτG : τ ∈ G := hGgen γ h1 h0 τ hatt
      refine ⟨hBU _ (hGBc τ hτG _ b.2), hBU' _ (hGBc τ hτG _ b.2), ?_⟩
      have := hbI' ⟨τ, hτG⟩
      rw [hmemI, not_not] at this
      exact this

    have hall : ∀ σ : ↥G, (σ : K ≃ₐ[k] K) ((b : ↥Bc) : K) ∈ U ∧
        ∃ hf' : (σ : K ≃ₐ[k] K) ((b : ↥Bc) : K) ∈ U', IsUnit (⟨(σ : K ≃ₐ[k] K) ((b : ↥Bc) : K), hf'⟩ : ↥U') := by
      intro σ
      have hob42 := hGatt σ σ.2
      obtain ⟨γ, h1, h0, hatt⟩ := hob42
      exact hsep γ h1 h0 σ hatt
    set f₀ : K := ((b : ↥Bc) : K) with hf₀
    have hNU : (∏ σ : ↥G, (σ : K ≃ₐ[k] K) f₀) ∈ U := prod_mem fun σ _ => (hall σ).1
    have hNU' : (∏ σ : ↥G, (σ : K ≃ₐ[k] K) f₀) ∈ U' := prod_mem fun σ _ => (hall σ).2.1
    have hNK₀ : (∏ σ : ↥G, (σ : K ≃ₐ[k] K) f₀) ∈ K₀ := by
      rw [hK₀, IntermediateField.mem_fixedField_iff]
      intro ρ hρ
      rw [map_prod]
      refine Fintype.prod_equiv (Equiv.mulLeft (⟨ρ, hρ⟩ : ↥G)) _ _ ?_
      intro σ
      simp [AlgEquiv.mul_apply]
    have hNnu : ¬ IsUnit (⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) f₀, hNU⟩ : ↥U) := by
      intro hu
      apply hbQ'
      have hsplit : (⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) f₀, hNU⟩ : ↥U) =
          ⟨f₀, hBU _ b.2⟩ * ⟨∏ σ ∈ Finset.univ.erase (1 : ↥G), (σ : K ≃ₐ[k] K) f₀,
            prod_mem fun σ _ => (hall σ).1⟩ := by
        apply Subtype.ext
        show (∏ σ : ↥G, (σ : K ≃ₐ[k] K) f₀) = f₀ * ∏ σ ∈ Finset.univ.erase (1 : ↥G), (σ : K ≃ₐ[k] K) f₀
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : ↥G)), mul_comm]
        simp
      rw [hsplit] at hu
      exact isUnit_of_mul_isUnit_left hu
    have hNu : IsUnit (⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) f₀, hNU'⟩ : ↥U') := by
      rw [isUnit_mk_iff]
      have hinv : ∀ σ : ↥G, ∃ y : K, y ∈ U' ∧ (σ : K ≃ₐ[k] K) f₀ * y = 1 := by
        intro σ
        have hob43 := (hall σ).2
        obtain ⟨hf', hu⟩ := hob43
        exact (isUnit_mk_iff U' _ hf').mp hu
      choose y hy using hinv
      refine ⟨∏ σ : ↥G, y σ, prod_mem fun σ _ => (hy σ).1, ?_⟩
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun σ _ => (hy σ).2
    refine ⟨⟨_, hNK₀⟩, hNU, hNU', ?_, ?_⟩
    · rw [isUnit_trace_iff]; exact hNnu
    · rw [isUnit_trace_iff]; exact hNu
  refine ⟨?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro U hU U' hU' heq
    by_contra hne
    have hob44 := key U hU U' hU' hne
    obtain ⟨g, hg, hg', hgu, hgu'⟩ := hob44
    apply hgu
    have hob45 := (isUnit_mk_iff (traceNode K₀ U') (g : ↥K₀) hg').mp hgu'
    obtain ⟨y, hy, hgy⟩ := hob45
    have hy' : y ∈ traceNode K₀ U := by rw [heq]; exact hy
    exact (isUnit_mk_iff (traceNode K₀ U) (g : ↥K₀) hg).mpr ⟨y, hy', hgy⟩
  · intro O hO O' hO' hne
    have hob46 := Finset.mem_image.mp hO
    obtain ⟨U, hU, rfl⟩ := hob46
    have hob47 := Finset.mem_image.mp hO'
    obtain ⟨U', hU', rfl⟩ := hob47
    have hne' : U ≠ U' := fun h => hne (by rw [h])
    exact key U hU U' hU' hne'

open IsLocalRing

theorem apply_eq_self_of_frac {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (B : Subalgebra R K) (hfrac : ∀ f : K, ∃ g h : ↥B, (h : K) ≠ 0 ∧ f * (h : K) = (g : K))
    (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ B → σ f = f) : ∀ f : K, σ f = f := by
  intro f
  have hob48 := hfrac f
  obtain ⟨g, h, hh0, hfh⟩ := hob48
  have e1 : σ f * σ (h : K) = σ (g : K) := by rw [← map_mul, hfh]
  rw [hσ _ h.2, hσ _ g.2, ← hfh] at e1
  exact mul_right_cancel₀ hh0 e1

theorem exists_eq_pow_of_stabilises {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (G : Subgroup (K ≃ₐ[k] K))
    (hGatt : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ)
    (B : Subalgebra R K) (W : ValuationSubring K)
    (hfrac : ∀ f : K, ∃ g h : ↥B, (h : K) ≠ 0 ∧ f * (h : K) = (g : K))
    (τ₀ : K ≃ₐ[k] K) (n : ℕ)
    (h72 : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → (∀ f : K, f ∈ W ↔ τ f ∈ W) →
      ∃ m : ℕ, m < n ∧ ∀ f : K, f ∈ B → τ f = (τ₀ ^ m) f)
    (O : Subring K) (hOW : ∀ f : K, f ∈ O → f ∈ W)
    (hR7oneO : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ →
      (∀ f : K, f ∈ O → τ f ∈ W) → ∀ f : K, f ∈ W ↔ τ f ∈ W) :
    ∀ σ : K ≃ₐ[k] K, σ ∈ G → (∀ f : K, f ∈ O ↔ σ f ∈ O) → ∃ j : ℕ, ∀ f : K, σ f = (τ₀ ^ j) f := by
  intro σ hσ hstab
  have hob49 := hGatt σ hσ
  obtain ⟨γ, h1, h0, hatt⟩ := hob49
  have hinto : ∀ f : K, f ∈ O → σ f ∈ W := fun f hf => hOW _ ((hstab f).mp hf)
  have hW : ∀ f : K, f ∈ W ↔ σ f ∈ W := hR7oneO γ h1 h0 σ hatt hinto
  have hob50 := h72 γ h1 h0 σ hatt hW
  obtain ⟨m, -, hm⟩ := hob50
  refine ⟨m, ?_⟩
  have key := apply_eq_self_of_frac B hfrac ((τ₀ ^ m)⁻¹ * σ) (fun f hf => by
    rw [AlgEquiv.mul_apply, hm f hf, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
  intro f
  have h1 := key f
  rw [AlgEquiv.mul_apply] at h1
  have h2 := congrArg (τ₀ ^ m) h1
  rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h2

def fixedPart {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K)) (O : Subring K) : Subring K where
  carrier := {f | f ∈ O ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f}
  mul_mem' := fun {a b} ha hb => ⟨O.mul_mem ha.1 hb.1, fun σ hσ => by rw [map_mul, ha.2 σ hσ, hb.2 σ hσ]⟩
  one_mem' := ⟨O.one_mem, fun σ _ => map_one σ⟩
  add_mem' := fun {a b} ha hb => ⟨O.add_mem ha.1 hb.1, fun σ hσ => by rw [map_add, ha.2 σ hσ, hb.2 σ hσ]⟩
  zero_mem' := ⟨O.zero_mem, fun σ _ => map_zero σ⟩
  neg_mem' := fun {a} ha => ⟨O.neg_mem ha.1, fun σ hσ => by rw [map_neg, ha.2 σ hσ]⟩

theorem mem_fixedPart {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K)) (O : Subring K) (f : K) :
    f ∈ fixedPart G O ↔ f ∈ O ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f := Iff.rfl

noncomputable def traceEquivFixedPart {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K))
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G) (O : Subring K) :
    ↥(traceNode K₀ O) ≃+* ↥(fixedPart G O) where
  toFun f := ⟨((f : ↥K₀) : K), ⟨f.2, fun σ hσ => by
    have hf : ((f : ↥K₀) : K) ∈ IntermediateField.fixedField G := hK₀ ▸ (f : ↥K₀).2
    rw [IntermediateField.mem_fixedField_iff] at hf
    exact hf σ hσ⟩⟩
  invFun g := ⟨⟨(g : K), by
    rw [hK₀, IntermediateField.mem_fixedField_iff]
    exact g.2.2⟩, g.2.1⟩
  left_inv f := Subtype.ext (Subtype.ext rfl)
  right_inv g := Subtype.ext rfl
  map_mul' a b := Subtype.ext rfl
  map_add' a b := Subtype.ext rfl

theorem traceEquivFixedPart_apply_coe {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K))
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G) (O : Subring K) (f : ↥(traceNode K₀ O)) :
    ((traceEquivFixedPart G K₀ hK₀ O f : ↥(fixedPart G O)) : K) = ((f : ↥K₀) : K) := rfl

theorem fixedPart_le {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K)) (O : Subring K) :
    fixedPart G O ≤ O := fun _ hf => hf.1

@[reducible] noncomputable def subringAction {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K)) (B : Subring K)
    (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B) : MulSemiringAction ↥G ↥B where
  smul σ b := ⟨(σ : K ≃ₐ[k] K) (b : K), hBG σ σ.2 _ b.2⟩
  one_smul b := Subtype.ext (by change ((1 : ↥G) : K ≃ₐ[k] K) (b : K) = b; rw [OneMemClass.coe_one, AlgEquiv.one_apply])
  mul_smul σ τ b := Subtype.ext (by
    change ((σ * τ : ↥G) : K ≃ₐ[k] K) (b : K) = (σ : K ≃ₐ[k] K) ((τ : K ≃ₐ[k] K) (b : K))
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply])
  smul_zero σ := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((0 : ↥B) : K) = 0; simp)
  smul_add σ a b := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((a + b : ↥B) : K) = _; simp; rfl)
  smul_one σ := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((1 : ↥B) : K) = 1; simp)
  smul_mul σ a b := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((a * b : ↥B) : K) = _; simp; rfl)

theorem noetherian_and_finite_fixedPart {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (hRfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ r : R, σ (algebraMap R K r) = algebraMap R K r)
    (Bc : Subalgebra R K) (hBcG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bc → σ f ∈ Bc)
    (hft : Algebra.FiniteType R ↥Bc) :
    IsNoetherianRing ↥(fixedPart G Bc.toSubring) ∧
    ∀ (hle : fixedPart G Bc.toSubring ≤ Bc.toSubring),
      letI := (Subring.inclusion hle).toAlgebra; Module.Finite ↥(fixedPart G Bc.toSubring) ↥Bc.toSubring := by
  classical
  haveI := hGfin
  set A : Subring K := fixedPart G Bc.toSubring with hA
  set B : Subring K := Bc.toSubring with hB
  have hle0 : A ≤ B := fixedPart_le G Bc.toSubring
  have hBG' : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B := fun σ hσ f hf => hBcG σ hσ f hf

  let φB : R →+* ↥B :=
    { toFun := fun r => ⟨algebraMap R K r, Bc.algebraMap_mem r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let φA : R →+* ↥A :=
    { toFun := fun r => ⟨algebraMap R K r, ⟨Bc.algebraMap_mem r, fun σ hσ => hRfix σ hσ r⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }

  have main : ∀ (hle : A ≤ B), letI := (Subring.inclusion hle).toAlgebra;
      Module.Finite ↥A ↥B ∧ IsNoetherianRing ↥A := by
    intro hle
    letI algAB : Algebra ↥A ↥B := (Subring.inclusion hle).toAlgebra
    letI algRB : Algebra R ↥B := Bc.algebra
    letI algRA : Algebra R ↥A := φA.toAlgebra
    haveI : IsScalarTower R ↥A ↥B := IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext rfl)
    haveI : FaithfulSMul ↥A ↥B := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro a b hab
      exact Subtype.ext (congrArg (fun z : ↥B => (z : K)) hab)
    letI act : MulSemiringAction ↥G ↥B := subringAction G B hBG'
    haveI : Algebra.IsInvariant ↥A ↥B ↥G := by
      refine ⟨fun b hb => ?_⟩
      refine ⟨⟨(b : K), ⟨b.2, fun σ hσ => ?_⟩⟩, Subtype.ext rfl⟩
      exact congrArg (fun z : ↥B => (z : K)) (hb ⟨σ, hσ⟩)

    haveI : Algebra.FiniteType R ↥B := hft
    have hob51 := Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType R ↥A ↥B ↥G
    obtain ⟨h1, h2⟩ := hob51
    exact ⟨h1, Algebra.FiniteType.isNoetherianRing R ↥A⟩
  exact ⟨(main hle0).2, fun hle => (main hle).1⟩

open IsLocalRing

noncomputable def restrictSubalg {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (C : Subalgebra R K) (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ C → σ f ∈ C) : ↥C →+* ↥C where
  toFun b := ⟨σ (b : K), hσ _ b.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem restrictSubalg_apply_coe {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (C : Subalgebra R K) (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ C → σ f ∈ C) (b : ↥C) :
    ((restrictSubalg C σ hσ b : ↥C) : K) = σ (b : K) := rfl

theorem exists_invariant_split {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (C : Subalgebra R K) (hCG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ C → σ f ∈ C)
    (W X : ValuationSubring K) (hCW : ∀ b : ↥C, (b : K) ∈ W) (hCX : ∀ b : ↥C, (b : K) ∈ X)
    (y : Ideal ↥C) (hy : y.IsMaximal)
    (hyW : ∀ b : ↥C, b ∈ y ↔ ∃ hb : (b : K) ∈ W, (⟨(b : K), hb⟩ : ↥W) ∈ maximalIdeal ↥W)
    (hXy : ∀ b : ↥C, (∀ hb : (b : K) ∈ X, (⟨(b : K), hb⟩ : ↥X) ∈ maximalIdeal ↥X) → b ∈ y)
    (hXne : ∃ b : ↥C, b ∈ y ∧ ∀ hb : (b : K) ∈ X, (⟨(b : K), hb⟩ : ↥X) ∉ maximalIdeal ↥X) :
    ∃ f : K, f ∈ C ∧ (∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) ∧
      (∀ hfW : f ∈ W, (⟨f, hfW⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ hfX : f ∈ X, (⟨f, hfX⟩ : ↥X) ∉ maximalIdeal ↥X) := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G

  let 𝔮 : Ideal ↥C := (maximalIdeal ↥X).comap (toVal C X hCX)
  have hmem𝔮 : ∀ b : ↥C, b ∈ 𝔮 ↔ (⟨(b : K), hCX b⟩ : ↥X) ∈ maximalIdeal ↥X := fun b => Iff.rfl
  let I : ↥G → Ideal ↥C := fun σ => 𝔮.comap (restrictSubalg C (σ : K ≃ₐ[k] K) (hCG σ σ.2))
  have hIprime : ∀ σ : ↥G, (I σ).IsPrime := by
    intro σ
    haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
    exact Ideal.comap_isPrime _ _
  have hmemI : ∀ (σ : ↥G) (b : ↥C), b ∈ I σ ↔
      (⟨(σ : K ≃ₐ[k] K) (b : K), hCX ⟨_, hCG σ σ.2 _ b.2⟩⟩ : ↥X) ∈ maximalIdeal ↥X := fun σ b => Iff.rfl

  have h𝔮y : 𝔮 ≤ y := by
    intro b hb
    apply hXy b
    intro hb'
    exact (hmem𝔮 b).mp hb
  have h𝔮ne : 𝔮 ≠ y := by
    obtain ⟨b, hby, hbX⟩ := hXne
    intro h
    have : b ∈ 𝔮 := h ▸ hby
    exact hbX (hCX b) ((hmem𝔮 b).mp this)

  have hnot : ∀ σ : ↥G, ¬ (y ≤ I σ) := by
    intro σ hle

    have hsurj : Function.Surjective (restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2))) := by
      intro c
      refine ⟨⟨(σ : K ≃ₐ[k] K) (c : K), hCG σ σ.2 _ c.2⟩, Subtype.ext ?_⟩
      rw [restrictSubalg_apply_coe]
      change (σ : K ≃ₐ[k] K)⁻¹ ((σ : K ≃ₐ[k] K) (c : K)) = c
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    haveI hJmax : (y.comap (restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2)))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ hsurj
    have hJ𝔮 : y.comap (restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2))) ≤ 𝔮 := by
      intro c hc
      rw [Ideal.mem_comap] at hc
      have h1 := hle hc
      rw [hmemI] at h1
      rw [hmem𝔮]
      have heq : (σ : K ≃ₐ[k] K) (((restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2)) c : ↥C) : K)) = (c : K) := by
        rw [restrictSubalg_apply_coe, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
      have : (⟨(σ : K ≃ₐ[k] K) (((restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2)) c : ↥C) : K)), hCX ⟨_, hCG σ σ.2 _ (restrictSubalg C _ _ c).2⟩⟩ : ↥X) = ⟨(c : K), hCX c⟩ :=
        Subtype.ext heq
      rw [this] at h1
      exact h1
    have hJeq : y.comap (restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2))) = 𝔮 := by
      haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
      exact hJmax.eq_of_le (Ideal.IsPrime.ne_top ‹_›) hJ𝔮
    have h𝔮max : 𝔮.IsMaximal := hJeq ▸ hJmax
    exact h𝔮ne (h𝔮max.eq_of_le hy.ne_top h𝔮y)

  have havoid : ¬ ((y : Set ↥C) ⊆ ⋃ σ ∈ (↑(Finset.univ : Finset ↥G) : Set ↥G), (I σ : Set ↥C)) := by
    rw [Ideal.subset_union_prime (1 : ↥G) (1 : ↥G) (fun σ _ _ _ => hIprime σ)]
    rintro ⟨σ, -, hσ⟩
    exact hnot σ hσ
  rw [Set.not_subset] at havoid
  obtain ⟨b, hby, hbI⟩ := havoid
  have hbI' : ∀ σ : ↥G, (b : ↥C) ∉ I σ := by
    intro σ hσ
    apply hbI
    simp only [Finset.coe_univ, Set.mem_iUnion, Set.mem_univ, exists_true_left]
    exact ⟨σ, hσ⟩

  set b₀ : K := ((b : ↥C) : K) with hb₀
  have hσC : ∀ σ : ↥G, (σ : K ≃ₐ[k] K) b₀ ∈ C := fun σ => hCG σ σ.2 _ b.2
  refine ⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀, ?_, ?_, ?_, ?_⟩
  · exact prod_mem fun σ _ => hσC σ
  · intro ρ hρ
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨ρ, hρ⟩ : ↥G)) _ _ ?_
    intro σ
    simp [AlgEquiv.mul_apply]
  · intro hfW
    rw [mem_maximalIdeal_iff_lt, map_prod]

    have hb1 : W.valuation b₀ < 1 := by
      have hob52 := (hyW b).mp hby
      obtain ⟨hbW, hbm⟩ := hob52
      exact (mem_maximalIdeal_iff_lt W _ hbW).mp hbm
    have hle1 : ∀ σ : ↥G, W.valuation ((σ : K ≃ₐ[k] K) b₀) ≤ 1 :=
      fun σ => (W.valuation_le_one_iff _).mpr (hCW ⟨_, hσC σ⟩)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : ↥G))]
    have hrest : ∏ σ ∈ Finset.univ.erase (1 : ↥G), W.valuation ((σ : K ≃ₐ[k] K) b₀) ≤ 1 :=
      Finset.prod_le_one' fun σ _ => hle1 σ
    have h1 : W.valuation (((1 : ↥G) : K ≃ₐ[k] K) b₀) < 1 := by simpa using hb1
    rw [mul_comm]
    exact mul_lt_one_of_lt_of_le h1 hrest
  · intro hfX hm
    rw [mem_maximalIdeal_iff_lt, map_prod] at hm
    have hall : ∀ σ : ↥G, X.valuation ((σ : K ≃ₐ[k] K) b₀) = 1 := by
      intro σ
      have hnot' := hbI' σ
      rw [hmemI] at hnot'
      have hX := hCX ⟨_, hσC σ⟩
      rcases X.valuation_lt_one_or_eq_one ⟨_, hX⟩ with h | h
      · exact (hnot' ((mem_maximalIdeal_iff_lt X _ hX).mpr h)).elim
      · exact h
    rw [Finset.prod_congr rfl (fun σ _ => hall σ), Finset.prod_const_one] at hm
    exact lt_irrefl _ hm

open IsLocalRing

theorem valuation_eq_one_of_inv_mem {K : Type} [Field K] (W : ValuationSubring K) (O : Subring K)
    (hOW : ∀ f : K, f ∈ O → f ∈ W) (x : K) (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : ↥O)) : W.valuation x = 1 := by
  have hob53 := (isUnit_mk_iff O x hx).mp hu
  obtain ⟨y, hy, hxy⟩ := hob53
  have h1 : W.valuation x ≤ 1 := (W.valuation_le_one_iff _).mpr (hOW _ hx)
  have h2 : W.valuation y ≤ 1 := (W.valuation_le_one_iff _).mpr (hOW _ hy)
  have h3 : W.valuation x * W.valuation y = 1 := by rw [← map_mul, hxy, map_one]
  exact le_antisymm h1 (by
    by_contra h
    rw [not_le] at h
    have := mul_lt_one_of_lt_of_le h h2
    rw [h3] at this
    exact lt_irrefl _ this)

noncomputable def twistToVal {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (Bc : Subalgebra R K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ Bc → f ∈ W)
    (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ Bc → σ f ∈ Bc) : ↥Bc →+* ↥W where
  toFun b := ⟨σ (b : K), hBW _ (hσ _ b.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

noncomputable def toSubring' {K : Type} [Field K] {R : Type} [CommRing R] [Algebra R K]
    (Bc : Subalgebra R K) (O : Subring K) (hBO : ∀ f : K, f ∈ Bc → f ∈ O) : ↥Bc →+* ↥O where
  toFun b := ⟨(b : K), hBO _ b.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem exists_invariant_cosplit {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (Bc : Subalgebra R K) (hBcG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bc → σ f ∈ Bc)
    (O : Subring K) [IsLocalRing ↥O] (hBO : ∀ f : K, f ∈ Bc → f ∈ O)
    (hloc : ∀ f : K, f ∈ O ↔ ∃ g h : K, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)
    (hres : ∀ (f : K) (hf : f ∈ O), ∃ (a : R) (ha : algebraMap R K a ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha⟩))
    (W : ValuationSubring K) (hOW : ∀ f : K, f ∈ O → f ∈ W)
    (hstabW : ∀ σ : K ≃ₐ[k] K, σ ∈ G → (∀ f : K, f ∈ O → σ f ∈ W) → ∀ f : K, f ∈ W ↔ σ f ∈ W)
    (c : K) (hcO : c ∈ O) (hcu : ¬ IsUnit (⟨c, hcO⟩ : ↥O))
    (hcW : ∀ hc : c ∈ W, (⟨c, hc⟩ : ↥W) ∉ maximalIdeal ↥W) :
    ∃ (f : K) (hfO : f ∈ O), (∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) ∧ ¬ IsUnit (⟨f, hfO⟩ : ↥O) ∧
      (∀ hfW : f ∈ W, (⟨f, hfW⟩ : ↥W) ∉ maximalIdeal ↥W) := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  have hBW : ∀ f : K, f ∈ Bc → f ∈ W := fun f hf => hOW _ (hBO _ hf)

  let 𝔮 : Ideal ↥Bc := (maximalIdeal ↥O).comap (toSubring' Bc O hBO)
  have hmem𝔮 : ∀ b : ↥Bc, b ∈ 𝔮 ↔ ¬ IsUnit (⟨(b : K), hBO _ b.2⟩ : ↥O) := by
    intro b
    show (toSubring' Bc O hBO b) ∈ maximalIdeal ↥O ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact Iff.rfl
  let I : ↥G → Ideal ↥Bc := fun σ => (maximalIdeal ↥W).comap (twistToVal Bc W hBW (σ : K ≃ₐ[k] K) (hBcG σ σ.2))
  have hIprime : ∀ σ : ↥G, (I σ).IsPrime := fun σ => Ideal.comap_isPrime _ _
  have hmemI : ∀ (σ : ↥G) (b : ↥Bc), b ∈ I σ ↔
      (⟨(σ : K ≃ₐ[k] K) (b : K), hBW _ (hBcG σ σ.2 _ b.2)⟩ : ↥W) ∈ maximalIdeal ↥W := fun σ b => Iff.rfl

  have h𝔮max : 𝔮.IsMaximal := by
    haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one), ?_⟩
    intro J x hJ hx hxJ
    rw [hmem𝔮, not_not] at hx
    have hob54 := (isUnit_mk_iff O _ (hBO _ x.2)).mp hx
    obtain ⟨y, hy, hxy⟩ := hob54
    have hob55 := hres y hy
    obtain ⟨a, ha, hna⟩ := hob55

    have hxa : (1 : ↥Bc) - x * algebraMap R ↥Bc a ∈ 𝔮 := by
      rw [hmem𝔮]
      intro hu
      apply hna
      have heq : ((⟨y, hy⟩ : ↥O) - ⟨_, ha⟩) * ⟨(x : K), hBO _ x.2⟩ = ⟨(((1 : ↥Bc) - x * algebraMap R ↥Bc a : ↥Bc) : K), hBO _ ((1 : ↥Bc) - x * algebraMap R ↥Bc a).2⟩ := by
        apply Subtype.ext
        show (y - algebraMap R K a) * (x : K) = (((1 : ↥Bc) - x * algebraMap R ↥Bc a : ↥Bc) : K)
        rw [Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
        have : (x : K) * y = 1 := hxy
        linear_combination this
      have h2 : IsUnit (((⟨y, hy⟩ : ↥O) - ⟨_, ha⟩) * ⟨(x : K), hBO _ x.2⟩) := by rw [heq]; exact hu
      exact isUnit_of_mul_isUnit_left h2
    have h3 : x * algebraMap R ↥Bc a ∈ J := J.mul_mem_right _ hxJ
    have h4 : (1 : ↥Bc) - x * algebraMap R ↥Bc a ∈ J := hJ hxa
    have : (1 : ↥Bc) = ((1 : ↥Bc) - x * algebraMap R ↥Bc a) + x * algebraMap R ↥Bc a := by ring
    rw [this]
    exact J.add_mem h4 h3

  have hob56 := (hloc c).mp hcO
  obtain ⟨g₀, h₀, hg₀, hh₀, hh₀u, hch⟩ := hob56
  have hvh₀ : W.valuation h₀ = 1 := valuation_eq_one_of_inv_mem W O hOW h₀ (hBO _ hh₀) (hh₀u _)
  have hvc : W.valuation c = 1 := by
    have h1 : W.valuation c ≤ 1 := (W.valuation_le_one_iff _).mpr (hOW _ hcO)
    rcases W.valuation_lt_one_or_eq_one ⟨c, hOW _ hcO⟩ with h | h
    · exact (hcW (hOW _ hcO) ((mem_maximalIdeal_iff_lt W c _).mpr h)).elim
    · exact h
  have hvg₀ : W.valuation g₀ = 1 := by rw [← hch, map_mul, hvc, hvh₀, one_mul]
  have hg₀𝔮 : (⟨g₀, hg₀⟩ : ↥Bc) ∈ 𝔮 := by
    rw [hmem𝔮]
    intro hu
    apply hcu
    have heq : (⟨g₀, hBO _ hg₀⟩ : ↥O) = ⟨c, hcO⟩ * ⟨h₀, hBO _ hh₀⟩ := Subtype.ext hch.symm
    rw [heq] at hu
    exact isUnit_of_mul_isUnit_left hu

  have hnot : ∀ σ : ↥G, ¬ (𝔮 ≤ I σ) := by
    intro σ hle
    have heq : 𝔮 = I σ := h𝔮max.eq_of_le (Ideal.IsPrime.ne_top (hIprime σ)) hle

    have hinto : ∀ f : K, f ∈ O → (σ : K ≃ₐ[k] K) f ∈ W := by
      intro f hf
      have hob57 := (hloc f).mp hf
      obtain ⟨g, h, hg, hh, hhu, hfh⟩ := hob57
      have hhI : (⟨h, hh⟩ : ↥Bc) ∉ I σ := by
        rw [← heq, hmem𝔮, not_not]; exact hhu _
      rw [hmemI] at hhI

      have hσhW : (σ : K ≃ₐ[k] K) h ∈ W := hBW _ (hBcG σ σ.2 _ hh)
      have hσhu : IsUnit (⟨(σ : K ≃ₐ[k] K) h, hσhW⟩ : ↥W) := by
        rcases W.valuation_lt_one_or_eq_one ⟨_, hσhW⟩ with h1 | h1
        · exact (hhI ((mem_maximalIdeal_iff_lt W _ _).mpr h1)).elim
        · exact (W.valuation_eq_one_iff _).mpr h1
      have hob58 := hσhu
      obtain ⟨u, hu⟩ := hob58
      have hyy : ((((u⁻¹ : (↥W)ˣ) : ↥W)) : K) ∈ W := ((u⁻¹ : (↥W)ˣ) : ↥W).2
      have hyy1 : (σ : K ≃ₐ[k] K) h * ((((u⁻¹ : (↥W)ˣ) : ↥W)) : K) = 1 := by
        have e := congrArg (fun z : ↥W => (z : K)) u.mul_inv
        rw [hu] at e
        simpa using e
      set yy : K := ((((u⁻¹ : (↥W)ˣ) : ↥W)) : K) with hyydef
      have : (σ : K ≃ₐ[k] K) f = (σ : K ≃ₐ[k] K) g * yy := by
        have e : (σ : K ≃ₐ[k] K) f * (σ : K ≃ₐ[k] K) h = (σ : K ≃ₐ[k] K) g := by rw [← map_mul, hfh]
        calc (σ : K ≃ₐ[k] K) f = (σ : K ≃ₐ[k] K) f * ((σ : K ≃ₐ[k] K) h * yy) := by rw [hyy1, mul_one]
          _ = (σ : K ≃ₐ[k] K) g * yy := by rw [← mul_assoc, e]
      rw [this]
      exact W.mul_mem _ _ (hBW _ (hBcG σ σ.2 _ hg)) hyy
    have hW := hstabW σ σ.2 hinto

    have h1 : (⟨g₀, hg₀⟩ : ↥Bc) ∈ I σ := heq ▸ hg₀𝔮
    rw [hmemI] at h1
    have h2 := (mem_maximalIdeal_iff_lt W _ _).mp h1

    have hg₀W : g₀ ∈ W := hBW _ hg₀
    have hg₀ne : g₀ ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvg₀; exact zero_ne_one hvg₀
    have hinvW : g₀⁻¹ ∈ W := by
      rw [← W.valuation_le_one_iff, map_inv₀, hvg₀, inv_one]
    have hσinv : (σ : K ≃ₐ[k] K) g₀⁻¹ ∈ W := (hW _).mp hinvW
    have h3 : W.valuation ((σ : K ≃ₐ[k] K) g₀) * W.valuation ((σ : K ≃ₐ[k] K) g₀⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hg₀ne, map_one, map_one]
    have h4 : W.valuation ((σ : K ≃ₐ[k] K) g₀⁻¹) ≤ 1 := (W.valuation_le_one_iff _).mpr hσinv
    have := mul_lt_one_of_lt_of_le h2 h4
    rw [h3] at this
    exact lt_irrefl _ this

  have havoid : ¬ ((𝔮 : Set ↥Bc) ⊆ ⋃ σ ∈ (↑(Finset.univ : Finset ↥G) : Set ↥G), (I σ : Set ↥Bc)) := by
    rw [Ideal.subset_union_prime (1 : ↥G) (1 : ↥G) (fun σ _ _ _ => hIprime σ)]
    rintro ⟨σ, -, hσ⟩
    exact hnot σ hσ
  rw [Set.not_subset] at havoid
  obtain ⟨b, hb𝔮, hbI⟩ := havoid
  have hbI' : ∀ σ : ↥G, (b : ↥Bc) ∉ I σ := by
    intro σ hσ
    apply hbI
    simp only [Finset.coe_univ, Set.mem_iUnion, Set.mem_univ, exists_true_left]
    exact ⟨σ, hσ⟩
  set b₀ : K := ((b : ↥Bc) : K) with hb₀
  have hσBc : ∀ σ : ↥G, (σ : K ≃ₐ[k] K) b₀ ∈ Bc := fun σ => hBcG σ σ.2 _ b.2
  have hprodO : (∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀) ∈ O := prod_mem fun σ _ => hBO _ (hσBc σ)
  refine ⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀, hprodO, ?_, ?_, ?_⟩
  · intro ρ hρ
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨ρ, hρ⟩ : ↥G)) _ _ ?_
    intro σ
    simp [AlgEquiv.mul_apply]
  · intro hu
    have hbu : ¬ IsUnit (⟨b₀, hBO _ b.2⟩ : ↥O) := (hmem𝔮 b).mp hb𝔮
    apply hbu
    have hsplit : (⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀, hprodO⟩ : ↥O) =
        ⟨b₀, hBO _ b.2⟩ * ⟨∏ σ ∈ Finset.univ.erase (1 : ↥G), (σ : K ≃ₐ[k] K) b₀,
          prod_mem fun σ _ => hBO _ (hσBc σ)⟩ := by
      apply Subtype.ext
      show (∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀) = b₀ * ∏ σ ∈ Finset.univ.erase (1 : ↥G), (σ : K ≃ₐ[k] K) b₀
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : ↥G)), mul_comm]
      simp
    rw [hsplit] at hu
    exact isUnit_of_mul_isUnit_left hu
  · intro hfW hm
    rw [mem_maximalIdeal_iff_lt, map_prod] at hm
    have hall : ∀ σ : ↥G, W.valuation ((σ : K ≃ₐ[k] K) b₀) = 1 := by
      intro σ
      have hnot' := hbI' σ
      rw [hmemI] at hnot'
      have hX := hBW _ (hσBc σ)
      rcases W.valuation_lt_one_or_eq_one ⟨_, hX⟩ with h | h
      · exact (hnot' ((mem_maximalIdeal_iff_lt W _ hX).mpr h)).elim
      · exact h
    rw [Finset.prod_congr rfl (fun σ _ => hall σ), Finset.prod_const_one] at hm
    exact lt_irrefl _ hm

@[reducible] noncomputable def subalgAction' {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B) : MulSemiringAction ↥G ↥B where
  smul σ b := ⟨(σ : K ≃ₐ[k] K) (b : K), hBG σ σ.2 _ b.2⟩
  one_smul b := Subtype.ext (by change ((1 : ↥G) : K ≃ₐ[k] K) (b : K) = b; rw [OneMemClass.coe_one, AlgEquiv.one_apply])
  mul_smul σ τ b := Subtype.ext (by
    change ((σ * τ : ↥G) : K ≃ₐ[k] K) (b : K) = (σ : K ≃ₐ[k] K) ((τ : K ≃ₐ[k] K) (b : K))
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply])
  smul_zero σ := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((0 : ↥B) : K) = 0; simp)
  smul_add σ a b := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((a + b : ↥B) : K) = _; simp; rfl)
  smul_one σ := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((1 : ↥B) : K) = 1; simp)
  smul_mul σ a b := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((a * b : ↥B) : K) = _; simp; rfl)

def fixedSubalg {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hRfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ r : R, σ (algebraMap R K r) = algebraMap R K r)
    (B : Subalgebra R K) : Subalgebra R K where
  carrier := {f | f ∈ B ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f}
  mul_mem' := fun {a b} ha hb => ⟨B.mul_mem ha.1 hb.1, fun σ hσ => by rw [map_mul, ha.2 σ hσ, hb.2 σ hσ]⟩
  one_mem' := ⟨B.one_mem, fun σ _ => map_one σ⟩
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, fun σ hσ => by rw [map_add, ha.2 σ hσ, hb.2 σ hσ]⟩
  zero_mem' := ⟨B.zero_mem, fun σ _ => map_zero σ⟩
  algebraMap_mem' := fun r => ⟨B.algebraMap_mem r, fun σ hσ => hRfix σ hσ r⟩

theorem mem_fixedSubalg {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hRfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ r : R, σ (algebraMap R K r) = algebraMap R K r)
    (B : Subalgebra R K) (f : K) :
    f ∈ fixedSubalg G hRfix B ↔ f ∈ B ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f := Iff.rfl

theorem finiteType_fixedSubalg {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (hRfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ r : R, σ (algebraMap R K r) = algebraMap R K r)
    (B : Subalgebra R K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (hft : Algebra.FiniteType R ↥B) :
    Algebra.FiniteType R ↥(fixedSubalg G hRfix B) := by
  classical
  haveI := hGfin
  set A : Subalgebra R K := fixedSubalg G hRfix B with hA
  have hle : A ≤ B := fun _ hf => hf.1
  letI algAB : Algebra ↥A ↥B := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower R ↥A ↥B := IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext rfl)
  haveI : FaithfulSMul ↥A ↥B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact Subtype.ext (congrArg (fun z : ↥B => (z : K)) hab)
  letI act : MulSemiringAction ↥G ↥B := subalgAction' G B hBG
  haveI : Algebra.IsInvariant ↥A ↥B ↥G := by
    refine ⟨fun b hb => ?_⟩
    refine ⟨⟨(b : K), ⟨b.2, fun σ hσ => ?_⟩⟩, Subtype.ext rfl⟩
    exact congrArg (fun z : ↥B => (z : K)) (hb ⟨σ, hσ⟩)
  haveI := hft
  exact (Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType R ↥A ↥B ↥G).2

theorem exists_finset_trace_eq_closure {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (hRfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ r : R, σ (algebraMap R K r) = algebraMap R K r)
    (B : Subalgebra R K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (hft : Algebra.FiniteType R ↥B) :
    ∃ T : Finset ↥K₀, B.toSubring.comap (algebraMap ↥K₀ K) =
      Subring.closure ({f : ↥K₀ | ∃ r : R, (f : K) = algebraMap R K r} ∪ ↑T) := by
  classical
  haveI := hGfin
  have hfix : ∀ f : K, f ∈ K₀ ↔ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f := by
    intro f; rw [hK₀, IntermediateField.mem_fixedField_iff]
  have hob59 := (finiteType_fixedSubalg G hGfin hRfix B hBG hft).out
  obtain ⟨s, hs⟩ := hob59

  have hsK₀ : ∀ b : ↥(fixedSubalg G hRfix B), ((b : K)) ∈ K₀ := fun b => (hfix _).mpr b.2.2
  let emb : ↥(fixedSubalg G hRfix B) → ↥K₀ := fun b => ⟨(b : K), hsK₀ b⟩
  refine ⟨s.image emb, ?_⟩
  apply le_antisymm
  ·
    intro f hf
    rw [Subring.mem_comap] at hf
    have hfA : (f : K) ∈ fixedSubalg G hRfix B := ⟨hf, (hfix _).mp f.2⟩
    have htop : (⟨(f : K), hfA⟩ : ↥(fixedSubalg G hRfix B)) ∈ Algebra.adjoin R (s : Set ↥(fixedSubalg G hRfix B)) := by
      rw [hs]; trivial

    let φ : ↥(fixedSubalg G hRfix B) →+* ↥K₀ :=
      { toFun := emb
        map_one' := Subtype.ext (by simp [emb])
        map_mul' := fun a b => Subtype.ext (by simp [emb])
        map_zero' := Subtype.ext (by simp [emb])
        map_add' := fun a b => Subtype.ext (by simp [emb]) }
    have hφ : ∀ b, φ b = emb b := fun _ => rfl
    have hmem : φ ⟨(f : K), hfA⟩ ∈ (Algebra.adjoin R (s : Set ↥(fixedSubalg G hRfix B))).toSubring.map φ :=
      Subring.mem_map.mpr ⟨_, htop, rfl⟩
    have heq : φ ⟨(f : K), hfA⟩ = f := Subtype.ext rfl
    rw [heq, Algebra.adjoin_eq_ring_closure, RingHom.map_closure] at hmem
    refine Subring.closure_mono ?_ hmem
    rintro x ⟨y, hy, rfl⟩
    rcases hy with ⟨r, rfl⟩ | hy
    · left; exact ⟨r, rfl⟩
    · right
      rw [Finset.coe_image]
      exact ⟨y, hy, rfl⟩
  · rw [Subring.closure_le]
    rintro f (⟨r, hr⟩ | hf)
    · show f ∈ B.toSubring.comap (algebraMap ↥K₀ K)
      rw [Subring.mem_comap, Subalgebra.mem_toSubring]
      change (f : K) ∈ B
      rw [hr]; exact B.algebraMap_mem r
    · rw [Finset.mem_coe, Finset.mem_image] at hf
      obtain ⟨b, -, rfl⟩ := hf
      show emb b ∈ B.toSubring.comap (algebraMap ↥K₀ K)
      rw [Subring.mem_comap, Subalgebra.mem_toSubring]
      exact b.2.1

theorem isUnit_fixedPart_iff_isUnit_trace {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K))
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G) (O : Subring K)
    (f : ↥K₀) (hf : (f : K) ∈ fixedPart G O) (hf' : f ∈ traceNode K₀ O) :
    IsUnit (⟨(f : K), hf⟩ : ↥(fixedPart G O)) ↔ IsUnit (⟨f, hf'⟩ : ↥(traceNode K₀ O)) := by
  have hfix : ∀ x : K, x ∈ K₀ ↔ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ x = x := by
    intro x; rw [hK₀, IntermediateField.mem_fixedField_iff]
  rw [isUnit_mk_iff, isUnit_mk_iff]
  constructor
  · rintro ⟨y, hy, hfy⟩
    exact ⟨⟨y, (hfix y).mpr hy.2⟩, hy.1, Subtype.ext hfy⟩
  · rintro ⟨y, hy, hfy⟩
    exact ⟨(y : K), ⟨hy, (hfix _).mp y.2⟩, congrArg (fun z : ↥K₀ => (z : K)) hfy⟩

theorem common_chart_trace {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (Bc : Subalgebra R K) (hBcG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bc → σ f ∈ Bc)
    [DecidableEq (Subring ↥K₀)] (ends : Finset (Subring K))
    (hOlocal : ∀ O ∈ ends, IsLocalRing ↥O)
    (hBcO : ∀ O ∈ ends, (∀ f : K, f ∈ Bc → f ∈ O) ∧
      (∀ f : K, f ∈ O ↔ ∃ g h : K, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) :
    ∀ O ∈ ends.image (traceNode K₀), (∀ f : ↥K₀, f ∈ Bc.toSubring.comap (algebraMap ↥K₀ K) → f ∈ O) ∧
      (∀ f : ↥K₀, f ∈ O ↔ ∃ g h : ↥K₀, g ∈ Bc.toSubring.comap (algebraMap ↥K₀ K) ∧ h ∈ Bc.toSubring.comap (algebraMap ↥K₀ K) ∧
        (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) := by
  classical
  have hfix : ∀ x : K, x ∈ K₀ ↔ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ x = x := by
    intro x; rw [hK₀, IntermediateField.mem_fixedField_iff]
  intro O hO
  have hob60 := Finset.mem_image.mp hO
  obtain ⟨Õ, hÕ, rfl⟩ := hob60
  haveI : IsLocalRing ↥Õ := hOlocal Õ hÕ
  have hob61 := hBcO Õ hÕ
  obtain ⟨hBÕ, hloc⟩ := hob61
  refine ⟨fun f hf => hBÕ _ hf, ?_⟩
  have hob62 := S3C4Pernode.mem_iff_exists_frac_invariant G hGfin Bc.toSubring
    (fun σ hσ f hf => hBcG σ hσ f hf) (fixedPart G Bc.toSubring) (fun f => Iff.rfl) Õ (fun f hf => hBÕ _ hf) hloc
    (fixedPart G Õ) (fun f => Iff.rfl)
  obtain ⟨-, hunits, hfrac⟩ := hob62
  intro f
  have hfK : (f : K) ∈ fixedPart G Õ ↔ f ∈ traceNode K₀ Õ := by
    rw [mem_fixedPart, mem_traceNode]
    exact ⟨fun h => h.1, fun h => ⟨h, (hfix _).mp f.2⟩⟩
  rw [← hfK, hfrac]
  constructor
  · rintro ⟨g, h, hg, hh, hhu, hfh⟩
    refine ⟨⟨g, (hfix g).mpr hg.2⟩, ⟨h, (hfix h).mpr hh.2⟩, hg.1, hh.1, ?_, Subtype.ext hfh⟩
    intro hh'
    have hhO : h ∈ fixedPart G Õ := ⟨hh', hh.2⟩
    exact (isUnit_fixedPart_iff_isUnit_trace G K₀ hK₀ Õ ⟨h, (hfix h).mpr hh.2⟩ hhO hh').mp (hhu hhO)
  · rintro ⟨g, h, hg, hh, hhu, hfh⟩
    refine ⟨(g : K), (h : K), ⟨hg, (hfix _).mp g.2⟩, ⟨hh, (hfix _).mp h.2⟩, ?_, congrArg (fun z : ↥K₀ => (z : K)) hfh⟩
    intro hh'
    exact (isUnit_fixedPart_iff_isUnit_trace G K₀ hK₀ Õ h hh' hh'.1).mpr (hhu hh'.1)

theorem n7_lift
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (ℓ' : ℕ) [Fact ℓ'.Prime]
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) [Fact (jℓ ≠ 0)]
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hy : y.IsMaximal)
    (hover :
    (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ)
        (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
      ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
        (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
            algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hjK : ModularCurve.qExpand ↥k₀ ℓ' (ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) ∈ Kℓ)
    (hjC : (⟨ModularCurve.qExpand ↥k₀ ℓ' (ModularCurve.coeffEmb ↥k₀ ModularCurve.jq), hjK⟩ : ↥Kℓ) ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ))
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha₀y : (⟨(⟨ModularCurve.qExpand ↥k₀ ℓ' (ModularCurve.coeffEmb ↥k₀ ModularCurve.jq), hjK⟩ : ↥Kℓ), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y) :
    ∃ hjR : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
      (R₀.residue ⟨_, hjR⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ∧
      ∀ ha₀ : ((a₀ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A,
        residue A ⟨((a₀ : ↥k₀) : (AlgebraicClosure ℚ)), ha₀⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hjR⟩) := by
  have hob63 := jq_residue_package q M' A W hW R₀ hR₀ s k₀ hκ
  obtain ⟨hjR, hjs, c, hc, hcres⟩ := hob63
  refine ⟨hjR, hjs, fun ha₀ => ?_⟩

  have hyc := hover jq (modularFunctionField_le_full M' (jq_mem M')) hjR (fun P h => h) hjs hjK hjC c hc hcres
  have hdiff : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) (a₀ - ⟨c, hc⟩) ∈ y := by
    have : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) (a₀ - ⟨c, hc⟩) =
        ((⟨(⟨ModularCurve.qExpand ↥k₀ ℓ' (ModularCurve.coeffEmb ↥k₀ ModularCurve.jq), hjK⟩ : ↥Kℓ), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩) -
        ((⟨(⟨ModularCurve.qExpand ↥k₀ ℓ' (ModularCurve.coeffEmb ↥k₀ ModularCurve.jq), hjK⟩ : ↥Kℓ), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀) := by
      rw [map_sub]; ring
    rw [this]
    exact y.sub_mem hyc ha₀y
  have hnu : ¬ IsUnit (a₀ - ⟨c, hc⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    intro hu
    apply hy.ne_top
    exact y.eq_top_of_isUnit_mem hdiff (hu.map _)

  have hnuA : ¬ IsUnit ((⟨((a₀ : ↥k₀) : (AlgebraicClosure ℚ)), ha₀⟩ : ↥A) - ⟨(c : (AlgebraicClosure ℚ)), hc⟩) := by
    intro hu
    apply hnu
    obtain ⟨u, hu⟩ := hu

    have hprod : (((a₀ : ↥k₀) : AlgebraicClosure ℚ) - (c : AlgebraicClosure ℚ)) * ((((u⁻¹ : (↥A)ˣ) : ↥A)) : AlgebraicClosure ℚ) = 1 := by
      have e := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) u.mul_inv
      rw [hu] at e
      simpa using e
    have hne : (((a₀ : ↥k₀) : AlgebraicClosure ℚ) - (c : AlgebraicClosure ℚ)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
    have hinv_eq : ((((u⁻¹ : (↥A)ˣ) : ↥A)) : AlgebraicClosure ℚ) = ((((a₀ : ↥k₀) - c)⁻¹ : ↥k₀) : AlgebraicClosure ℚ) := by
      rw [eq_inv_of_mul_eq_one_right hprod]; push_cast; ring_nf
    have hinvA : ((((a₀ : ↥k₀) - c)⁻¹ : ↥k₀) : AlgebraicClosure ℚ) ∈ A := hinv_eq ▸ ((u⁻¹ : (↥A)ˣ) : ↥A).2
    have hne' : ((a₀ : ↥k₀) - c) ≠ 0 := by
      intro h0; apply hne
      have e := congrArg (fun z : ↥k₀ => (z : AlgebraicClosure ℚ)) h0
      push_cast at e
      exact e
    refine isUnit_iff_exists_inv.mpr ⟨⟨((a₀ : ↥k₀) - c)⁻¹, hinvA⟩, Subtype.ext ?_⟩
    show ((a₀ : ↥k₀) - c) * ((a₀ : ↥k₀) - c)⁻¹ = 1
    exact mul_inv_cancel₀ hne'
  have hm : ((⟨((a₀ : ↥k₀) : (AlgebraicClosure ℚ)), ha₀⟩ : ↥A) - ⟨(c : (AlgebraicClosure ℚ)), hc⟩) ∈ maximalIdeal ↥A :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnuA
  rw [← hcres, ← sub_eq_zero, ← map_sub]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hm

theorem completion_pack
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (n : ℕ) (hnq : n ∣ q + 1) :
    ∃ (_ : IsDomain (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
      (_ : IsDiscreteValuationRing (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
      (_ : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
      maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) =
        Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩} ∧
      IsUnit ((n : ℕ) : AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
  haveI := hdvr
  have hirr : Irreducible (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hunif
  obtain ⟨i1, i2, i3, hirr', -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨π₀, hπ⟩ hirr
  haveI := i1; haveI := i2; haveI := i3
  refine ⟨i1, i2, i3, hirr'.maximalIdeal_eq, ?_⟩

  have hqnu : ¬ IsUnit ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA

    have hinvA : ((((u⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) : AlgebraicClosure ℚ) ∈ A := ((u⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).2
    have hprod : ((q : ℕ) : AlgebraicClosure ℚ) * ((((u⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) : AlgebraicClosure ℚ) = 1 := by
      have e := congrArg (fun z : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) => ((z : ↥k₀) : AlgebraicClosure ℚ)) u.mul_inv
      rw [hu] at e
      simpa using e
    have h2 : A.valuation ((((u⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr hinvA
    have := mul_lt_one_of_lt_of_le hq1 h2
    rw [← map_mul, hprod, map_one] at this
    exact lt_irrefl _ this
  have hq1u : IsUnit ((q + 1 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    by_contra hnu
    have h1 : ((q + 1 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2 : ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := (IsLocalRing.mem_maximalIdeal _).mpr hqnu
    have h3 : (1 : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
      have : (1 : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = ((q + 1 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) - ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by push_cast; ring
      rw [this]
      exact (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).sub_mem h1 h2
    exact (maximalIdeal.isMaximal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hnu : IsUnit ((n : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hnq) hq1u
  have := hnu.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
  rwa [map_natCast] at this

end S3C4Glue

namespace S3C4Glue

open IsLocalRing

theorem ne_zero_of_isUnit_mk {K : Type} [Field K] (O : Subring K) (h : K) (hh : h ∈ O) (hu : IsUnit (⟨h, hh⟩ : ↥O)) : h ≠ 0 := by
  intro h0
  obtain ⟨u, hu⟩ := hu
  have e := congrArg (fun z : ↥O => (z : K)) u.mul_inv
  rw [hu] at e
  simp [h0] at e

theorem exists_frac_invariants {k K : Type} [Field k] [Field K] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (Bx : Subring K) (hBxG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bx → σ f ∈ Bx)
    (Õ : Subring K) (hBxO : Bx ≤ Õ)
    (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)
    (hfracO : ∀ f : K, ∃ a b : K, a ∈ Õ ∧ b ∈ Õ ∧ b ≠ 0 ∧ f * b = a) :
    ∀ f : ↥K₀, ∃ g h : ↥K₀, (g : K) ∈ Bx ∧ (h : K) ∈ Bx ∧ h ≠ 0 ∧ f * h = g := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  have hfix : ∀ x : K, x ∈ K₀ ↔ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ x = x := by
    intro x; rw [hK₀, IntermediateField.mem_fixedField_iff]

  have hfracB : ∀ f : K, ∃ g h : K, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g := by
    intro f
    have hob64 := hfracO f
    obtain ⟨a, b, ha, hb, hb0, hfb⟩ := hob64
    have hob65 := (hloc a).mp ha
    obtain ⟨g₁, h₁, hg₁, hh₁, hu₁, e₁⟩ := hob65
    have hob66 := (hloc b).mp hb
    obtain ⟨g₂, h₂, hg₂, hh₂, hu₂, e₂⟩ := hob66
    have hh₁0 : h₁ ≠ 0 := ne_zero_of_isUnit_mk Õ h₁ (hBxO hh₁) (hu₁ (hBxO hh₁))
    have hh₂0 : h₂ ≠ 0 := ne_zero_of_isUnit_mk Õ h₂ (hBxO hh₂) (hu₂ (hBxO hh₂))
    have hg₂0 : g₂ ≠ 0 := by rw [← e₂]; exact mul_ne_zero hb0 hh₂0
    refine ⟨g₁ * h₂, h₁ * g₂, Bx.mul_mem hg₁ hh₂, Bx.mul_mem hh₁ hg₂, mul_ne_zero hh₁0 hg₂0, ?_⟩

    calc f * (h₁ * g₂) = (f * b) * h₁ * h₂ := by rw [← e₂]; ring
      _ = g₁ * h₂ := by rw [hfb, ← e₁]

  intro f
  have hob67 := hfracB (f : K)
  obtain ⟨g, h, hg, hh, hh0, e⟩ := hob67

  set D : K := ∏ σ : ↥G, (σ : K ≃ₐ[k] K) h with hD
  have hDB : D ∈ Bx := Subring.prod_mem _ (fun σ _ => hBxG σ σ.2 h hh)
  have hD0 : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro σ _
    exact (map_ne_zero_iff (σ : K ≃ₐ[k] K).toRingHom (σ : K ≃ₐ[k] K).injective).mpr hh0
  have hDfix : ∀ ρ : K ≃ₐ[k] K, ρ ∈ G → ρ D = D := by
    intro ρ hρ
    rw [hD, map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨ρ, hρ⟩ : ↥G)) _ _ (fun σ => by simp [AlgEquiv.mul_apply])

  have hsplit : D = h * ∏ σ ∈ (Finset.univ.erase (1 : ↥G)), (σ : K ≃ₐ[k] K) h := by
    rw [hD, ← Finset.mul_prod_erase Finset.univ (fun σ : ↥G => (σ : K ≃ₐ[k] K) h) (Finset.mem_univ (1 : ↥G))]
    rfl
  have hND : (f : K) * D ∈ Bx := by
    rw [hsplit, ← mul_assoc, e]
    exact Bx.mul_mem hg (Subring.prod_mem _ (fun σ _ => hBxG σ σ.2 h hh))
  have hNfix : ∀ ρ : K ≃ₐ[k] K, ρ ∈ G → ρ ((f : K) * D) = (f : K) * D := by
    intro ρ hρ; rw [map_mul, hDfix ρ hρ, (hfix _).mp f.2 ρ hρ]
  refine ⟨⟨(f : K) * D, (hfix _).mpr hNfix⟩, ⟨D, (hfix _).mpr hDfix⟩, hND, hDB, ?_, Subtype.ext rfl⟩
  exact fun h0 => hD0 (congrArg (fun z : ↥K₀ => (z : K)) h0)

theorem mem_maximalIdeal_comap_iff {k K : Type} [Field k] [Field K] [Algebra k K]
    (K₀ : IntermediateField k K) (V : ValuationSubring K) (f : ↥K₀) (hf : f ∈ V.comap (algebraMap ↥K₀ K)) :
    (⟨f, hf⟩ : ↥(V.comap (algebraMap ↥K₀ K))) ∈ IsLocalRing.maximalIdeal ↥(V.comap (algebraMap ↥K₀ K)) ↔
      (⟨(f : K), hf⟩ : ↥V) ∈ IsLocalRing.maximalIdeal ↥V := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  rw [isUnit_mk_iff (V.comap (algebraMap ↥K₀ K)).toSubring f hf]
  rw [isUnit_mk_iff V.toSubring (f : K) hf]
  constructor
  · rintro ⟨y, hy, hfy⟩
    exact ⟨(y : K), hy, by exact_mod_cast congrArg (fun z : ↥K₀ => (z : K)) hfy⟩
  · rintro ⟨y, hy, hfy⟩
    have hf0 : (f : K) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hfy; exact zero_ne_one hfy
    have hyeq : y = ((f⁻¹ : ↥K₀) : K) := by
      rw [eq_inv_of_mul_eq_one_right hfy]; push_cast; rfl
    refine ⟨f⁻¹, ?_, ?_⟩
    · show ((f⁻¹ : ↥K₀) : K) ∈ V; rw [← hyeq]; exact hy
    · exact mul_inv_cancel₀ (fun h0 => hf0 (by rw [h0]; rfl))

end S3C4Glue

open S3C4Glue in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M : ¬ ℓ' ∣ M')
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)]
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)

    (hover :
    (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ)
        (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
      ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
        (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
            algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hjK : ModularCurve.jqNModC ↥k₀ (q * ℓ') ∈ Kℓ)
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (Wt : ValuationSubring ↥Kℓ)
    (hR3d : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ↔ ∃ hb : (b : ↥Kℓ) ∈ Wt, (⟨(b : ↥Kℓ), hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt)
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ)
    (K₀ : IntermediateField ↥k₀ ↥Kℓ) (hK₀ : K₀ = IntermediateField.fixedField G)
    (Õ : Subring ↥Kℓ) (hCO : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Õ) (hOW : ∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wt)
    (O : Subring ↥K₀) (hOdef : O = Õ.comap (algebraMap ↥K₀ ↥Kℓ))
    (Wx : ValuationSubring ↥Kℓ)
    (hOWx : ∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx)
    (hCWx : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx)
    (hVA : ∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x)
    (hcentre : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y)
    (hne : ∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx)
    (hVj : ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
      (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
        ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :
    ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M'))) →
        ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ), ∃ hF : (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀,
          (⟨_, hF⟩ : ↥K₀) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ) ∧
          (∀ hW : (⟨_, hF⟩ : ↥K₀) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hW⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)) ↔
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
          ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            (⟨_, hF⟩ : ↥K₀) ∈ O ∧
            ∀ (hO' : (⟨_, hF⟩ : ↥K₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥K₀ c ∈ O),
              residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
              ¬ IsUnit ((⟨_, hO'⟩ : ↥O) - ⟨_, hcO⟩)) := by
  classical
  subst hOdef
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero ℓ' := ⟨(Fact.out : ℓ'.Prime).ne_zero⟩
  have hob68 := S3C4Glue.C3aux_exists_emb k₀ (q * ℓ') ξ hξ
  obtain ⟨ι, hι'⟩ := hob68
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')) :=
    ⟨ι, by rw [hι']; simp only [Nat.cast_mul]⟩
  intro g hg hgi hcusp hgK
  have hgC := ModularCurve.FullLevel.qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd q M' hqM' A hA R₀ hR₀
    k₀ ℓ' Kℓ hKℓ jℓ hjℓ g hg hgi hcusp hgK
  have hx0 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull ↥k₀ M' 1 (q ^ 2 * M')
    ⟨q ^ 2, by ring⟩ (ModularCurve.FullLevel.levelH q M') g hg
  rw [ModularCurve.qExpand_one_apply] at hx0
  have hfix : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ (⟨_, hgK⟩ : ↥Kℓ) = ⟨_, hgK⟩ := by
    intro τ hτ
    have hob69 := hGatt τ hτ
    obtain ⟨γ, hγq, hγ0, hatt⟩ := hob69
    exact (ModularCurve.FullLevel.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom q M'
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM') ℓ' ↥k₀ ξ hξ hι Kℓ hKℓ).2 _ hx0 ⟨_, hgK⟩ rfl γ hγq hγ0 τ hatt
  have hF : (⟨_, hgK⟩ : ↥Kℓ) ∈ K₀ := by
    rw [hK₀, IntermediateField.mem_fixedField_iff]; exact hfix
  have hgWx : (⟨_, hgK⟩ : ↥Kℓ) ∈ Wx := hCWx ⟨_, hgC⟩
  refine ⟨hF, hgWx, ?_, ?_⟩
  · intro hW
    have hob70 := ModularCurve.FullLevel.qExpand_coeffEmb_mem_maximalIdeal_iff_residue_eq_zero_of_forall_aeval_jqNModC_mem
      q hq M' hqM' A hA R₀ hR₀ k₀ π₀ hπ hdvr hunif ℓ' Kℓ hKℓ jℓ hjℓ hjK Wx hVA hCWx hVj g hg hgi hcusp hgK
    obtain ⟨hV, hiff⟩ := hob70
    rw [S3C4Glue.mem_maximalIdeal_comap_iff K₀ Wx ⟨_, hF⟩ hW]
    exact hiff
  · intro hres
    refine ⟨(S3C4Glue.mem_traceNode K₀ Õ _).mpr (hCO ⟨_, hgC⟩), ?_⟩
    intro hO' c hc hcO hev hu
    have hy' := hover g hg hgi hcusp hres hgK hgC c hc hev
    have hob71 := (hR3d _).mp hy'
    obtain ⟨hbW, hbm⟩ := hob71

    have hAval : (((⟨⟨_, hgK⟩, hgC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) : ↥Kℓ) =
        (⟨_, hgK⟩ : ↥Kℓ) - algebraMap ↥k₀ ↥Kℓ c := by
      rw [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]; rfl

    have hob72 := (S3C4Glue.isUnit_mk_iff (traceNode K₀ Õ) _ _).mp (by
      have : ((⟨_, hO'⟩ : ↥(traceNode K₀ Õ)) - ⟨_, hcO⟩) = ⟨(⟨_, hF⟩ : ↥K₀) - algebraMap ↥k₀ ↥K₀ c, (traceNode K₀ Õ).sub_mem hO' hcO⟩ := rfl
      rw [this] at hu; exact hu)
    obtain ⟨v, hvO, hv⟩ := hob72
    have hvW : (v : ↥Kℓ) ∈ Wt := hOW _ ((S3C4Glue.mem_traceNode K₀ Õ v).mp hvO)
    have hprod : ((⟨_, hgK⟩ : ↥Kℓ) - algebraMap ↥k₀ ↥Kℓ c) * (v : ↥Kℓ) = 1 := by
      have := congrArg (fun z : ↥K₀ => (z : ↥Kℓ)) hv
      simpa using this
    apply hbm
    have : (⟨_, hbW⟩ : ↥Wt) = ⟨(⟨_, hgK⟩ : ↥Kℓ) - algebraMap ↥k₀ ↥Kℓ c, hAval ▸ hbW⟩ := Subtype.ext hAval
    rw [this]
    exact IsUnit.of_mul_eq_one (b := (⟨(v : ↥Kℓ), hvW⟩ : ↥Wt)) (Subtype.ext hprod)

end S_ModularCurve_FullLevel_levelLaws_trace_of_igusaBranch_of_rigidChart
end P2MW
export P2MW.S_ModularCurve_FullLevel_levelLaws_trace_of_igusaBranch_of_rigidChart (solution)
