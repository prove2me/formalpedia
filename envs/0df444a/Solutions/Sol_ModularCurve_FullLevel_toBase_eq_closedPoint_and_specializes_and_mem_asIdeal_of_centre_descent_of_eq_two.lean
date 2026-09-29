-- Prove2me | solution 1 for ModularCurve.FullLevel.toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2ac78463-f3bd-55f4-9403-ad3d9508cd14

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_transcendental_and_finiteDimensional_adjoin_levelField
import Theorems.Thm_ModularCurve_FullLevel_mem_igusaRing_coe_levelField_and_injective_twoChartIntegralModel_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_two
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin

import Theorems.Thm_ModularCurve_FullLevel_isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_two
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_eq_of_specializes_of_isMaximal_of_mem_chart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ValuationSubring.instIsAlgClosedResidueField GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E150I

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem isUnit_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    IsUnit (e a) ↔ IsUnit a := MulEquiv.isUnit_map e.toMulEquiv

theorem mem_maximalIdeal_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (a : A) : e a ∈ maximalIdeal B ↔ a ∈ maximalIdeal A := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_of_ringEquiv]

theorem eval_map_symm {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (f : B[X]) (b : A) :
    e ((f.map e.symm.toRingHom).eval b) = f.eval (e b) := by
  rw [Polynomial.eval_map]
  change e.toRingHom (eval₂ e.symm.toRingHom b f) = _
  rw [Polynomial.hom_eval₂, RingEquiv.toRingHom_comp_symm_toRingHom, eval₂_eq_eval_map, Polynomial.map_id]
  rfl

theorem henselianLocalRing_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [HenselianLocalRing A] (e : A ≃+* B) : HenselianLocalRing B where
  is_henselian := by
    intro f hf a₀ h₁ h₂
    set g : A[X] := f.map e.symm.toRingHom with hg_def
    have hg : g.Monic := hf.map _
    have hb₀ : e (e.symm a₀) = a₀ := e.apply_symm_apply a₀
    have h₁' : g.eval (e.symm a₀) ∈ maximalIdeal A := by
      rw [← mem_maximalIdeal_iff_of_ringEquiv e, eval_map_symm, hb₀]; exact h₁
    have h₂' : IsUnit (g.derivative.eval (e.symm a₀)) := by
      rw [← isUnit_iff_of_ringEquiv e, hg_def, derivative_map, eval_map_symm, hb₀]; exact h₂
    obtain ⟨b, hb, hb'⟩ := HenselianLocalRing.is_henselian g hg (e.symm a₀) h₁' h₂'
    refine ⟨e b, ?_, ?_⟩
    · have := congrArg e hb.eq_zero
      rw [eval_map_symm, map_zero] at this
      exact this
    · have := (mem_maximalIdeal_iff_of_ringEquiv e _).mpr hb'
      rwa [map_sub, hb₀] at this

theorem isDiscreteValuationRing_of_ringEquiv {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing A] (e : A ≃+* B) : IsDiscreteValuationRing B := by
  haveI : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  haveI : IsLocalRing B := IsLocalRing.of_surjective' e.toRingHom e.surjective
  refine { not_a_field' := ?_ }
  intro h
  apply IsDiscreteValuationRing.not_a_field A
  rw [eq_bot_iff] at h ⊢
  intro a ha
  have := h ((mem_maximalIdeal_iff_of_ringEquiv e a).mpr ha)
  rw [Ideal.mem_bot] at this ⊢
  exact e.injective (this.trans (map_zero e).symm)

theorem maximalIdeal_eq_span_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (ϖ : A) (h : maximalIdeal A = Ideal.span {ϖ}) : maximalIdeal B = Ideal.span {e ϖ} := by
  apply le_antisymm
  · intro b hb
    have : e.symm b ∈ maximalIdeal A := by
      rw [← mem_maximalIdeal_iff_of_ringEquiv e, e.apply_symm_apply]; exact hb
    rw [h, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    rw [Ideal.mem_span_singleton]
    refine ⟨e c, ?_⟩
    rw [← map_mul, ← hc, e.apply_symm_apply]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (mem_maximalIdeal_iff_of_ringEquiv e ϖ).mpr (h ▸ Ideal.mem_span_singleton_self ϖ)

theorem exists_isPrimitiveRoot_of_isUnit_of_residueField
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    (n : ℕ) (hn : 0 < n) (hnA : IsUnit (n : A))
    (hk : ∃ ζ₀ : ResidueField A, IsPrimitiveRoot ζ₀ n) :
    ∃ ζ : A, IsPrimitiveRoot ζ n ∧ ∃ ζ₀ : ResidueField A, IsPrimitiveRoot ζ₀ n ∧ residue A ζ = ζ₀ := by
  obtain ⟨ζ₀, hζ₀⟩ := hk
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective ζ₀
  have ha₀' : residue A a₀ = ζ₀ := ha₀

  have hmonic : (X ^ n - 1 : A[X]).Monic := monic_X_pow_sub_C (1 : A) hn.ne'
  have heval : (X ^ n - 1 : A[X]).eval a₀ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff]
    simp only [eval_sub, eval_pow, eval_X, eval_one, map_sub, map_pow, map_one, ha₀', hζ₀.pow_eq_one, sub_self]
  have hderiv : IsUnit ((X ^ n - 1 : A[X]).derivative.eval a₀) := by
    have : (X ^ n - 1 : A[X]).derivative.eval a₀ = (n : A) * a₀ ^ (n - 1) := by
      simp [derivative_X_pow]
    rw [this]
    refine hnA.mul (IsUnit.pow _ ?_)
    rw [← residue_ne_zero_iff_isUnit, ha₀']
    exact hζ₀.ne_zero hn.ne'
  obtain ⟨ζ, hroot, hζa⟩ := HenselianLocalRing.is_henselian (X ^ n - 1) hmonic a₀ heval hderiv
  have hres : residue A ζ = ζ₀ := by
    rw [← ha₀', ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hζa
  have hpow : ζ ^ n = 1 := by
    have := hroot
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at this
    exact this
  refine ⟨ζ, IsPrimitiveRoot.mk_of_lt ζ hn hpow ?_, ζ₀, hζ₀, hres⟩
  intro l hl0 hln hl
  apply hζ₀.pow_ne_one_of_pos_of_lt hl0.ne' hln
  rw [← hres, ← map_pow, hl, map_one]

end E150I

namespace E148LC
theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] (O : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (O.comap f).nonunits ↔ f x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero_iff f f.injective]
end E148LC

namespace E147GP

universe u

open AlgebraicCurve.TwoChartIntegralModel in

theorem chartAlg_mem_of_subset {R F : Type u} {E : Type*} [CommRing R] [Field F] [Field E] [Algebra R F]
    (ι : F →+* E) (O : ValuationSubring E) (S : Set F)
    (hR : ∀ a : R, ι (algebraMap R F a) ∈ O) (hS : ∀ s ∈ S, ι s ∈ O) :
    ∀ b : F, b ∈ chartAlg R F S → ι b ∈ O := by
  intro b hb
  rw [mem_chartAlg_iff] at hb
  let P : Subalgebra R F :=
    { carrier := {f | ι f ∈ O}
      mul_mem' := fun {a b} ha hb => by
        show ι (a * b) ∈ O
        rw [map_mul]; exact O.mul_mem _ _ ha hb
      one_mem' := by show ι 1 ∈ O; rw [map_one]; exact O.one_mem
      add_mem' := fun {a b} ha hb => by
        show ι (a + b) ∈ O
        rw [map_add]; exact O.add_mem _ _ ha hb
      zero_mem' := by show ι 0 ∈ O; rw [map_zero]; exact O.zero_mem
      algebraMap_mem' := hR }
  have hadj : Algebra.adjoin R S ≤ P := Algebra.adjoin_le (fun s hs => hS s hs)
  let φ : ↥(Algebra.adjoin R S) →+* O :=
    (ι.comp (algebraMap ↥(Algebra.adjoin R S) F)).codRestrict O.toSubring (fun s => hadj s.2)
  have hint : IsIntegral O (ι b) :=
    hb.map_of_comp_eq φ ι (by ext s; rfl)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := E)).mp hint
  rw [← hy]
  exact y.2

theorem mem_nonunits_of_mem_nonunits_of_le {K E : Type*} [Field K] [Field E] (V : ValuationSubring K) (W : ValuationSubring E)
    (ι : K →+* E) (hVW : ∀ f : K, f ∈ V → ι f ∈ W) (x : K) (hx : ι x ∈ W.nonunits) : x ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hx ⊢
  rcases hx with h0 | hinv
  · exact Or.inl ((map_eq_zero_iff ι ι.injective).mp h0)
  · exact Or.inr (fun h => hinv (by rw [← map_inv₀]; exact hVW _ h))

end E147GP

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
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

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
    [Fact ((⟨_, hjF₀⟩ : ↥F₀) ≠ 0)]
    (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q))
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V)
    (hCV : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V)
    (𝔫 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫p : 𝔫.IsPrime)
    (h𝔫 : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits) :
    (AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩) = closedPoint A₀ ∧
    (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩ ⤳ y →
      y = (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩) ∧
    (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y = (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩ →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
          ((b : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg (lineInfty q)).nonunits → b ∈ y.asIdeal) ∧
    (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y = (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩ →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
          ((b : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg (lineInfty q)).nonunits → b ∈ y.asIdeal) := by
  classical
  have hqprime : q.Prime := Fact.out

  obtain ⟨k₀, π₀, hπ₀, hk₀, hππ, hdvrK, hunifK, hhensK, hresK, hκ, ⟨ℓa, hℓa, hℓa3, hℓaq, hℓaM', ζ₀, hζ₀⟩, htame, ⟨eK, heK⟩,
      hA₁, hfd, hdvr1, hhens1, ⟨e₀, he₀⟩, hform⟩ :=
    ModularCurve.FullLevel.exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
  letI algk0 : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  obtain ⟨F₀', hCHAR, hK1, hSTAB, hLD, hRAT, hcar, Φ, hΦ⟩ := hform
  haveI := hdvr1
  haveI := hhens1
  have hΦ' : ∀ t : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'), ((Φ.symm t : ↥F₀) : ↥(fieldBar q M')) = (t : ↥(fieldBar q M')) := fun t => by
    rw [← hΦ (Φ.symm t), Φ.apply_symm_apply]

  obtain ⟨R, hR⟩ := ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr
  have hR₀O := ModularCurve.FullLevel.mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr

  let iBT : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) →+* ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') :=
    RingHom.codRestrict ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')
      (fun c => (le_sup_left : IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ≤ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))
        (IntermediateField.subset_adjoin _ _ ⟨(c : AlgebraicClosure ℚ), c.2, rfl⟩))
  letI algBT : Algebra ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') := iBT.toAlgebra
  have hBT : ∀ c : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), ((algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) := fun _ => rfl
  letI algA1T : Algebra ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') :=
    (Φ.toRingHom.comp ((algebraMap A₀ ↥F₀).comp e₀.symm.toRingHom)).toAlgebra
  have halgT : ∀ a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))), ((algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))) : AlgebraicClosure ℚ) := by
    intro a
    change ((Φ (algebraMap A₀ ↥F₀ (e₀.symm a)) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) = _
    rw [hΦ, hj₀, ← he₀ (e₀.symm a), e₀.apply_symm_apply]
  letI algBF : Algebra ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥F₀ := (Φ.symm.toRingHom.comp (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))).toAlgebra
  let ψ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') ≃ₐ[↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))] ↥F₀ := AlgEquiv.ofRingEquiv (f := Φ.symm) (fun _ => rfl)
  letI algA0B : Algebra A₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) := ((algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))).comp e₀.symm.symm.toRingHom).toAlgebra
  haveI : IsFractionRing A₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (R := ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)))) (S := ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))) e₀.symm).mp inferInstance
  haveI istA0BF : IsScalarTower A₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥F₀ := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    apply Subtype.ext
    change ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      ((Φ.symm (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') ((e₀.symm.symm a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)))) : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)))) : ↥F₀) : ↥(fieldBar q M'))
    rw [hΦ', hBT, hj₀]
    exact congrArg _ (he₀ a).symm

  let j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') := Φ (⟨_, hjF₀⟩ : ↥F₀)
  have hj₁ : (j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
      ↥(modularFunctionFieldBar M')) := hΦ _
  have hj₁' : ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]; rfl
  haveI hj₁0 : Fact (j₁ ≠ 0) := ⟨fun h => (Fact.out : (⟨_, hjF₀⟩ : ↥F₀) ≠ 0) (Φ.injective (h.trans (map_zero Φ).symm))⟩
  have hψj : ψ j₁ = (⟨_, hjF₀⟩ : ↥F₀) := Φ.symm_apply_apply _

  obtain ⟨htj1, hFD1⟩ := @ModularCurve.FullLevel.transcendental_and_finiteDimensional_adjoin_levelField
    q _ M' _ k₀ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd F₀' hK1 (hLD (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd) hRAT algBT hBT j₁ hj₁'
  have hIR := ModularCurve.FullLevel.mem_igusaRing_coe_levelField_and_injective_twoChartIntegralModel_of_eq_two
    q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvrK hunifK hhensK hresK hκ ℓa hℓa hℓa3 hℓaq hℓaM' ζ₀ hζ₀ π₀ hπ₀ htame (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd (A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) hA₁ F₀' hK1 hSTAB hLD hRAT halgT j₁ hj₁
  dsimp only at hIR
  obtain ⟨hR1, hR2, hR3, hR4⟩ := hIR
  have hBI := ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_two
    q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvrK hunifK hhensK hresK hκ ℓa hℓa hℓa3 hℓaq hℓaM' ζ₀ hζ₀ π₀ hπ₀ htame (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd (A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) hA₁ F₀' hK1 hSTAB hLD hRAT halgT j₁ hj₁

  have htjF : Transcendental ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (⟨_, hjF₀⟩ : ↥F₀) := by
    intro h
    apply htj1
    rw [← hψj] at h
    exact (isAlgebraic_algHom_iff ψ.toAlgHom ψ.injective).mp h
  have htj0 : Transcendental A₀ (⟨_, hjF₀⟩ : ↥F₀) := fun h =>
    htjF (h.extendScalars (IsFractionRing.injective A₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))))
  haveI := hFD1
  have hmap : (IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({j₁} : Set ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))).map ψ.toAlgHom =
      IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    congr 2
  let e₁ := ((IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({j₁} : Set ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))).equivMap ψ.toAlgHom).trans
    (IntermediateField.equivOfEq hmap)
  have hFDF : FiniteDimensional ↥(IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) ↥F₀ := by
    refine Module.Finite.of_equiv_equiv e₁.toRingEquiv ψ.toRingEquiv ?_
    ext x
    rfl
  haveI := hFDF
  have hsepF : Algebra.IsSeparable ↥(IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) ↥F₀ := inferInstance

  let VIg : CuspidalType.ProjLine q → ValuationSubring ↥F₀ := fun l => (OIg l).comap F₀.subtype
  have hVIg : ∀ l (x : ↥F₀), x ∈ VIg l ↔ (x : ↥(fieldBar q M')) ∈ OIg l := fun _ _ => ValuationSubring.mem_comap
  have hVIgnu : ∀ l (x : ↥F₀), x ∈ (VIg l).nonunits ↔ (x : ↥(fieldBar q M')) ∈ (OIg l).nonunits := fun l x =>
    E148LC.mem_nonunits_comap_iff (OIg l) F₀.subtype x

  have heA : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      ((algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') (e₀ a) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) := fun a => by
    rw [hj₀, halgT, he₀]
  have hVA : ∀ l (a : A₀), algebraMap A₀ ↥F₀ a ∈ VIg l := fun l a => by
    rw [hVIg, heA]; exact hR1 l (e₀ a)
  have hVm : ∀ l, ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ ↥F₀ a ∈ (VIg l).nonunits := fun l a ha => by
    rw [hVIgnu, heA]; exact hR2 l (e₀ a) ((E150I.mem_maximalIdeal_iff_of_ringEquiv e₀ a).mpr ha)

  have hVWnu : ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ (OIg (lineInfty q)).nonunits → x ∈ V.nonunits := fun x hx =>
    E147GP.mem_nonunits_of_mem_nonunits_of_le V (OIg (lineInfty q)) F₀.subtype hV x hx
  have hmax : 𝔫.IsMaximal :=
    ModularCurve.FullLevel.isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
      ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) (Or.inl rfl) V hV hVlt hCV 𝔫 h𝔫
  have hϖ𝔫 : algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫 := by
    rw [h𝔫]
    apply hVWnu
    have h1 := hVm (lineInfty q) ϖ₀ (by rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀)
    rw [hVIgnu] at h1
    exact h1
  refine ⟨?_, ?_, ?_, ?_⟩

  · have hc : (AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩) =
        (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))))).base ⟨𝔫, h𝔫p⟩ := by
      rw [← AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase]
      rfl
    rw [hc]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) 𝔫 = maximalIdeal A₀
    have hne : Ideal.comap (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) 𝔫 ≠ ⊥ := by
      intro h0
      have : ϖ₀ ∈ (⊥ : Ideal A₀) := by rw [← h0, Ideal.mem_comap]; exact hϖ𝔫
      rw [Ideal.mem_bot] at this
      apply IsDiscreteValuationRing.not_a_field A₀
      rw [hϖ₀, this, Ideal.span_singleton_eq_bot]
    haveI : (Ideal.comap (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) 𝔫).IsPrime := Ideal.comap_isPrime _ 𝔫
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)

  · intro y hy
    exact AlgebraicCurve.TwoChartIntegralModel.eq_of_specializes_of_isMaximal_of_mem_chart A₀ ϖ₀ hϖ₀
      ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) htj0 hFDF hsepF _
      (Or.inl ⟨⟨𝔫, h𝔫p⟩, rfl, hmax, hϖ𝔫⟩) y hy

  · intro y hy b hb
    have hyy : y = ⟨𝔫, h𝔫p⟩ := (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).isOpenEmbedding.injective hy
    subst hyy
    show b ∈ 𝔫
    rw [h𝔫]
    exact hVWnu _ hb

  · intro y hy b hb

    have hy' : (CategoryTheory.Limits.colimit.ι (CategoryTheory.Limits.span (AlgebraicCurve.TwoChartIntegralModel.fFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))
          (AlgebraicCurve.TwoChartIntegralModel.fInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) CategoryTheory.Limits.WalkingSpan.left).base ⟨𝔫, h𝔫p⟩ =
        (CategoryTheory.Limits.colimit.ι (CategoryTheory.Limits.span (AlgebraicCurve.TwoChartIntegralModel.fFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))
          (AlgebraicCurve.TwoChartIntegralModel.fInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) CategoryTheory.Limits.WalkingSpan.right).base y := hy.symm
    obtain ⟨k, fi, fj, m, hm1, hm2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff
      (CategoryTheory.Limits.span (AlgebraicCurve.TwoChartIntegralModel.fFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (AlgebraicCurve.TwoChartIntegralModel.fInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))).mp hy'
    rcases k with (_ | _ | _)
    rotate_left
    · change CategoryTheory.Limits.WidePushoutShape.Hom (some CategoryTheory.Limits.WalkingPair.left)
        (some CategoryTheory.Limits.WalkingPair.right) at fj
      cases fj
    · change CategoryTheory.Limits.WidePushoutShape.Hom (some CategoryTheory.Limits.WalkingPair.right)
        (some CategoryTheory.Limits.WalkingPair.left) at fi
      cases fi
    change CategoryTheory.Limits.WidePushoutShape.Hom none (some CategoryTheory.Limits.WalkingPair.left) at fi
    change CategoryTheory.Limits.WidePushoutShape.Hom none (some CategoryTheory.Limits.WalkingPair.right) at fj
    cases fi
    cases fj

    have hm1' : (AlgebraicCurve.TwoChartIntegralModel.fFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base m = ⟨𝔫, h𝔫p⟩ := by
      first | simpa using hm1 | exact hm1
    have hm2' : (AlgebraicCurve.TwoChartIntegralModel.fInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base m = y := by
      first | simpa using hm2 | exact hm2
    have hcomapF : Ideal.comap (AlgebraicCurve.TwoChartIntegralModel.inclFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).toRingHom m.asIdeal = 𝔫 :=
      congrArg PrimeSpectrum.asIdeal hm1'
    have hcomapI : Ideal.comap (AlgebraicCurve.TwoChartIntegralModel.inclInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).toRingHom m.asIdeal = y.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hm2'

    have hjn : AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) ∉ 𝔫 := by
      intro hj
      rw [← hcomapF, Ideal.mem_comap] at hj
      exact m.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hj (AlgebraicCurve.TwoChartIntegralModel.isUnit_inclFin_jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))
    have hjinv : ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ ∈ V := by
      have h1 : ((AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) ∉ V.nonunits := fun h => hjn ((h𝔫 _).mpr h)
      rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h1
      exact h1.2
    have hCIV : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V := fun g =>
      E147GP.chartAlg_mem_of_subset (RingHom.id ↥F₀) V ({((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹} : Set ↥F₀)
        (fun a => hCV (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a)) (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hjinv) (g : ↥F₀) g.2
    have hbV : (b : ↥F₀) ∈ V.nonunits := hVWnu _ hb

    letI algFM : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := (AlgebraicCurve.TwoChartIntegralModel.inclFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).toRingHom.toAlgebra
    have hloc : IsLocalization.Away (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) :=
      AlgebraicCurve.TwoChartIntegralModel.isLocalization_away_inclFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)
    have hread : ∀ z : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (z : ↥F₀) ∈ V.nonunits → z ∈ m.asIdeal := by
      intro z hz
      obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, hcz⟩ := IsLocalization.surj (Submonoid.powers (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) z

      have hu : IsUnit (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) ^ n)) := by
        rw [map_pow]; exact (AlgebraicCurve.TwoChartIntegralModel.isUnit_inclFin_jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).pow n
      have hcV : (c : ↥F₀) ∈ V.nonunits := by
        have hval : (c : ↥F₀) = (z : ↥F₀) * ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) ^ n := by
          have := congrArg (fun w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) => (w : ↥F₀)) hcz
          simp only [Subalgebra.coe_mul] at this
          have h2 : ((algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) = (c : ↥F₀) :=
            AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl A₀ ↥F₀ _ c
          have h3 : ((algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) ^ n) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) = ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) ^ n := by
            rw [map_pow, Subalgebra.coe_pow]
            exact congrArg (fun w : ↥F₀ => w ^ n) (AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl A₀ ↥F₀ _ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))
          rw [← h2, ← this, h3]
        rw [hval, ValuationSubring.mem_nonunits_iff, Valuation.map_mul, Valuation.map_pow]
        have hj1 : V.valuation (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)) ≤ 1 := (V.valuation_le_one_iff _).mpr (hCV (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))
        calc V.valuation (z : ↥F₀) * V.valuation (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)) ^ n ≤ V.valuation (z : ↥F₀) * 1 := by
              apply mul_le_mul_right (pow_le_one' hj1 n)
          _ < 1 := by rw [mul_one]; exact (ValuationSubring.mem_nonunits_iff _).mp hz
      have hcn : c ∈ 𝔫 := (h𝔫 c).mpr hcV
      rw [← hcomapF, Ideal.mem_comap] at hcn

      have : z * algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) ^ n) ∈ m.asIdeal := by
        rw [hcz]; exact hcn
      exact (m.2.mem_or_mem this).resolve_right (fun h => m.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu))
    rw [← hcomapI, Ideal.mem_comap]
    apply hread
    show ((AlgebraicCurve.TwoChartIntegralModel.inclInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) ∈ V.nonunits
    rw [AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl]
    exact hbV

end S_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two (solution)
