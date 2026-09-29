-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_levelAutBar_smul_centred_goodPt_of_centred_of_not_mem_range_iotaFin_twoChartIntegralModel_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/e1836aba-0c1d-5924-94ae-27c5218c5e1f

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_FullLevel_exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_centred_of_isRational_of_isProper_twoChartIntegralModel_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_isProper_toBase_twoChartIntegralModel_levelField_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_forall_mem_nonunits_igusa_mem_asIdeal_of_centred_twoChartIntegralModel_of_eq_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_levelAutBar_smul_centred_goodPt_of_centred_of_not_mem_range_iotaFin_twoChartIntegralModel_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ValuationSubring.instIsAlgClosedResidueField GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

universe u

namespace N4Aux

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

section Valuation

variable {F : Type u} [Field F]

theorem val_mul_lt_one (A : ValuationSubring F) {a b : F} (ha : A.valuation a ≤ 1) (hb : A.valuation b < 1) :
    A.valuation (a * b) < 1 := by
  rw [map_mul]
  calc A.valuation a * A.valuation b ≤ 1 * A.valuation b := mul_le_mul_left ha _
    _ = A.valuation b := one_mul _
    _ < 1 := hb

theorem mem_nonunits_iff_mem_and (A : ValuationSubring F) (x : F) :
    x ∈ A.nonunits ↔ x ∈ A ∧ (x ≠ 0 → x⁻¹ ∉ A) := by
  rw [ValuationSubring.mem_nonunits_iff]
  constructor
  · intro hx
    refine ⟨(A.valuation_le_one_iff x).1 hx.le, fun hx0 hinv => ?_⟩
    have h1 : A.valuation x⁻¹ ≤ 1 := (A.valuation_le_one_iff _).2 hinv
    have h2 : A.valuation (x⁻¹ * x) < 1 := val_mul_lt_one A h1 hx
    rw [inv_mul_cancel₀ hx0, map_one] at h2
    exact lt_irrefl _ h2
  · rintro ⟨hxA, hinv⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [map_zero]; exact zero_lt_one
    by_contra hcon
    apply hinv hx0
    rw [← A.valuation_le_one_iff]
    rw [not_lt] at hcon
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ hcon

theorem mem_nonunits_iff_of_forall_mem_iff {A A' : ValuationSubring F} (σ : F ≃+* F)
    (h : ∀ f, σ f ∈ A' ↔ f ∈ A) (f : F) : σ f ∈ A'.nonunits ↔ f ∈ A.nonunits := by
  rw [mem_nonunits_iff_mem_and, mem_nonunits_iff_mem_and, h, ← map_inv₀, h]
  have : σ f ≠ 0 ↔ f ≠ 0 := (map_ne_zero_iff (σ : F →+* F) σ.injective)
  rw [this]

theorem valuation_inv_lt_one_of_mem_chartAlgFin {R : Type u} [CommRing R] [Algebra R F]
    (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V)
    (j j' : F) (hj0 : j ≠ 0) [Fact (j' ≠ 0)] (hjj' : j ∈ chartAlgFin R F j')
    (hj : V.valuation j⁻¹ < 1) : V.valuation j'⁻¹ < 1 := by
  by_contra hcon
  have hj'0 : j' ≠ 0 := Fact.out

  have hj'V : j' ∈ V := by
    rw [← V.valuation_le_one_iff]
    rw [not_lt, map_inv₀, one_le_inv₀ ((map_ne_zero V.valuation).mpr hj'0 |>.bot_lt)] at hcon
    exact hcon

  let W : Subalgebra R F := { V.toSubring.toSubsemiring with algebraMap_mem' := hRV }
  have hle : Algebra.adjoin R ({j'} : Set F) ≤ W := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hj'V)

  rw [mem_chartAlg_iff] at hjj'
  obtain ⟨p, hpmon, hpj⟩ := hjj'
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpmon.coeff_natDegree, map_one, one_mul] at hpj

  set n := p.natDegree with hn
  have hcV : ∀ i, (algebraMap (↥(Algebra.adjoin R ({j'} : Set F))) F (p.coeff i)) ∈ V := fun i =>
    hle (p.coeff i).2
  have key : (1 : F) = - ∑ i ∈ Finset.range n,
      algebraMap (↥(Algebra.adjoin R ({j'} : Set F))) F (p.coeff i) * (j⁻¹) ^ (n - i) := by
    have hjn : (j⁻¹) ^ n * j ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hj0, one_pow]
    have := congrArg (fun z => (j⁻¹) ^ n * z) hpj
    simp only [mul_add, mul_zero, Finset.mul_sum, hjn] at this
    rw [← eq_neg_iff_add_eq_zero] at this
    have hS : ∑ i ∈ Finset.range n, algebraMap (↥(Algebra.adjoin R ({j'} : Set F))) F (p.coeff i) * (j⁻¹) ^ (n - i)
        = ∑ i ∈ Finset.range n, (j⁻¹) ^ n * (algebraMap (↥(Algebra.adjoin R ({j'} : Set F))) F (p.coeff i) * j ^ i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < n := Finset.mem_range.1 hi
      have hpow : (j⁻¹) ^ n * j ^ i = (j⁻¹) ^ (n - i) := by
        rw [show n = (n - i) + i by omega, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hj0, one_pow, mul_one,
          show n - i + i - i = n - i by omega]
      rw [mul_left_comm, hpow]
    rw [hS, this, neg_neg]
  have hlt : V.valuation (- ∑ i ∈ Finset.range n,
      algebraMap (↥(Algebra.adjoin R ({j'} : Set F))) F (p.coeff i) * (j⁻¹) ^ (n - i)) < 1 := by
    rw [Valuation.map_neg]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i hi
    have hni : n - i ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hi)
    exact val_mul_lt_one V ((V.valuation_le_one_iff _).2 (hcV i)) (by rw [map_pow]; exact pow_lt_one₀ zero_le' hj hni)
  rw [← key, map_one] at hlt
  exact lt_irrefl _ hlt

end Valuation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

section Overlap

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_mid_of_ιFin_eq_ιInf (y : XFin R F j) (y' : XInf R F j)
    (h : (ιFin R F j).base y = (ιInf R F j).base y') :
    ∃ z : XMid R F j, (fFin R F j).base z = y ∧ (fInf R F j).base z = y' := by
  have h' : (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.left).base y =
      (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.right).base y' := h
  obtain ⟨k, fi, fj, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff _).1 h'
  rcases k with (_ | _ | _)
  · have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
    have hfj : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
    subst hfi hfj
    exact ⟨z, h1, h2⟩
  · exact nomatch fj
  · exact nomatch fi

theorem exists_comap_eq_of_ιFin_eq_ιInf (y : XFin R F j) (y' : XInf R F j)
    (h : (ιFin R F j).base y = (ιInf R F j).base y') :
    ∃ z : XMid R F j, y.asIdeal = Ideal.comap (inclFin R F j).toRingHom z.asIdeal ∧
      y'.asIdeal = Ideal.comap (inclInf R F j).toRingHom z.asIdeal := by
  obtain ⟨z, h1, h2⟩ := exists_mid_of_ιFin_eq_ιInf R F j y y' h
  exact ⟨z, by rw [← h1]; rfl, by rw [← h2]; rfl⟩

theorem jInvChartInf_mem_of_not_mem_range (y' : XInf R F j)
    (hx : (ιInf R F j).base y' ∉ Set.range (ιFin R F j).base) :
    jInvChartInf R F j ∈ y'.asIdeal := by
  by_contra hj
  letI : Algebra (chartAlgInf R F j) (chartAlgMid R F j) := (inclInf R F j).toRingHom.toAlgebra
  haveI : IsLocalization.Away (jInvChartInf R F j) (chartAlgMid R F j) :=
    isLocalization_away_inclInf R F j
  have hdisj : Disjoint (↑(Submonoid.powers (jInvChartInf R F j)) : Set (chartAlgInf R F j))
      (↑y'.asIdeal : Set (chartAlgInf R F j)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hj (y'.isPrime.mem_of_pow_mem n hn)
  have hmem : y' ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (chartAlgInf R F j) (chartAlgMid R F j))) := by
    rw [PrimeSpectrum.localization_comap_range (chartAlgMid R F j)
      (Submonoid.powers (jInvChartInf R F j))]
    exact hdisj
  obtain ⟨z, hz⟩ := hmem
  apply hx
  have hglue : (ιFin R F j).base ((fFin R F j).base z) = (ιInf R F j).base ((fInf R F j).base z) :=
    congrArg (fun f => f.base z) (glue_condition R F j)
  refine ⟨(fFin R F j).base z, hglue.trans ?_⟩
  show (ιInf R F j).base (PrimeSpectrum.comap (inclInf R F j).toRingHom z) = _
  rw [← hz]
  rfl

theorem exists_inf_witness (z : XMid R F j) (b : chartAlgFin R F j) :
    ∃ (n : ℕ) (g : chartAlgInf R F j),
      (b : F) * ((jInvChartInf R F j ^ n : chartAlgInf R F j) : F) = (g : F) ∧
      jInvChartInf R F j ^ n ∉ Ideal.comap (inclInf R F j).toRingHom z.asIdeal ∧
      (b ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal ↔
        g ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hb : (b : F) ∈ chartAlg R F (insert j⁻¹⁻¹ {j⁻¹}) := by
    rw [inv_inv]
    exact chartAlg_mono R F (Set.singleton_subset_iff.2 (Set.mem_insert j _)) b.2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j⁻¹) (inv_ne_zero hj0) hb
  have hu : IsUnit (inclInf R F j (jInvChartInf R F j) ^ n) := (isUnit_inclInf_jInvChartInf R F j).pow n
  have e1 : ∀ x, (inclInf R F j).toRingHom x = inclInf R F j x := fun _ => rfl
  have e2 : ∀ x, (inclFin R F j).toRingHom x = inclFin R F j x := fun _ => rfl
  refine ⟨n, ⟨j⁻¹ ^ n * b, hn⟩, ?_, ?_, ?_⟩
  · rw [Subalgebra.coe_pow, coe_jInvChartInf]
    ring
  · intro hmem
    rw [Ideal.mem_comap, e1, map_pow] at hmem
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2]
    have hprod : inclInf R F j ⟨j⁻¹ ^ n * b, hn⟩ =
        inclInf R F j (jInvChartInf R F j) ^ n * inclFin R F j b := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_chartIncl, coe_chartIncl,
        coe_jInvChartInf]
    rw [hprod, Ideal.unit_mul_mem_iff_mem _ hu]

end Overlap

section FinWitness

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_fin_witness (z : XMid R F j) (b : chartAlgInf R F j) :
    ∃ (n : ℕ) (g : chartAlgFin R F j),
      (b : F) * ((jChartFin R F j ^ n : chartAlgFin R F j) : F) = (g : F) ∧
      jChartFin R F j ^ n ∉ Ideal.comap (inclFin R F j).toRingHom z.asIdeal ∧
      (b ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal ↔
        g ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hb : (b : F) ∈ chartAlg R F (insert j⁻¹ {j}) :=
    chartAlg_mono R F (Set.singleton_subset_iff.2 (Set.mem_insert j⁻¹ _)) b.2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j) hj0 hb
  have hu : IsUnit (inclFin R F j (jChartFin R F j) ^ n) := (isUnit_inclFin_jChartFin R F j).pow n
  have e1 : ∀ x, (inclInf R F j).toRingHom x = inclInf R F j x := fun _ => rfl
  have e2 : ∀ x, (inclFin R F j).toRingHom x = inclFin R F j x := fun _ => rfl
  refine ⟨n, ⟨j ^ n * b, hn⟩, ?_, ?_, ?_⟩
  · rw [Subalgebra.coe_pow, coe_jChartFin]
    ring
  · intro hmem
    rw [Ideal.mem_comap, e2, map_pow] at hmem
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2]
    have hprod : inclFin R F j ⟨j ^ n * b, hn⟩ =
        inclFin R F j (jChartFin R F j) ^ n * inclInf R F j b := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_chartIncl, coe_chartIncl,
        coe_jChartFin]
    rw [hprod, Ideal.unit_mul_mem_iff_mem _ hu]

end FinWitness

section Dict

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem chartDict :
    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel R F j) → F → Prop := fun x f =>
      (∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel R F j) → F → Prop := fun x f =>
      (∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F))
    (∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        InStalk ((ιFin R F j).base y) (b : F) ∧ (InMax ((ιFin R F j).base y) (b : F) ↔ b ∈ y.asIdeal)) ∧
    (∀ (y : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)),
        InStalk ((ιInf R F j).base y) (b : F) ∧ (InMax ((ιInf R F j).base y) (b : F) ↔ b ∈ y.asIdeal)) := by
  intro InStalk InMax
  have h1F : ∀ y₂ : ↥(XFin R F j), (1 : ↥(chartAlgFin R F j)) ∉ y₂.asIdeal := fun y₂ =>
    (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top
  have h1I : ∀ y₂ : ↥(XInf R F j), (1 : ↥(chartAlgInf R F j)) ∉ y₂.asIdeal := fun y₂ =>
    (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top
  constructor
  · intro y b
    have hov : ∀ y', (ιInf R F j).base y' = (ιFin R F j).base y →
        ∃ z : XMid R F j, y.asIdeal = Ideal.comap (inclFin R F j).toRingHom z.asIdeal ∧
          y'.asIdeal = Ideal.comap (inclInf R F j).toRingHom z.asIdeal :=
      fun y' hy' => exists_comap_eq_of_ιFin_eq_ιInf R F j y y' hy'.symm
    constructor
    · refine ⟨fun y₂ _ => ⟨b, 1, h1F y₂, by simp⟩, fun y' hy' => ?_⟩
      obtain ⟨z, hzy, hzy'⟩ := hov y' hy'
      obtain ⟨n, g, hbg, hnot, -⟩ := exists_inf_witness R F j z b
      exact ⟨g, jInvChartInf R F j ^ n, by rwa [hzy'], hbg⟩
    · constructor
      · rintro ⟨hF, -⟩
        obtain ⟨g, h, hh, hg, hbh⟩ := hF y rfl
        have hbh' : b * h = g := Subtype.ext hbh
        have hmem : b * h ∈ y.asIdeal := by rw [hbh']; exact hg
        exact (y.isPrime.mem_or_mem hmem).resolve_right hh
      · intro hb
        refine ⟨fun y₂ hy₂ => ?_, fun y' hy' => ?_⟩
        · have hyy : y₂ = y := (ιFin R F j).isOpenEmbedding.injective hy₂
          subst hyy
          exact ⟨b, 1, h1F y₂, hb, by simp⟩
        · obtain ⟨z, hzy, hzy'⟩ := hov y' hy'
          obtain ⟨n, g, hbg, hnot, hiff⟩ := exists_inf_witness R F j z b
          refine ⟨g, jInvChartInf R F j ^ n, by rwa [hzy'], ?_, hbg⟩
          rw [hzy']
          exact hiff.1 (by rw [← hzy]; exact hb)
  · intro y b
    have hov : ∀ y', (ιFin R F j).base y' = (ιInf R F j).base y →
        ∃ z : XMid R F j, y'.asIdeal = Ideal.comap (inclFin R F j).toRingHom z.asIdeal ∧
          y.asIdeal = Ideal.comap (inclInf R F j).toRingHom z.asIdeal :=
      fun y' hy' => exists_comap_eq_of_ιFin_eq_ιInf R F j y' y hy'
    constructor
    · refine ⟨fun y' hy' => ?_, fun y₂ _ => ⟨b, 1, h1I y₂, by simp⟩⟩
      obtain ⟨z, hzy', hzy⟩ := hov y' hy'
      obtain ⟨n, g, hbg, hnot, -⟩ := exists_fin_witness R F j z b
      exact ⟨g, jChartFin R F j ^ n, by rwa [hzy'], hbg⟩
    · constructor
      · rintro ⟨-, hI⟩
        obtain ⟨g, h, hh, hg, hbh⟩ := hI y rfl
        have hbh' : b * h = g := Subtype.ext hbh
        have hmem : b * h ∈ y.asIdeal := by rw [hbh']; exact hg
        exact (y.isPrime.mem_or_mem hmem).resolve_right hh
      · intro hb
        refine ⟨fun y' hy' => ?_, fun y₂ hy₂ => ?_⟩
        · obtain ⟨z, hzy', hzy⟩ := hov y' hy'
          obtain ⟨n, g, hbg, hnot, hiff⟩ := exists_fin_witness R F j z b
          refine ⟨g, jChartFin R F j ^ n, by rwa [hzy'], ?_, hbg⟩
          rw [hzy']
          exact hiff.1 (by rw [← hzy]; exact hb)
        · have hyy : y₂ = y := (ιInf R F j).isOpenEmbedding.injective hy₂
          subst hyy
          exact ⟨b, 1, h1I y₂, hb, by simp⟩

end Dict

section Transport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem cuspTransport (j' : F) [Fact (j' ≠ 0)]
    (hjj' : j ∈ chartAlgFin R F j')
    (hswap3 : ∀ y, y ∈ chartAlgInf R F j' → ∃ s, s ∈ chartAlgInf R F j ∧
      (∃ a, a ∈ chartAlgInf R F j ∧ s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j)
    (hswap4 : ∀ y, y ∈ chartAlgInf R F j → ∃ s, s ∈ chartAlgInf R F j' ∧
      (∃ a, a ∈ chartAlgInf R F j' ∧ s = 1 + j'⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j')
    (σ : F ≃ₐ[R] F) (hσj' : σ j' = j')
    (hσFin : ∀ b, b ∈ chartAlgFin R F j ↔ σ b ∈ chartAlgFin R F j)
    (hσInf : ∀ b, b ∈ chartAlgInf R F j' ↔ σ b ∈ chartAlgInf R F j')
    (V V' : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V) (hVV' : ∀ f, σ f ∈ V' ↔ f ∈ V)
    (x x' : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (I : Set F) (hI : ∀ c ∈ I, ∀ h ∈ chartAlgInf R F j, h * c ∈ I) :
    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel R F j) → F → Prop := fun x f =>
      (∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel R F j) → F → Prop := fun x f =>
      (∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F))
    (∀ f, InStalk x f → f ∈ V ∧ (f ∈ V.nonunits ↔ InMax x f)) →
    (∀ f, InStalk x' f → f ∈ V' ∧ (f ∈ V'.nonunits ↔ InMax x' f)) →
    x ∉ Set.range (ιFin R F j).base →
    (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x → ∀ b : ↥(chartAlgInf R F j), (b : F) ∈ I → b ∈ y.asIdeal) →
    x' ∉ Set.range (ιFin R F j).base ∧
    ∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = x' →
      ∀ b : ↥(chartAlgInf R F j), σ.symm (b : F) ∈ I → b ∈ y'.asIdeal := by
  intro InStalk InMax hx hx' hxFin hC1
  have hj0 : j ≠ 0 := Fact.out
  obtain ⟨hDF, hDI⟩ := chartDict R F j

  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ↥(XInf R F j), (ιInf R F j).base y₀ = x := by
    rcases mem_range_ιFin_or_mem_range_ιInf R F j x with h | ⟨y₀, h⟩
    · exact absurd h hxFin
    · exact ⟨y₀, h⟩
  subst hy₀
  have hjinv : jInvChartInf R F j ∈ y₀.asIdeal := jInvChartInf_mem_of_not_mem_range R F j y₀ hxFin
  have h1y₀ : (1 : ↥(chartAlgInf R F j)) ∉ y₀.asIdeal := (Ideal.ne_top_iff_one _).1 y₀.isPrime.ne_top

  have hInfV : ∀ b : ↥(chartAlgInf R F j), (b : F) ∈ V ∧ ((b : F) ∈ V.nonunits ↔ b ∈ y₀.asIdeal) := fun b =>
    ⟨(hx _ (hDI y₀ b).1).1, ((hx _ (hDI y₀ b).1).2).trans (hDI y₀ b).2⟩
  have hjV : V.valuation j⁻¹ < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ← coe_jInvChartInf (R := R) (F := F) (j := j)]
    exact (hInfV _).2.mpr hjinv
  refine ⟨?_, ?_⟩
  ·
    rintro ⟨y', hy'⟩
    have hσj : σ j ∈ chartAlgFin R F j := (hσFin j).1 (jChartFin R F j).2
    have hst : InStalk x' (σ j) := by rw [← hy']; exact (hDF y' ⟨σ j, hσj⟩).1
    have hjV' : j ∈ V := (hVV' j).1 (hx' _ hst).1
    have : V.valuation (j * j⁻¹) < 1 := val_mul_lt_one V ((V.valuation_le_one_iff _).2 hjV') hjV
    rw [mul_inv_cancel₀ hj0, map_one] at this
    exact lt_irrefl _ this
  · intro y' hy' b hbI
    have hσj's : σ.symm j' = j' := by rw [AlgEquiv.symm_apply_eq]; exact hσj'.symm
    have hσInf' : ∀ z, σ.symm z ∈ chartAlgInf R F j' ↔ z ∈ chartAlgInf R F j' := fun z => by
      rw [hσInf, AlgEquiv.apply_symm_apply]

    obtain ⟨s₁, hs₁, ⟨a₁, ha₁, hs₁eq⟩, hs₁b⟩ := hswap4 (b : F) b.2
    have hz : σ.symm (s₁ * b) ∈ chartAlgInf R F j' := (hσInf' _).2 hs₁b
    have hw : σ.symm s₁ ∈ chartAlgInf R F j' := (hσInf' _).2 hs₁
    have he : σ.symm a₁ ∈ chartAlgInf R F j' := (hσInf' _).2 ha₁
    have hw_eq : σ.symm s₁ = 1 + j'⁻¹ * σ.symm a₁ := by
      rw [hs₁eq, map_add, map_one, map_mul, map_inv₀, hσj's]
    obtain ⟨s₂, hs₂, ⟨a₂, ha₂, hs₂eq⟩, hg₂⟩ := hswap3 _ hz
    obtain ⟨s₃, hs₃, ⟨a₃, ha₃, hs₃eq⟩, hh₃⟩ := hswap3 _ hw
    obtain ⟨s₄, hs₄, ⟨a₄, ha₄, hs₄eq⟩, he₄⟩ := hswap3 _ he

    have hsm : ∀ (s a : F) (hs : s ∈ chartAlgInf R F j) (ha : a ∈ chartAlgInf R F j), s = 1 + j⁻¹ * a →
        (⟨s, hs⟩ : ↥(chartAlgInf R F j)) - 1 ∈ y₀.asIdeal := by
      intro s a hs ha hsa
      have : (⟨s, hs⟩ : ↥(chartAlgInf R F j)) - 1 = jInvChartInf R F j * ⟨a, ha⟩ :=
        Subtype.ext (by simp [hsa, coe_jInvChartInf])
      rw [this]; exact y₀.asIdeal.mul_mem_right _ hjinv
    have hsnot : ∀ (s a : F) (hs : s ∈ chartAlgInf R F j) (ha : a ∈ chartAlgInf R F j), s = 1 + j⁻¹ * a →
        (⟨s, hs⟩ : ↥(chartAlgInf R F j)) ∉ y₀.asIdeal := by
      intro s a hs ha hsa hmem
      apply h1y₀
      have := y₀.asIdeal.sub_mem hmem (hsm s a hs ha hsa)
      rwa [sub_sub_cancel] at this

    have heSt : InStalk ((ιInf R F j).base y₀) (σ.symm a₁) := by
      refine ⟨fun y hy => absurd ⟨y, hy⟩ hxFin, fun y hy => ?_⟩
      have hyy : y = y₀ := (ιInf R F j).isOpenEmbedding.injective hy
      subst hyy
      exact ⟨⟨s₄ * σ.symm a₁, he₄⟩, ⟨s₄, hs₄⟩, hsnot s₄ a₄ hs₄ ha₄ hs₄eq, by simp [mul_comm]⟩
    have heV : V.valuation (σ.symm a₁) ≤ 1 := (V.valuation_le_one_iff _).2 (hx _ heSt).1

    have hj'V : V.valuation j'⁻¹ < 1 := valuation_inv_lt_one_of_mem_chartAlgFin V hRV j j' hj0 hjj' hjV

    let H : ↥(chartAlgInf R F j) := ⟨s₂, hs₂⟩ * ⟨s₃ * σ.symm s₁, hh₃⟩
    let G : ↥(chartAlgInf R F j) := ⟨s₃, hs₃⟩ * ⟨s₂ * σ.symm (s₁ * b), hg₂⟩
    have hcH : σ.symm (b : F) * (H : F) = (G : F) := by
      simp only [H, G, Subalgebra.coe_mul, map_mul]
      ring

    let T : ↥(chartAlgInf R F j) := H - ⟨s₂, hs₂⟩ * ⟨s₃, hs₃⟩
    have hT : (T : F) = (s₂ * s₃) * (j'⁻¹ * σ.symm a₁) := by
      simp only [T, H, Subalgebra.coe_sub, Subalgebra.coe_mul, hw_eq]
      ring
    have hs₂s₃V : V.valuation (s₂ * s₃) ≤ 1 :=
      (V.valuation_le_one_iff _).2 (hInfV (⟨s₂, hs₂⟩ * ⟨s₃, hs₃⟩)).1
    have hTy : T ∈ y₀.asIdeal := by
      apply (hInfV T).2.mp
      rw [ValuationSubring.mem_nonunits_iff, hT]
      exact val_mul_lt_one V hs₂s₃V (by rw [mul_comm]; exact val_mul_lt_one V heV hj'V)
    have hHnot : H ∉ y₀.asIdeal := by
      intro hH
      apply h1y₀
      have h23 : (⟨s₂, hs₂⟩ * ⟨s₃, hs₃⟩ : ↥(chartAlgInf R F j)) - 1 ∈ y₀.asIdeal := by
        have : (⟨s₂, hs₂⟩ * ⟨s₃, hs₃⟩ : ↥(chartAlgInf R F j)) - 1 =
            (⟨s₂, hs₂⟩ - 1) * ⟨s₃, hs₃⟩ + (⟨s₃, hs₃⟩ - 1) := by ring
        rw [this]
        exact y₀.asIdeal.add_mem (y₀.asIdeal.mul_mem_right _ (hsm s₂ a₂ hs₂ ha₂ hs₂eq)) (hsm s₃ a₃ hs₃ ha₃ hs₃eq)
      have : (1 : ↥(chartAlgInf R F j)) = H - T - (⟨s₂, hs₂⟩ * ⟨s₃, hs₃⟩ - 1) := by simp only [T]; ring
      rw [this]
      exact y₀.asIdeal.sub_mem (y₀.asIdeal.sub_mem hH hTy) h23

    have hGI : (G : F) ∈ I := by
      rw [← hcH, mul_comm]
      exact hI _ hbI _ H.2
    have hGy : G ∈ y₀.asIdeal := hC1 y₀ rfl G hGI

    have hcSt : InStalk ((ιInf R F j).base y₀) (σ.symm (b : F)) := by
      refine ⟨fun y hy => absurd ⟨y, hy⟩ hxFin, fun y hy => ?_⟩
      have hyy : y = y₀ := (ιInf R F j).isOpenEmbedding.injective hy
      subst hyy
      exact ⟨G, H, hHnot, hcH⟩
    have hcMax : InMax ((ιInf R F j).base y₀) (σ.symm (b : F)) := by
      refine ⟨fun y hy => absurd ⟨y, hy⟩ hxFin, fun y hy => ?_⟩
      have hyy : y = y₀ := (ιInf R F j).isOpenEmbedding.injective hy
      subst hyy
      exact ⟨G, H, hHnot, hGy, hcH⟩
    have hcV : σ.symm (b : F) ∈ V.nonunits := (hx _ hcSt).2.mpr hcMax

    have hbV' : (b : F) ∈ V'.nonunits := by
      have := (mem_nonunits_iff_of_forall_mem_iff (A := V) (A' := V') σ.toRingEquiv
        (fun f => hVV' f) (σ.symm (b : F))).2 hcV
      simpa using this
    have hbSt : InStalk x' (b : F) := by rw [← hy']; exact (hDI y' b).1
    have hbMax : InMax x' (b : F) := (hx' _ hbSt).2.mp hbV'
    rw [← hy'] at hbMax
    exact (hDI y' b).2.mp hbMax

theorem not_mem_range_of_not_mem_range (V : ValuationSubring F)
    (x xb : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) :
    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel R F j) → F → Prop := fun x f =>
      (∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel R F j) → F → Prop := fun x f =>
      (∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F))
    (∀ f, InStalk x f → f ∈ V ∧ (f ∈ V.nonunits ↔ InMax x f)) →
    (∀ f, InStalk xb f → f ∈ V ∧ (f ∈ V.nonunits ↔ InMax xb f)) →
    x ∉ Set.range (ιFin R F j).base → xb ∉ Set.range (ιFin R F j).base := by
  intro InStalk InMax hx hxb hxFin
  have hj0 : j ≠ 0 := Fact.out
  obtain ⟨hDF, hDI⟩ := chartDict R F j
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ↥(XInf R F j), (ιInf R F j).base y₀ = x := by
    rcases mem_range_ιFin_or_mem_range_ιInf R F j x with h | ⟨y₀, h⟩
    · exact absurd h hxFin
    · exact ⟨y₀, h⟩
  subst hy₀
  have hjinv : jInvChartInf R F j ∈ y₀.asIdeal := jInvChartInf_mem_of_not_mem_range R F j y₀ hxFin
  have hjV : V.valuation j⁻¹ < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ← coe_jInvChartInf (R := R) (F := F) (j := j)]
    exact ((hx _ (hDI y₀ _).1).2).mpr ((hDI y₀ _).2 |>.mpr hjinv)
  rintro ⟨y', hy'⟩
  have hst : InStalk xb j := by rw [← hy']; exact (hDF y' (jChartFin R F j)).1
  have hjV' : j ∈ V := (hxb _ hst).1
  have : V.valuation (j * j⁻¹) < 1 := val_mul_lt_one V ((V.valuation_le_one_iff _).2 hjV') hjV
  rw [mul_inv_cancel₀ hj0, map_one] at this
  exact lt_irrefl _ this

end Transport

end N4Aux

namespace N4Cv

section CompositeValuation

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem inv_mem_of_isUnit {O : ValuationSubring F} {f : F} (hf : f ∈ O) (hu : IsUnit (⟨f, hf⟩ : ↥O)) : f⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : (↥O)ˣ) : ↥O).1 * f = 1 := by
    have h := congrArg Subtype.val (u.inv_mul)
    rw [hu] at h
    exact h
  have h2 : ((u⁻¹ : (↥O)ˣ) : ↥O).1 = f⁻¹ := eq_inv_of_mul_eq_one_left h1
  exact h2 ▸ ((u⁻¹ : (↥O)ˣ) : ↥O).2

theorem mem_maximalIdeal_inv_of_not_mem {O : ValuationSubring F} {f : F} (hf : f ∉ O) :
    ∃ hfi : f⁻¹ ∈ O, (⟨f⁻¹, hfi⟩ : ↥O) ∈ maximalIdeal ↥O := by
  have hfi : f⁻¹ ∈ O := (O.mem_or_inv_mem f).resolve_left hf
  refine ⟨hfi, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact hf (inv_inv f ▸ inv_mem_of_isUnit hfi hu)

theorem ne_zero_of_isUnit_mk {O : ValuationSubring F} {f : F} (hf : f ∈ O) (hu : IsUnit (⟨f, hf⟩ : ↥O)) : f ≠ 0 := by
  rintro rfl
  exact not_isUnit_zero ((show (⟨(0 : F), hf⟩ : ↥O) = 0 from rfl) ▸ hu)

noncomputable def resEquiv (P : Place K F) (hP : P.IsRational) : K ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap K P.ResidueField) ⟨P.algebraMap_residueField_injective, hP⟩

noncomputable def ev (P : Place K F) (hP : P.IsRational) : ↥P.toValuationSubring →+* K :=
  (resEquiv P hP).symm.toRingHom.comp (IsLocalRing.residue ↥P.toValuationSubring)

theorem ev_eq_evalAt (P : Place K F) (hP : P.IsRational) (f : F) (hf : f ∈ P.toValuationSubring) :
    ev P hP ⟨f, hf⟩ = P.evalAt f := by
  apply P.algebraMap_residueField_injective
  rw [P.algebraMap_evalAt hP hf]
  change (resEquiv P hP) ((resEquiv P hP).symm (IsLocalRing.residue _ ⟨f, hf⟩)) = _
  rw [RingEquiv.apply_symm_apply]

theorem evalAt_algebraMap (P : Place K F) (hP : P.IsRational) (a : K) :
    P.evalAt (algebraMap K F a) = a := by
  rw [← ev_eq_evalAt P hP _ (P.algebraMap_mem' a)]
  apply P.algebraMap_residueField_injective
  change (resEquiv P hP) ((resEquiv P hP).symm (IsLocalRing.residue _ _)) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem ev_eq_zero_iff (P : Place K F) (hP : P.IsRational) (f : ↥P.toValuationSubring) :
    ev P hP f = 0 ↔ f ∈ maximalIdeal ↥P.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff]
  change (resEquiv P hP).symm _ = 0 ↔ _
  rw [map_eq_zero_iff _ (resEquiv P hP).symm.injective]

theorem evalAt_mul (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f * g) = P.evalAt f * P.evalAt g := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP g hg, ← ev_eq_evalAt P hP (f * g) (mul_mem hf hg), ← map_mul]; rfl

theorem evalAt_add (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP g hg, ← ev_eq_evalAt P hP (f + g) (add_mem hf hg), ← map_add]; rfl

theorem evalAt_neg (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt (-f) = -P.evalAt f := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP (-f) (neg_mem hf), ← map_neg]; rfl

theorem evalAt_sub (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f - g) = P.evalAt f - P.evalAt g := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP g hg, ← ev_eq_evalAt P hP (f - g) (sub_mem hf hg), ← map_sub]; rfl

theorem evalAt_eq_zero_iff (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt f = 0 ↔ (⟨f, hf⟩ : ↥P.toValuationSubring) ∈ maximalIdeal ↥P.toValuationSubring := by
  rw [← ev_eq_evalAt P hP f hf, ev_eq_zero_iff]

variable (P : Place K F) (hP : P.IsRational) (A : ValuationSubring K)

noncomputable def compVal : ValuationSubring F where
  carrier := {f | f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A}
  mul_mem' := by
    rintro f g ⟨hf, hfA⟩ ⟨hg, hgA⟩
    exact ⟨mul_mem hf hg, by rw [evalAt_mul P hP hf hg]; exact mul_mem hfA hgA⟩
  one_mem' := ⟨one_mem _, by rw [Place.evalAt_one]; exact one_mem _⟩
  add_mem' := by
    rintro f g ⟨hf, hfA⟩ ⟨hg, hgA⟩
    exact ⟨add_mem hf hg, by rw [evalAt_add P hP hf hg]; exact add_mem hfA hgA⟩
  zero_mem' := ⟨zero_mem _, by
    have : P.evalAt (0 : F) = 0 := by
      rw [← ev_eq_evalAt P hP 0 (zero_mem _)]
      exact (ev_eq_zero_iff P hP _).mpr (by
        have : (⟨(0 : F), zero_mem _⟩ : ↥P.toValuationSubring) = 0 := rfl
        rw [this]; exact (maximalIdeal ↥P.toValuationSubring).zero_mem)
    rw [this]; exact zero_mem _⟩
  neg_mem' := by
    rintro f ⟨hf, hfA⟩
    exact ⟨neg_mem hf, by rw [evalAt_neg P hP hf]; exact neg_mem hfA⟩
  mem_or_inv_mem' := by
    intro f
    by_cases hf : f ∈ P.toValuationSubring
    · by_cases hfm : (⟨f, hf⟩ : ↥P.toValuationSubring) ∈ maximalIdeal ↥P.toValuationSubring
      · left
        exact ⟨hf, by rw [(evalAt_eq_zero_iff P hP hf).mpr hfm]; exact zero_mem _⟩
      · have hfu : IsUnit (⟨f, hf⟩ : ↥P.toValuationSubring) := by
          rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hfm
        have hfi : f⁻¹ ∈ P.toValuationSubring := inv_mem_of_isUnit hf hfu
        have hf0 : f ≠ 0 := ne_zero_of_isUnit_mk hf hfu
        have hprod : P.evalAt f * P.evalAt f⁻¹ = 1 := by
          rw [← evalAt_mul P hP hf hfi, mul_inv_cancel₀ hf0, Place.evalAt_one]
        rcases A.mem_or_inv_mem (P.evalAt f) with hA | hA
        · left; exact ⟨hf, hA⟩
        · right
          refine ⟨hfi, ?_⟩
          rw [eq_inv_of_mul_eq_one_right hprod]
          exact hA
    · right
      obtain ⟨hfi, hm⟩ := mem_maximalIdeal_inv_of_not_mem hf
      exact ⟨hfi, by rw [(evalAt_eq_zero_iff P hP hfi).mpr hm]; exact zero_mem _⟩

theorem mem_compVal_iff {f : F} : f ∈ compVal P hP A ↔ f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A :=
  ⟨fun h => h, fun h => h⟩

theorem algebraMap_mem_compVal {a : K} (ha : a ∈ A) : algebraMap K F a ∈ compVal P hP A :=
  ⟨P.algebraMap_mem' a, by rw [evalAt_algebraMap P hP]; exact ha⟩

theorem isUnit_compVal_iff (f : F) (hf : f ∈ compVal P hP A) :
    IsUnit (⟨f, hf⟩ : ↥(compVal P hP A)) ↔ IsUnit (⟨P.evalAt f, hf.2⟩ : ↥A) := by
  constructor
  · intro hu
    have hfi : f⁻¹ ∈ compVal P hP A := inv_mem_of_isUnit hf hu
    have hf0 : f ≠ 0 := ne_zero_of_isUnit_mk hf hu
    have hprod : P.evalAt f * P.evalAt f⁻¹ = 1 := by
      rw [← evalAt_mul P hP hf.1 hfi.1, mul_inv_cancel₀ hf0, Place.evalAt_one]
    exact isUnit_iff_exists_inv.mpr ⟨⟨P.evalAt f⁻¹, hfi.2⟩, Subtype.ext hprod⟩
  · intro hu
    have hne : P.evalAt f ≠ 0 := ne_zero_of_isUnit_mk hf.2 hu
    have hfm : (⟨f, hf.1⟩ : ↥P.toValuationSubring) ∉ maximalIdeal ↥P.toValuationSubring :=
      fun h => hne ((evalAt_eq_zero_iff P hP hf.1).mpr h)
    have hfu : IsUnit (⟨f, hf.1⟩ : ↥P.toValuationSubring) := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hfm
    have hfiP : f⁻¹ ∈ P.toValuationSubring := inv_mem_of_isUnit hf.1 hfu
    have hf0 : f ≠ 0 := ne_zero_of_isUnit_mk hf.1 hfu
    have hprod : P.evalAt f * P.evalAt f⁻¹ = 1 := by
      rw [← evalAt_mul P hP hf.1 hfiP, mul_inv_cancel₀ hf0, Place.evalAt_one]
    have hfiA : P.evalAt f⁻¹ ∈ A := by
      rw [eq_inv_of_mul_eq_one_right hprod]
      exact inv_mem_of_isUnit _ hu
    exact isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hfiP, hfiA⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩

theorem coe_mem_nonunits_compVal_iff (f : F) (hf : f ∈ compVal P hP A) :
    f ∈ (compVal P hP A).nonunits ↔ P.evalAt f ∈ A.nonunits := by
  have h1 : f ∈ (compVal P hP A).nonunits ↔ (⟨f, hf⟩ : ↥(compVal P hP A)) ∈ maximalIdeal _ :=
    ValuationSubring.coe_mem_nonunits_iff (a := (⟨f, hf⟩ : ↥(compVal P hP A)))
  have h2 : P.evalAt f ∈ A.nonunits ↔ (⟨P.evalAt f, hf.2⟩ : ↥A) ∈ maximalIdeal _ :=
    ValuationSubring.coe_mem_nonunits_iff (a := (⟨P.evalAt f, hf.2⟩ : ↥A))
  rw [h1, h2, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_compVal_iff, ← mem_nonunits_iff,
    ← IsLocalRing.mem_maximalIdeal]

theorem valuation_evalAt_lt_one_iff (f : F) (hf : f ∈ compVal P hP A) :
    A.valuation (P.evalAt f) < 1 ↔ f ∈ (compVal P hP A).nonunits := by
  rw [coe_mem_nonunits_compVal_iff P hP A f hf, ValuationSubring.mem_nonunits_iff]

end CompositeValuation

end N4Cv

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

    ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')) (x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)), Centred P x →
      x ∉ Set.range (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base →
        ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ ∃ x' : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x' ∧ Centred (levelAutBar q M' ζ γ • P) x' := by
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hK1 hstab hLD hRAT instAlg hconst j₁ hj₁ instFact
  intro InStalk InMax Centred GoodPt Reads OffBranch
  intro P x hPx hxFin
  have hPrat : P.IsRational := hPx.1

  have hT1 := ModularCurve.FullLevel.isProper_toBase_twoChartIntegralModel_levelField_of_eq_three (q := q) (hq3 := hq3) (M' := M') (hqM' := hqM') (A := A) (hA := hA) (W := W) (hW := hW) (hle := hle) (R₀ := R₀) (hR₀ := hR₀) (ζ := ζ) (OIg := OIg) (OSS := OSS) (hIg_inf := hIg_inf) (hIg := hIg) (hIg_inj := hIg_inj) (hIg_perm := hIg_perm) (hSS_A := hSS_A) (hSS_over := hSS_over) (hSS_fix := hSS_fix) (hSS_tr := hSS_tr) (R := R) (hR := hR) (hR₀O := hR₀O) (π := π) (hπ := hπ) (hπP := hπP) (k₀ := k₀) (π₀ := π₀) (hπ₀ := hπ₀) (hdvr := hdvr) (hunif := hunif) (hhens := hhens) (hres := hres) (hκ := hκ) (ℓ := ℓ) (hℓ := hℓ) (hℓ3 := hℓ3) (hℓq := hℓq) (hℓM' := hℓM') (ζ₀ := ζ₀) (hζ₀ := hζ₀) (ϖt := ϖt) (hϖtA := hϖtA) (hϖt := hϖt) (K₁ := K₁) (hK₁ := hK₁) (A₁ := A₁) (hA₁ := hA₁) F₀ hK1 hstab hLD hRAT hconst j₁ hj₁
  have hT2 := ModularCurve.FullLevel.exists_centred_of_isRational_of_isProper_twoChartIntegralModel_of_eq_three (q := q) (hq3 := hq3) (M' := M') (hqM' := hqM') (A := A) (hA := hA) (W := W) (hW := hW) (hle := hle) (R₀ := R₀) (hR₀ := hR₀) (ζ := ζ) (OIg := OIg) (OSS := OSS) (hIg_inf := hIg_inf) (hIg := hIg) (hIg_inj := hIg_inj) (hIg_perm := hIg_perm) (hSS_A := hSS_A) (hSS_over := hSS_over) (hSS_fix := hSS_fix) (hSS_tr := hSS_tr) (R := R) (hR := hR) (hR₀O := hR₀O) (π := π) (hπ := hπ) (hπP := hπP) (k₀ := k₀) (π₀ := π₀) (hπ₀ := hπ₀) (hdvr := hdvr) (hunif := hunif) (hhens := hhens) (hres := hres) (hκ := hκ) (ℓ := ℓ) (hℓ := hℓ) (hℓ3 := hℓ3) (hℓq := hℓq) (hℓM' := hℓM') (ζ₀ := ζ₀) (hζ₀ := hζ₀) (ϖt := ϖt) (hϖtA := hϖtA) (hϖt := hϖt) (K₁ := K₁) (hK₁ := hK₁) (A₁ := A₁) (hA₁ := hA₁) F₀ hK1 hstab hLD hRAT hconst j₁ hj₁ hT1
  have hT3 := ModularCurve.FullLevel.exists_forall_mem_nonunits_igusa_mem_asIdeal_of_centred_twoChartIntegralModel_of_eq_three (q := q) (hq3 := hq3) (M' := M') (hqM' := hqM') (A := A) (hA := hA) (W := W) (hW := hW) (hle := hle) (R₀ := R₀) (hR₀ := hR₀) (ζ := ζ) (OIg := OIg) (OSS := OSS) (hIg_inf := hIg_inf) (hIg := hIg) (hIg_inj := hIg_inj) (hIg_perm := hIg_perm) (hSS_A := hSS_A) (hSS_over := hSS_over) (hSS_fix := hSS_fix) (hSS_tr := hSS_tr) (R := R) (hR := hR) (hR₀O := hR₀O) (π := π) (hπ := hπ) (hπP := hπP) (k₀ := k₀) (π₀ := π₀) (hπ₀ := hπ₀) (hdvr := hdvr) (hunif := hunif) (hhens := hhens) (hres := hres) (hκ := hκ) (ℓ := ℓ) (hℓ := hℓ) (hℓ3 := hℓ3) (hℓq := hℓq) (hℓM' := hℓM') (ζ₀ := ζ₀) (hζ₀ := hζ₀) (ϖt := ϖt) (hϖtA := hϖtA) (hϖt := hϖt) (K₁ := K₁) (hK₁ := hK₁) (A₁ := A₁) (hA₁ := hA₁) F₀ hK1 hstab hLD hRAT hconst j₁ hj₁
  obtain ⟨j', hj'exp, hj'fin, hjfin', hN3⟩ := ModularCurve.FullLevel.exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three (q := q) (hq3 := hq3) (M' := M') (hqM' := hqM') (hle := hle) (k₀ := k₀) (K₁ := K₁) (hK₁ := hK₁) (A₁ := A₁) F₀ hK1 hstab hLD hRAT hconst j₁ hj₁
  obtain ⟨j'', hj''exp, hsw3, hsw4⟩ := ModularCurve.FullLevel.exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_three (q := q) (hq3 := hq3) (M' := M') (hqM' := hqM') (hle := hle) (k₀ := k₀) (K₁ := K₁) (hK₁ := hK₁) (A₁ := A₁) F₀ hK1 hstab hLD hRAT hconst j₁ hj₁
  have hjj : j' = j'' := Subtype.ext (Subtype.ext (hj'exp.trans hj''exp.symm))
  subst hjj
  have hj₁0 : j₁ ≠ 0 := Fact.out
  haveI hj'F : Fact (j' ≠ 0) := ⟨fun h => by
    have h2 : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = 0 := by
      rw [← hj'exp, h]; rfl
    have h3 : qExpand ℚ q jq = 0 := (coeffEmb (AlgebraicClosure ℚ)).injective (h2.trans (map_zero _).symm)
    exact jq_ne_zero (qExpand_injective (R := ℚ) (N := q) (h3.trans (map_zero _).symm))⟩

  obtain ⟨xb, hxbsp, hxbcl, hxbcen⟩ := hT2 P hPrat
  obtain ⟨ℓb, -, hInfℓ, hcontInf, -⟩ := hT3 P xb hxbcen hxbsp hxbcl

  obtain ⟨γ, hγ, -, hOIgℓ⟩ := hIg ℓb
  have hg : levelAutBar q M' ζ γ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
      ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ} :=
    Subgroup.subset_closure ⟨ζ, γ, hγ, rfl⟩
  obtain ⟨σ, hσg, hσgs, hσj', hσFin, hσInf', hσP⟩ := hN3 _ hg
  obtain ⟨hgPrat, hgP⟩ := hσP P hPrat

  obtain ⟨x', hx'sp, hx'cl, hx'cen⟩ := hT2 (levelAutBar q M' ζ γ • P) hgPrat

  let ι : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) →+* ↥(fieldBar q M') := algebraMap ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ↥(fieldBar q M')
  have hι : ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), ι f = (f : ↥(fieldBar q M')) := fun f => rfl
  let V : ValuationSubring ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) := (N4Cv.compVal P hPrat A).comap ι
  let V' : ValuationSubring ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) := (N4Cv.compVal (levelAutBar q M' ζ γ • P) hgPrat A).comap ι
  have hmemV : ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), f ∈ V ↔ (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A :=
    fun f => Iff.rfl
  have hmemV' : ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), f ∈ V' ↔ (f : ↥(fieldBar q M')) ∈ (levelAutBar q M' ζ γ • P).toValuationSubring ∧
      (levelAutBar q M' ζ γ • P).evalAt (f : ↥(fieldBar q M')) ∈ A := fun f => Iff.rfl

  have hnuV : ∀ (Q : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')) (hQ : Q.IsRational) (f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      (f : ↥(fieldBar q M')) ∈ N4Cv.compVal Q hQ A →
      (f ∈ ((N4Cv.compVal Q hQ A).comap ι).nonunits ↔ A.valuation (Q.evalAt (f : ↥(fieldBar q M'))) < 1) := by
    intro Q hQ f hf
    rw [N4Cv.valuation_evalAt_lt_one_iff Q hQ A _ hf, N4Aux.mem_nonunits_iff_mem_and, N4Aux.mem_nonunits_iff_mem_and,
      ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀]
    have hne : (f ≠ 0) ↔ (ι f ≠ 0) := (map_ne_zero_iff ι (algebraMap ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ↥(fieldBar q M')).injective).symm
    rw [hne]
    exact Iff.rfl

  have hxV : ∀ f, InStalk xb f → f ∈ V ∧ (f ∈ V.nonunits ↔ InMax xb f) := by
    intro f hf
    obtain ⟨h1, h2, h3⟩ := hxbcen.2 f hf
    exact ⟨⟨h1, h2⟩, (hnuV P hPrat f ⟨h1, h2⟩).trans h3⟩
  have hx'V : ∀ f, InStalk x' f → f ∈ V' ∧ (f ∈ V'.nonunits ↔ InMax x' f) := by
    intro f hf
    obtain ⟨h1, h2, h3⟩ := hx'cen.2 f hf
    exact ⟨⟨h1, h2⟩, (hnuV _ hgPrat f ⟨h1, h2⟩).trans h3⟩

  have hRV : ∀ r : ↥A₁, algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) r ∈ V := by
    intro r
    show ι (algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) r) ∈ N4Cv.compVal P hPrat A
    rw [hι, hconst]
    exact N4Cv.algebraMap_mem_compVal P hPrat A (((hA₁ (r : ↥K₁)).1 r.2))

  have hVV' : ∀ f, σ f ∈ V' ↔ f ∈ V := by
    intro f
    rw [hmemV, hmemV', hσg f, (hgP (f : ↥(fieldBar q M'))).1]
    exact and_congr_left' (hgP (f : ↥(fieldBar q M'))).2

  let I : Set ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) := {c | (c : ↥(fieldBar q M')) ∈ (OIg ℓb).nonunits}
  have hI : ∀ c ∈ I, ∀ h ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁, h * c ∈ I := by
    intro c hc h hh
    have hc' : ((c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓb).nonunits := hc
    show ((h * c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓb).nonunits
    have hmul : ((h * c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) = (h : ↥(fieldBar q M')) * (c : ↥(fieldBar q M')) := rfl
    rw [hmul, ValuationSubring.mem_nonunits_iff]
    rw [ValuationSubring.mem_nonunits_iff] at hc'
    exact N4Aux.val_mul_lt_one (OIg ℓb) (((OIg ℓb).valuation_le_one_iff _).2 (hcontInf ⟨h, hh⟩)) hc'

  have hxV0 : ∀ f, InStalk x f → f ∈ V ∧ (f ∈ V.nonunits ↔ InMax x f) := by
    intro f hf
    obtain ⟨h1, h2, h3⟩ := hPx.2 f hf
    exact ⟨⟨h1, h2⟩, (hnuV P hPrat f ⟨h1, h2⟩).trans h3⟩
  have hxbFin : xb ∉ Set.range (TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base :=
    N4Aux.not_mem_range_of_not_mem_range ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ V x xb hxV0 hxV hxFin

  obtain ⟨hx'Fin, hx'br⟩ := N4Aux.cuspTransport ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ j' hjfin' hsw3 hsw4 σ hσj' hσFin hσInf'
    V V' hRV hVV' xb x' I hI hxV hx'V hxbFin (fun y hy b hb => hInfℓ y hy b hb)

  refine ⟨γ, hγ, x', ⟨hx'sp, hx'cl, fun y hy => absurd ⟨y, hy⟩ hx'Fin, ?_, fun y hy => absurd ⟨y, hy⟩ hx'Fin⟩, hx'cen⟩
  intro y' hy' b hb
  apply hx'br y' hy' b

  show ((σ.symm (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓb).nonunits
  rw [hσgs]
  rw [hR] at hb
  have key : ∀ f : ↥(fieldBar q M'),
      (levelAutBar q M' ζ γ).toRingEquiv f ∈ (OIg (lineInfty q)).nonunits ↔ f ∈ (OIg ℓb).nonunits :=
    N4Aux.mem_nonunits_iff_of_forall_mem_iff (A := OIg ℓb) (A' := OIg (lineInfty q))
      (levelAutBar q M' ζ γ).toRingEquiv (fun f => by rw [hOIgℓ, ValuationSubring.mem_comap]; rfl)
  rw [← key]
  simpa using hb

end S_ModularCurve_FullLevel_exists_levelAutBar_smul_centred_goodPt_of_centred_of_not_mem_range_iotaFin_twoChartIntegralModel_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_levelAutBar_smul_centred_goodPt_of_centred_of_not_mem_range_iotaFin_twoChartIntegralModel_of_eq_three (solution)
