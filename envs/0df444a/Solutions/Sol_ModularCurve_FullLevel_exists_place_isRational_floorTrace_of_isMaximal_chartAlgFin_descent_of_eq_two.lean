-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/01d247c5-9018-5bbe-b785-b3a8ee609209

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_transcendental_and_finiteDimensional_adjoin_levelField
import Theorems.Thm_ModularCurve_FullLevel_mem_igusaRing_coe_levelField_and_injective_twoChartIntegralModel_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_two
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_ModularCurve_FullLevel_exists_primes_chartAlg_localization_eq_igusaRing_minimal_injective_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_two
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Theorems.Thm_ModularCurve_FullLevel_exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH_of_eq_two
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_qExpand_jqModC_mem_intFormRatiosC_gammaH
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_two_le_ringKrullDim_stalk_of_isMaximal_of_mem
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_two
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

namespace T2Aux

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

end CompositeValuation

end T2Aux

namespace E147B2

open ModularCurve.FullLevel CongruenceSubgroup

theorem coeffMap_subtype_laurentMap_jqInt {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) :
    coeffMap A.subtype (laurentMap (Int.castRingHom ↥A) jqInt) = coeffEmb L jq := by
  rw [← laurentMap_jqInt]
  ext k
  rw [coeffMap_coeff, laurentMap_coeff, coeffEmb_coeff, laurentMap_coeff]
  simp

theorem laurentMap_jqInt_geom (K : Type*) [Field K] : laurentMap (Int.castRingHom K) jqInt = jqModC K := by
  rw [jqModC, jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]

theorem coeffMap_residue_laurentMap_jqInt {L : Type*} [Field L] (A : ValuationSubring L) :
    coeffMap (IsLocalRing.residue ↥A) (laurentMap (Int.castRingHom ↥A) jqInt) = jqModC (ResidueField ↥A) := by
  rw [← laurentMap_jqInt_geom]
  ext k
  rw [coeffMap_coeff, laurentMap_coeff, laurentMap_coeff]
  simp

end E147B2

namespace E147B2

section Restrict

variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def resHom (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring) :
    ↥s.toValuationSubring →+* ↥Q.toValuationSubring where
  toFun x := ⟨j x, (hmem x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem coe_resHom (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring) (x : ↥s.toValuationSubring) :
    ((resHom s Q j hmem x : ↥Q.toValuationSubring) : F') = j x := rfl

theorem resHom_mem_maximalIdeal_iff (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring) (x : ↥s.toValuationSubring) :
    resHom s Q j hmem x ∈ maximalIdeal ↥Q.toValuationSubring ↔ x ∈ maximalIdeal ↥s.toValuationSubring := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff, coe_resHom,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, ← hmem,
    map_eq_zero_iff j j.injective]

scoped instance isLocalHom_resHom (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring) :
    IsLocalHom (resHom s Q j hmem) := by
  constructor
  intro x hx
  by_contra hnu
  have hxm : x ∈ maximalIdeal ↥s.toValuationSubring := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have := (resHom_mem_maximalIdeal_iff s Q j hmem x).mpr hxm
  exact (IsLocalRing.mem_maximalIdeal _).mp this hx

theorem isRational_restrict (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring)
    (hQ : Q.IsRational) (hjK : ∀ c : K, j (algebraMap K F c) = algebraMap K F' c) : s.IsRational := by
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hc⟩ := hQ (IsLocalRing.residue _ (resHom s Q j hmem x))
  refine ⟨c, ?_⟩
  change IsLocalRing.residue _ (algebraMap K ↥s.toValuationSubring c) = IsLocalRing.residue _ x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← resHom_mem_maximalIdeal_iff s Q j hmem,
    ← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero, ← hc]
  have : resHom s Q j hmem (algebraMap K ↥s.toValuationSubring c) = algebraMap K ↥Q.toValuationSubring c :=
    Subtype.ext (hjK c)
  rw [this]
  rfl

theorem evalAt_restrict (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring)
    (hQ : Q.IsRational) (hjK : ∀ c : K, j (algebraMap K F c) = algebraMap K F' c)
    (g : F) (hg : g ∈ s.toValuationSubring) : s.evalAt g = Q.evalAt (j g) := by
  have hs := isRational_restrict s Q j hmem hQ hjK
  have hg' : j g ∈ Q.toValuationSubring := (hmem g).mp hg
  rw [← T2Aux.ev_eq_evalAt s hs g hg, ← T2Aux.ev_eq_evalAt Q hQ (j g) hg']
  apply Q.algebraMap_residueField_injective
  have key : ∀ y : ↥Q.toValuationSubring,
      algebraMap K Q.ResidueField (T2Aux.ev Q hQ y) = IsLocalRing.residue _ y := by
    intro y
    change (T2Aux.resEquiv Q hQ) ((T2Aux.resEquiv Q hQ).symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have key' : ∀ y : ↥s.toValuationSubring,
      algebraMap K s.ResidueField (T2Aux.ev s hs y) = IsLocalRing.residue _ y := by
    intro y
    change (T2Aux.resEquiv s hs) ((T2Aux.resEquiv s hs).symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have hmap : ∀ c : K, IsLocalRing.ResidueField.map (resHom s Q j hmem) (algebraMap K s.ResidueField c) =
      algebraMap K Q.ResidueField c := by
    intro c
    change IsLocalRing.ResidueField.map (resHom s Q j hmem) (IsLocalRing.residue _ (algebraMap K ↥s.toValuationSubring c)) =
      IsLocalRing.residue _ (algebraMap K ↥Q.toValuationSubring c)
    rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    exact Subtype.ext (hjK c)
  rw [key, ← hmap, key', IsLocalRing.ResidueField.map_residue]
  rfl

end Restrict

end E147B2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_two.E147B2"

namespace E140CR

open ModularCurve ModularCurve.FullLevel IsLocalRing AlgebraicCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem isRational_place_xHFunctionFieldC (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (Q : Place (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M'))) :
    Q.IsRational := by
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH _ _)
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI : IsCurveOver (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed _ _ (ModularCurve.translation_mem_GammaH _ _)
  haveI : Module.Finite (ResidueField ↥A) Q.ResidueField := IsCurveOver.finiteResidue Q
  haveI : Algebra.IsIntegral (ResidueField ↥A) Q.ResidueField := Algebra.IsIntegral.of_finite _ _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField ↥A) (K := Q.ResidueField)).2

end E140CR
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_two.E147B2"

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
    (𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫 : 𝔫.IsMaximal)
    (hϖ : algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫)
    :
    ∃ s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'),
      s.IsRational ∧ IsAffineGeomPlace (ResidueField A) M' s ∧

      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A₀, residue A (ι a) =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) =
                (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
              g ∈ 𝔫) ∧

      (∀ a : A₀, residue A (ι a) =
          s.evalAt (jGeomGen (ResidueField A) M') →
        TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a ∈ 𝔫) := by
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

  haveI h𝔫p : 𝔫.IsPrime := h𝔫.isPrime
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  obtain ⟨𝔮, hLOC, hMIN, hINJ, hSURJ⟩ :=
    ModularCurve.FullLevel.exists_primes_chartAlg_localization_eq_igusaRing_minimal_injective_descent_of_eq_two
      q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) (Or.inl rfl)
  have hmap𝔪 : (maximalIdeal A₀).map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) = Ideal.span {algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀} := by
    rw [hϖ₀, Ideal.map_span, Set.image_singleton]
  have h𝔪le : (maximalIdeal A₀).map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) ≤ 𝔫 := by
    rw [hmap𝔪, Ideal.span_singleton_le_iff_mem]; exact hϖ
  obtain ⟨q', hq'min, hq'le⟩ := Ideal.exists_minimalPrimes_le h𝔪le
  obtain ⟨ℓ, rfl⟩ := hSURJ q' hq'min
  haveI h𝔮p : (𝔮 ℓ).IsPrime := (hMIN ℓ).1.1

  have hCVℓ : ∀ c : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (c : ↥F₀) ∈ ((OIg ℓ).comap F₀.subtype) := by
    intro c
    rw [ValuationSubring.mem_comap]
    exact (hLOC ℓ _).mpr ⟨c, 1, fun h => h𝔮p.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rw [OneMemClass.coe_one, mul_one]⟩
  have hcenℓ : ∀ c : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∈ 𝔮 ℓ ↔ (c : ↥F₀) ∈ (((OIg ℓ).comap F₀.subtype)).nonunits := by
    intro c
    constructor
    · intro hc
      rw [ValuationSubring.mem_nonunits_iff_or]
      by_cases hc0 : (c : ↥F₀) = 0
      · exact Or.inl hc0
      · right
        intro hinv
        rw [ValuationSubring.mem_comap] at hinv
        obtain ⟨b, c', hc', hbc⟩ := (hLOC ℓ ((c : ↥F₀))⁻¹).mp hinv
        apply hc'
        have : c' = c * b := by
          apply Subtype.ext
          rw [Subalgebra.coe_mul, ← hbc, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
        rw [this]; exact Ideal.mul_mem_right _ _ hc
    · intro hc
      by_contra hcq
      have hinv : ((c : ↥F₀))⁻¹ ∈ ((OIg ℓ).comap F₀.subtype) := by
        rw [ValuationSubring.mem_comap]
        refine (hLOC ℓ ((c : ↥F₀))⁻¹).mpr ⟨1, c, hcq, ?_⟩
        have hc0 : (c : ↥F₀) ≠ 0 := by
          intro h0; apply hcq
          rw [show c = 0 from Subtype.ext h0]; exact (𝔮 ℓ).zero_mem
        rw [OneMemClass.coe_one, inv_mul_cancel₀ hc0]
      rw [ValuationSubring.mem_nonunits_iff_or] at hc
      rcases hc with h0 | hni
      · apply hcq; rw [show c = 0 from Subtype.ext h0]; exact (𝔮 ℓ).zero_mem
      · exact hni hinv

  obtain ⟨ρ, hρalg, τ, hτ, hρA, hρf⟩ :=
    ModularCurve.FullLevel.exists_ringHom_residueField_igusaRing_xHFunctionFieldC_reading_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ ℓ
  let ψC : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* ↥((OIg ℓ).comap F₀.subtype) :=
    ((TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).val.toRingHom).codRestrict ((OIg ℓ).comap F₀.subtype) hCVℓ
  let θ : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) := ρ.comp ((IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype)).comp ψC)
  have hθ : ∀ c : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), θ c = ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(c : ↥F₀), hCVℓ c⟩) := fun _ => rfl
  have hθker : ∀ c : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), θ c = 0 ↔ c ∈ 𝔮 ℓ := by
    intro c
    rw [hθ, map_eq_zero_iff ρ ρ.injective, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff, hcenℓ]
  have hθA : ∀ a : A₀, θ (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a) = algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) (IsLocalRing.residue ↥A (ι a)) :=
    fun a => hρA a (hCVℓ (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a))

  have hne : 𝔫 ≠ 𝔮 ℓ := by
    intro heq
    haveI : IsNoetherianRing ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := by
      haveI := (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A₀
        ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) htj0 hFDF hsepF).1
      exact Algebra.FiniteType.isNoetherianRing A₀ _
    have h1 : 𝔫.height ≤ 1 := by
      rw [heq]
      haveI : (Ideal.span {algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀}).IsPrincipal := ⟨⟨_, rfl⟩⟩
      exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ (hmap𝔪 ▸ hMIN ℓ)
    obtain ⟨est, -, -⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
      A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) _ ⟨𝔫, h𝔫p⟩ rfl
    have h2 := AlgebraicCurve.TwoChartIntegralModel.two_le_ringKrullDim_stalk_of_isMaximal_of_mem A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) htj0 ϖ₀ hϖ₀
      ⟨𝔫, h𝔫p⟩ h𝔫 hϖ
    rw [RingEquiv.ringKrullDim est.commRingCatIsoToRingEquiv,
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔫 (Localization.AtPrime 𝔫)] at h2
    have h3 : (2 : WithBot ℕ∞) ≤ 1 := h2.trans (WithBot.coe_le_coe.mpr h1)
    exact absurd h3 (by decide)
  have hkerle : RingHom.ker θ.rangeRestrict ≤ 𝔫 := by
    intro c hc
    rw [RingHom.mem_ker] at hc
    have : θ c = 0 := congrArg Subtype.val hc
    exact hq'le ((hθker c).mp this)
  have hI : Ideal.map θ.rangeRestrict 𝔫 ≠ ⊤ := by
    intro htop
    have := Ideal.comap_map_of_surjective θ.rangeRestrict θ.rangeRestrict_surjective 𝔫
    rw [htop, Ideal.comap_top, sup_eq_left.mpr (by rwa [← RingHom.ker_eq_comap_bot])] at this
    exact h𝔫p.ne_top this.symm
  obtain ⟨B', hB'le, hB'n⟩ := Ideal.image_subset_nonunits_valuationSubring (A := θ.range) (Ideal.map θ.rangeRestrict 𝔫) hI
  have hθB' : ∀ c : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), θ c ∈ B' := fun c => hB'le ⟨c, rfl⟩
  have h𝔫B' : ∀ c ∈ 𝔫, θ c ∈ B'.nonunits := fun c hc => hB'n ⟨⟨θ c, ⟨c, rfl⟩⟩, Ideal.mem_map_of_mem _ hc, rfl⟩
  have hcen : ∀ c : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∈ 𝔫 ↔ θ c ∈ B'.nonunits := by
    let θ' : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* ↥B' := θ.codRestrict B' hθB'
    have hJle : 𝔫 ≤ (maximalIdeal ↥B').comap θ' := fun c hc => by
      rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; exact h𝔫B' c hc
    have hJ : 𝔫 = (maximalIdeal ↥B').comap θ' :=
      h𝔫.eq_of_le (Ideal.IsPrime.ne_top (Ideal.comap_isPrime θ' _)) hJle
    intro c
    rw [hJ, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    exact Iff.rfl
  have hB'top : B' ≠ ⊤ := by
    intro htop
    obtain ⟨c, hc𝔫, hcℓ⟩ := SetLike.not_le_iff_exists.mp (fun h : 𝔫 ≤ 𝔮 ℓ => hne (le_antisymm h hq'le))
    have h1 := h𝔫B' c hc𝔫
    rw [htop, ValuationSubring.mem_nonunits_iff_or] at h1
    rcases h1 with h0 | hni
    · exact hcℓ ((hθker c).mp h0)
    · exact hni (ValuationSubring.mem_top _)
  have hκB' : ∀ c : ResidueField ↥A, algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) c ∈ B' := by
    intro c
    obtain ⟨a, ha⟩ := hres c
    rw [← ha, RingHom.comp_apply, ← hθA]
    exact hθB' _

  obtain ⟨t, ht⟩ := ModularCurve.FullLevel.exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH_of_eq_two q hq2 M' hqM' A hA
  haveI := ht
  obtain ⟨Q, hQ⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional t B' hκB' hB'top
  have hQrat : Q.IsRational := E140CR.isRational_place_xHFunctionFieldC q M' A Q

  have hCΛ : ∀ c : ResidueField ↥A, algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c = HahnSeries.C c := by
    intro c
    rw [HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]
  have hτC : ∀ c : ResidueField ↥A, τ (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c) = algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c := by
    intro c
    rcases hτ with rfl | rfl
    · rfl
    · rw [hCΛ, qExpand_C]
  have hgen : ∀ N' : ℕ, ∀ (_ : NeZero N'), N' ∣ q ^ 2 * M' →
      qExpand (ResidueField ↥A) N' (jqModC (ResidueField ↥A)) ∈ xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M') := by
    intro N' _ hN'
    exact intFormRatiosC_subset _ _ (ModularCurve.qExpand_jqModC_mem_intFormRatiosC_gammaH (ResidueField ↥A) (q ^ 2 * M') N' hN' (levelH q M'))
  have hτmem : ∀ x : ↥(modularFunctionFieldC (ResidueField ↥A) M'), τ (x : LaurentSeries (ResidueField ↥A)) ∈ xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M') := by
    let T : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) :=
      Subfield.toIntermediateField ((xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')).toSubfield.comap τ) (fun c => by
        show τ (algebraMap _ _ c) ∈ xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')
        rw [hτC]; exact IntermediateField.algebraMap_mem _ c)
    have hle : modularFunctionFieldC (ResidueField ↥A) M' ≤ T := by
      rw [modularFunctionFieldC, IntermediateField.adjoin_le_iff]
      intro y hy
      show τ y ∈ xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')
      rcases hy with rfl | hy
      · rcases hτ with rfl | rfl
        · have := hgen 1 inferInstance (one_dvd _); rwa [qExpand_one_apply] at this
        · exact hgen (q ^ 2) inferInstance (Dvd.intro _ rfl)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rcases hτ with rfl | rfl
        · exact hgen M' inferInstance (Dvd.intro_left _ rfl)
        · show qExpand _ (q ^ 2) (qExpand _ M' (jqModC _)) ∈ _
          rw [qExpand_qExpand]
          haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
          exact hgen (q ^ 2 * M') inferInstance dvd_rfl
    intro x
    exact hle x.2
  let jτ : ↥(modularFunctionFieldC (ResidueField ↥A) M') →+* ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) :=
    (τ.comp (modularFunctionFieldC (ResidueField ↥A) M').val.toRingHom).codRestrict (xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) (fun x => hτmem x)
  have hjτ : ∀ x : ↥(modularFunctionFieldC (ResidueField ↥A) M'), ((jτ x : ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField ↥A)) = τ (x : LaurentSeries (ResidueField ↥A)) := fun _ => rfl
  have hjK : ∀ c : ResidueField ↥A, jτ (algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') c) = algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) c := by
    intro c
    apply Subtype.ext
    show τ (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c) = algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c
    exact hτC c

  let O : ValuationSubring ↥(modularFunctionFieldC (ResidueField ↥A) M') := Q.toValuationSubring.comap jτ
  have hOK : ∀ c : ResidueField ↥A, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') c ∈ O := by
    intro c
    rw [ValuationSubring.mem_comap, hjK]
    exact Q.algebraMap_mem' c
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hall : ∀ g : ↥(modularFunctionFieldC (ResidueField ↥A) M'), jτ g ∈ Q.toValuationSubring := by
      intro g
      have : g ∈ O := by rw [htop]; exact ValuationSubring.mem_top g
      exact ValuationSubring.mem_comap.mp this
    have hg0 : jGeomGen (ResidueField ↥A) M' - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') (Q.evalAt (jτ (jGeomGen (ResidueField ↥A) M'))) ≠ 0 := by
      intro h
      have halg : IsAlgebraic (ResidueField ↥A) (jGeomGen (ResidueField ↥A) M') := by
        rw [sub_eq_zero.mp h]
        exact isAlgebraic_algebraMap _
      exact ModularCurve.transcendental_jqModC (ResidueField ↥A) (IntermediateField.isAlgebraic_iff.mp halg)
    have hunit : Q.evalAt (jτ (jGeomGen (ResidueField ↥A) M' - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') (Q.evalAt (jτ (jGeomGen (ResidueField ↥A) M'))))) ≠ 0 := by
      rw [Ne, T2Aux.evalAt_eq_zero_iff Q hQrat (hall _), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      refine isUnit_iff_exists_inv.mpr ⟨⟨jτ (jGeomGen (ResidueField ↥A) M' - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') (Q.evalAt (jτ (jGeomGen (ResidueField ↥A) M'))))⁻¹, hall _⟩, Subtype.ext ?_⟩
      change jτ _ * jτ _ = 1
      rw [← map_mul, mul_inv_cancel₀ hg0, map_one]
    apply hunit
    rw [map_sub, T2Aux.evalAt_sub Q hQrat (hall _) (hall _), hjK, T2Aux.evalAt_algebraMap Q hQrat, sub_self]
  haveI := ModularCurve.finiteDimensional_adjoin_jqModC (N := M') A
  obtain ⟨s, hs⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional
    ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M'⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M'))) O hOK hOtop
  have hmem : ∀ g : ↥(modularFunctionFieldC (ResidueField ↥A) M'), g ∈ s.toValuationSubring ↔ jτ g ∈ Q.toValuationSubring := by
    intro g; rw [hs]; exact ValuationSubring.mem_comap
  have hsrat : s.IsRational := E147B2.isRational_restrict s Q jτ hmem hQrat hjK

  have hread : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers) (a : A₀) (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))),
      ((g : ↥F₀) : ↥(fieldBar q M')) = (IntermediateField.inclusion hle f : ↥(fieldBar q M')) -
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
      θ g = jτ (R₀.residue ⟨f, hf⟩) - algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) (IsLocalRing.residue ↥A (ι a)) := by
    intro f hf a g hg
    apply Subtype.ext
    rw [hθ, hρf f hf a g (hCVℓ g) hg]
    show _ = ((jτ (R₀.residue ⟨f, hf⟩) : ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField ↥A)) - ((algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) (IsLocalRing.residue ↥A (ι a)) : ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField ↥A))
    rw [hjτ]
    rfl

  have hyA := E147B2.coeffMap_subtype_laurentMap_jqInt A
  have hy : coeffMap A.subtype (laurentMap (Int.castRingHom ↥A) jqInt) ∈ modularFunctionFieldBar M' := by
    rw [hyA]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨hjint', hjres'⟩ := hR₀ _ hy
  have efm : (⟨coeffMap A.subtype (laurentMap (Int.castRingHom ↥A) jqInt), hy⟩ : ↥(modularFunctionFieldBar M')) = (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) :=
    Subtype.ext hyA
  have hjint : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers := efm ▸ hjint'
  have hjres : R₀.residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), hjint⟩ = jGeomGen (ResidueField ↥A) M' := by
    have key : R₀.residue ⟨_, hjint'⟩ = R₀.residue ⟨_, hjint⟩ := by congr 1; exact Subtype.ext efm
    rw [← key]
    apply Subtype.ext
    rw [hjres', E147B2.coeffMap_residue_laurentMap_jqInt]
    rfl
  have hθj : θ (TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) = jτ (jGeomGen (ResidueField ↥A) M') := by
    have := hread (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hjint 0 (TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (by
      rw [map_zero, ZeroMemClass.coe_zero, map_zero, sub_zero]; rfl)
    rw [this, hjres, map_zero, map_zero, map_zero, sub_zero]

  have hjQ : jτ (jGeomGen (ResidueField ↥A) M') ∈ Q.toValuationSubring := by rw [← hθj, hQ]; exact hθB' _
  have hjs : jGeomGen (ResidueField ↥A) M' ∈ s.toValuationSubring := (hmem _).mpr hjQ
  have haff : IsAffineGeomPlace (ResidueField ↥A) M' s := by
    rcases ModularCurve.isAffineGeomPlace_or_ord_jGeomGen_lt_zero (ResidueField ↥A) M' s with h | h
    · exact h
    · exact absurd h (not_lt.mpr (AlgebraicCurve.Place.ord_nonneg_of_mem s hjs))
  have hclause : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈ s.toValuationSubring →
      ∀ a : A₀, residue A (ι a) = s.evalAt (R₀.residue ⟨f, hf⟩) →
        ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) =
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
          g ∈ 𝔫 := by
    intro f hf _ hfs a ha g hg
    have hfQ : jτ (R₀.residue ⟨f, hf⟩) ∈ Q.toValuationSubring := (hmem _).mp hfs
    have hval : Q.evalAt (jτ (R₀.residue ⟨f, hf⟩)) = residue A (ι a) := by
      rw [← E147B2.evalAt_restrict s Q jτ hmem hQrat hjK _ hfs]; exact ha.symm
    have hθg := hread f hf a g hg
    have hθgQ : θ g ∈ Q.toValuationSubring := by rw [hQ]; exact hθB' g
    have h0 : Q.evalAt (θ g) = 0 := by
      rw [hθg, T2Aux.evalAt_sub Q hQrat hfQ (Q.algebraMap_mem' _), hval, T2Aux.evalAt_algebraMap Q hQrat, sub_self]
    have h1 := (T2Aux.evalAt_eq_zero_iff Q hQrat hθgQ).mp h0
    rw [hcen, ← hQ]
    exact ValuationSubring.coe_mem_nonunits_iff.mpr h1
  refine ⟨s, hsrat, haff, hclause, ?_⟩
  intro a ha
  have hg : (((TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) : ↥(fieldBar q M')) =
      (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) -
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) := by
    rw [← hj₀ a]
    rfl
  rw [← hjres] at ha
  exact hclause (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hjint (fun P h => h) (by rw [hjres]; exact hjs) a ha _ hg

end S_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_place_isRational_floorTrace_of_isMaximal_chartAlgFin_descent_of_eq_two (solution)
