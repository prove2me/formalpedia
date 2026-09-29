-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ad46d913-dd3e-51b9-90d1-7e46907bc663

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularCurve_XHDRModelAtP_crossingPt_mem_preimage_iotaFin
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_modularUnit_mem_and_inv_mem_and_div_mem_of_valuationSubring_pair_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01"
p2m_attr_erase "simp" "CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun"
p2m_attr_erase "simp" "KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

section KerMin
p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel AlgebraicCurve.TwoChartIntegralModel"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.XO XHDRLevel.baseGerm XHDRModelAtP translation_mem_GammaH qExpFunctionFieldC jq coeffEmb coeffEmb_coeff jqModC IgusaScheme modularUnitSeries_ne_zero XHDRModelAtP.crossingPt_mem_preimage_iotaFin XHDRModelAtP.exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar XHDRLevel.exists_valuationSubring_pair_gammaH XHDRModelAtP.exists_modularUnit_mem_and_inv_mem_and_div_mem_of_valuationSubring_pair_chartAlgFin transcendental_of_coe_eq_coeffEmb_jq finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "XO bcMap bcMap_fst baseGerm R jAt coe_jAt X toBase chartAlgFin ιFin fibre ΓM exists_ogg_unit_pair_chartAlgFin_gammaH exists_valuationSubring_pair_gammaH"
namespace KerMinH
p2m_open "ModularCurve.XHDRLevel ModularCurve"

variable (p : ℕ) [Fact p.Prime]

scoped instance instDVR_R : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out

theorem maximalIdeal_R : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out

theorem mem_maximalIdeal_iff_mem_span (a : ↥(GaloisRep.ratLocalizedAt p)) :
    a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) ↔ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := by rw [maximalIdeal_R]

theorem p_ne_zero_R : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem irreducible_p : Irreducible ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (p_ne_zero_R p) (maximalIdeal_R p)

theorem prime_p : Prime ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := (irreducible_p p).prime

theorem res_eq_zero_iff (r : ↥(GaloisRep.ratLocalizedAt p)) : GaloisRep.ratLocalizedAtResidue p r = 0 ↔ ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ r := by
  rw [← Ideal.mem_span_singleton, ← maximalIdeal_R]
  constructor
  · intro hr
    by_contra h
    have hu : IsUnit r := by rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
    exact (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hr
  · intro hr
    rw [maximalIdeal_R, Ideal.mem_span_singleton] at hr
    obtain ⟨t, rfl⟩ := hr
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem residue_eq_zero_iff' (r : ↥(GaloisRep.ratLocalizedAt p)) :
    IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p) r = 0 ↔ GaloisRep.ratLocalizedAtResidue p r = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, res_eq_zero_iff, ← Ideal.mem_span_singleton, maximalIdeal_R]

theorem map_residue_ne_zero_iff (Q : Polynomial ↥(GaloisRep.ratLocalizedAt p)) :
    Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 ↔ Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩ <;> ext n <;> have hn := congrArg (fun P : Polynomial _ => P.coeff n) h <;>
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hn ⊢
  · exact (residue_eq_zero_iff' p _).mp hn
  · exact (residue_eq_zero_iff' p _).mpr hn

theorem map_ne_zero_iff_not_C_dvd (Q : Polynomial ↥(GaloisRep.ratLocalizedAt p)) :
    Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ↔ ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ Q) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  refine not_congr ⟨fun h n => (res_eq_zero_iff p _).mp ?_, fun h => ?_⟩
  · have hn := congrArg (fun P : Polynomial _ => P.coeff n) h
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hn
  · ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (res_eq_zero_iff p _).mpr (h n)

scoped instance instIsFractionRing_R : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

theorem ringHom_ext_R {S : Type*} [Semiring S] (f g : ↥(GaloisRep.ratLocalizedAt p) →+* S) : f = g := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

theorem isScalarTower_R (Γ : Subgroup SL(2, ℤ)) (inst : Algebra ℚ ↥(qExpFunctionFieldC ℚ Γ)) :
    @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) _ (@Algebra.toSMul _ _ _ _ inst) _ :=
  @IsScalarTower.of_algebraMap_eq ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ _ _ inst _ fun a =>
    RingHom.congr_fun (ringHom_ext_R p (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ))
      ((@algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ inst).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) a

scoped instance instIsScalarTower (Γ : Subgroup SL(2, ℤ)) : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) :=
  isScalarTower_R p Γ inferInstance

theorem coeffEmb_rat (x : LaurentSeries ℚ) : coeffEmb ℚ x = x := by
  ext k
  rw [coeffEmb_coeff]
  rfl

theorem coe_jAt_eq_coeffEmb (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ((jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = coeffEmb ℚ jq := by
  rw [coeffEmb_rat, coe_jAt]
  rfl

theorem transcendental_iff_of_inst (Γ : Subgroup SL(2, ℤ)) (i₁ i₂ : Algebra ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ))
    (x : ↥(qExpFunctionFieldC ℚ Γ)) :
    @Transcendental ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₁ x ↔
      @Transcendental ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₂ x := by
  have h : @algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₁ =
      @algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₂ := ringHom_ext_R p _ _
  unfold Transcendental IsAlgebraic
  refine not_congr ⟨?_, ?_⟩ <;> rintro ⟨q, hq, hx⟩ <;> refine ⟨q, hq, ?_⟩
  · rw [@Polynomial.aeval_def _ _ _ _ i₂, ← h, ← @Polynomial.aeval_def _ _ _ _ i₁]; exact hx
  · rw [@Polynomial.aeval_def _ _ _ _ i₁, h, ← @Polynomial.aeval_def _ _ _ _ i₂]; exact hx

p2m_attr_erase "instance" "DivisionRing.toRatAlgebra in"

theorem transcendental_jAt_IF (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Transcendental ↥(GaloisRep.ratLocalizedAt p) (jAt Γ hj) := by
  have hst := IsScalarTower.of_algebraMap_eq (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ℚ)
    (A := ↥(qExpFunctionFieldC ℚ Γ)) (fun _ => rfl)
  exact @ModularCurve.transcendental_of_coe_eq_coeffEmb_jq ℚ _ _ (qExpFunctionFieldC ℚ Γ) ↥(GaloisRep.ratLocalizedAt p)
    _ _ _ _ _ hst (jAt Γ hj) (coe_jAt_eq_coeffEmb Γ hj)

theorem transcendental_jAt (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Transcendental ↥(GaloisRep.ratLocalizedAt p) (jAt Γ hj) :=
  (transcendental_iff_of_inst p Γ _ _ _).mp (transcendental_jAt_IF p Γ hj)

universe u in
theorem minimalPrimes_span_natCast_chartAlgFin_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))
      ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))
      ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :
    ∃ W₀ W₁ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),

      (∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
        ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits) ∧
      W₀ ≠ W₁ ∧
      (∀ i : Fin 2, ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ (![W₀, W₁] i).nonunits →
        x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) _ ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ (![W₀, W₁] i)) ∧

      (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
        (∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits) ∨
        (∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits)) ∧

      (∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
        ∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ (![W₀, W₁] i).nonunits) ∧

      (∃ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits ∧
          (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₁.nonunits) ∧
      (∃ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits ∧
          (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₀.nonunits) := by
  obtain ⟨W₀, W₁, h1, h2, h3, h5, h6⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_pair_gammaH p M H hpM hpM2 hHp hj

  have h1' : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits :=
    fun i => ⟨(h1 i).1, fun a ha => (h1 i).2 a ((mem_maximalIdeal_iff_mem_span p a).mp ha)⟩
  have h2' : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i) :=
    fun i Q hQ => h2 i Q ((map_residue_ne_zero_iff p Q).mp hQ)
  have h5' : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ :=
    fun V hV1 hV1' hV2 => h5 V hV1 (fun a ha => hV1' a ((mem_maximalIdeal_iff_mem_span p a).mpr ha))
      (fun Q hQ => hV2 Q ((map_residue_ne_zero_iff p Q).mpr hQ))
  haveI := hFD; haveI := hsep
  haveI := instIsScalarTower p (CohCarrier.GammaH M H)
  have hϖ : Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgFin p (CohCarrier.GammaH M H) hj) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} =
      Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))} := by rw [map_natCast]
  obtain ⟨hi, hii, hiii⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)
      (transcendental_jAt p _ hj) hFD hsep ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (maximalIdeal_R p) W₀ W₁ h1' h2' h3 h5'
  rw [hϖ] at hi hii
  exact ⟨W₀, W₁, h1, h3, h6, hi, hii, hiii⟩

theorem kerMin_of_pair
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (W₀ W₁ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW1 : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits)
    (hW2 : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i))
    (hW3 : W₀ ≠ W₁)
    (hW5 : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V) →
      (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁) :
    (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
      (∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits) ∨
      (∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits)) ∧
    (∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
      ∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ (![W₀, W₁] i).nonunits) ∧
    (∃ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits ∧ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₁.nonunits) ∧
    (∃ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits ∧ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₀.nonunits) := by
  have h1' : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits :=
    fun i => ⟨(hW1 i).1, fun a ha => (hW1 i).2 a ((mem_maximalIdeal_iff_mem_span p a).mp ha)⟩
  have h2' : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i) :=
    fun i Q hQ => hW2 i Q ((map_residue_ne_zero_iff p Q).mp hQ)
  have h5' : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ :=
    fun V hV1 hV1' hV2 => hW5 V hV1 (fun a ha => hV1' a ((mem_maximalIdeal_iff_mem_span p a).mpr ha))
      (fun Q hQ => hV2 Q ((map_residue_ne_zero_iff p Q).mpr hQ))
  haveI := hFD; haveI := hsep
  haveI := instIsScalarTower p (CohCarrier.GammaH M H)
  have hϖ : Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgFin p (CohCarrier.GammaH M H) hj) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} = Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))} := by rw [map_natCast]
  obtain ⟨hi, hii, hiii⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj) (transcendental_jAt p _ hj) hFD hsep ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (maximalIdeal_R p) W₀ W₁ h1' h2' hW3 h5'
  rw [hϖ] at hi hii
  exact ⟨hi, hii, hiii⟩

theorem finiteDimensional_adjoin_jAt (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt Γ hj} : Set ↥(qExpFunctionFieldC ℚ Γ))) ↥(qExpFunctionFieldC ℚ Γ) := by

  have h := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ Γ hT Γ le_rfl
    (fun γ hγ => Or.inl hγ) (jAt Γ hj) (coe_jAt Γ hj)).1
  convert h <;> exact Subsingleton.elim _ _

theorem isSeparable_adjoin_jAt (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({jAt Γ hj} : Set ↥(qExpFunctionFieldC ℚ Γ))) ↥(qExpFunctionFieldC ℚ Γ) := by
  haveI := finiteDimensional_adjoin_jAt Γ hT hj
  infer_instance

end ModularCurve.XHDRLevel.KerMinH
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel.KerMinH"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve"
end KerMin
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel.KerMinH"

noncomputable section

namespace OggTH

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel AlgebraicCurve"
open scoped TensorProduct MatrixGroups

theorem comp_base_apply' {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).base x = g.base (f.base x) := rfl

namespace RingStalk

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (O : Type) [CommRing O] [Algebra (R p) O]

private abbrev _root_.OggTH.RingStalk.XO : Scheme.{0} := pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) O)))

p2m_export "OggTH.RingStalk" "XO"

abbrev PFin := pullback (ιFin p Γ hj) (pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) O))))

abbrev gFin : PFin p Γ hj O ⟶ XO p Γ hj O := pullback.snd _ _

def isoFin : PFin p Γ hj O ≅ Spec (CommRingCat.of (↥(chartAlgFin p Γ hj) ⊗[R p] O)) :=
  pullbackRightPullbackFstIso (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) O))) (ιFin p Γ hj) ≪≫
    pullback.congrHom ((AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj))) rfl ≪≫ pullbackSpecIso (R p) ↥(chartAlgFin p Γ hj) O

def chartFin : Spec (CommRingCat.of (↥(chartAlgFin p Γ hj) ⊗[R p] O)) ⟶ XO p Γ hj O :=
  (isoFin p Γ hj O).inv ≫ gFin p Γ hj O

scoped instance : IsOpenImmersion (chartFin p Γ hj O) := by
  unfold chartFin; infer_instance

theorem chartFin_fst : chartFin p Γ hj O ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥(chartAlgFin p Γ hj)) (B := O))) ≫
      ιFin p Γ hj := by
  have hc : gFin p Γ hj O ≫ pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) O))) =
      pullback.fst (ιFin p Γ hj) _ ≫ ιFin p Γ hj := pullback.condition.symm
  unfold chartFin isoFin
  simp only [Iso.trans_inv, Category.assoc, hc]
  rw [pullbackRightPullbackFstIso_inv_fst_assoc, pullback.congrHom_inv]
  erw [pullback.lift_fst_assoc]
  rw [Category.comp_id, pullbackSpecIso_inv_fst_assoc]

theorem chartFin_snd : chartFin p Γ hj O ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥(chartAlgFin p Γ hj)) (B := O)).toRingHom) := by
  have hc : gFin p Γ hj O ≫ pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) O))) =
      pullback.snd (ιFin p Γ hj) _ ≫ pullback.snd _ _ := rfl
  unfold chartFin isoFin
  simp only [Iso.trans_inv, Category.assoc, hc]
  rw [pullbackRightPullbackFstIso_inv_snd_snd, pullback.congrHom_inv]
  erw [pullback.lift_snd]
  rw [Category.comp_id, pullbackSpecIso_inv_snd]
  rfl

theorem chartFin_comp_map {O' : Type} [CommRing O'] [Algebra (R p) O'] (φ : O →ₐ[R p] O')
    (h₁ : toBase p Γ hj ≫ 𝟙 _ = 𝟙 _ ≫ toBase p Γ hj)
    (h₂ : Spec.map (CommRingCat.ofHom (algebraMap (R p) O')) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) O))) :
    chartFin p Γ hj O' ≫ pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) h₁ h₂ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (R p) ↥(chartAlgFin p Γ hj)) φ).toRingHom) ≫
        chartFin p Γ hj O := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, chartFin_fst, Category.comp_id, Category.assoc, chartFin_fst,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    ext a
    simp
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, chartFin_snd, Category.assoc, chartFin_snd, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2

theorem range_chartFin : Set.range (chartFin p Γ hj O).base =
    (pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) O)))).base ⁻¹' Set.range (ιFin p Γ hj).base := by
  rw [chartFin, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hsurj : Function.Surjective (isoFin p Γ hj O).inv.base := (isoFin p Γ hj O).inv.homeomorph.surjective
  rw [hsurj.range_eq, Set.image_univ, IsOpenImmersion.range_pullbackSnd]
  rfl

@[reducible] private noncomputable def _root_.OggTH.RingStalk.instCommRingChartTensor :
    CommRing (↥(chartAlgFin p Γ hj) ⊗[R p] O) := inferInstance
attribute [local instance] OggTH.RingStalk.instCommRingChartTensor

private def _root_.OggTH.RingStalk.stalkIso (𝔮 : PrimeSpectrum (↥(chartAlgFin p Γ hj) ⊗[R p] O)) :
    (XO p Γ hj O).presheaf.stalk ((chartFin p Γ hj O).base 𝔮) ≅ CommRingCat.of (Localization.AtPrime 𝔮.asIdeal) :=
  asIso ((chartFin p Γ hj O).stalkMap 𝔮) ≪≫ Spec.stalkIso (CommRingCat.of (↥(chartAlgFin p Γ hj) ⊗[R p] O)) 𝔮

p2m_export "OggTH.RingStalk" "stalkIso"
theorem mem_image_top (𝔮 : PrimeSpectrum (↥(chartAlgFin p Γ hj) ⊗[R p] O)) :
    (chartFin p Γ hj O).base 𝔮 ∈ (chartFin p Γ hj O) ''ᵁ ⊤ := ⟨𝔮, trivial, rfl⟩

def sectionOf (r : ↥(chartAlgFin p Γ hj) ⊗[R p] O) : Γ(XO p Γ hj O, (chartFin p Γ hj O) ''ᵁ ⊤) :=
  ((chartFin p Γ hj O).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin p Γ hj) ⊗[R p] O))).inv r)

set_option maxHeartbeats 6400000 in

theorem stalkIso_germ_sectionOf (𝔮 : PrimeSpectrum (↥(chartAlgFin p Γ hj) ⊗[R p] O)) (r : ↥(chartAlgFin p Γ hj) ⊗[R p] O) :
    (stalkIso p Γ hj O 𝔮).hom ((XO p Γ hj O).presheaf.germ ((chartFin p Γ hj O) ''ᵁ ⊤) ((chartFin p Γ hj O).base 𝔮)
        (mem_image_top p Γ hj O 𝔮) (sectionOf p Γ hj O r)) =
      algebraMap _ (Localization.AtPrime 𝔮.asIdeal) r := by
  have h1 := Scheme.Hom.germ_stalkMap (chartFin p Γ hj O) ((chartFin p Γ hj O) ''ᵁ ⊤) 𝔮 (mem_image_top p Γ hj O 𝔮)
  have h2 := Spec.germ_stalkMapIso_hom (R := CommRingCat.of (↥(chartAlgFin p Γ hj) ⊗[R p] O)) 𝔮
  have h2' : ∀ s, (Spec.stalkIso (CommRingCat.of (↥(chartAlgFin p Γ hj) ⊗[R p] O)) 𝔮).hom
      ((Spec (CommRingCat.of (↥(chartAlgFin p Γ hj) ⊗[R p] O))).presheaf.germ ⊤ 𝔮 trivial s) =
      algebraMap _ (Localization.AtPrime 𝔮.asIdeal) ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin p Γ hj) ⊗[R p] O))).hom s) := by
    intro s
    have := congrArg (fun φ => φ.hom s) h2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  simp only [stalkIso, sectionOf, Iso.trans_hom, asIso_hom, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply ((XO p Γ hj O).presheaf.germ _ _ (mem_image_top p Γ hj O 𝔮))
    ((chartFin p Γ hj O).stalkMap 𝔮), h1, ConcreteCategory.comp_apply, Scheme.Hom.appIso_inv_app_apply,
    TopCat.Presheaf.germ_res_apply]
  erw [h2']
  simp

theorem isUnit_iff_of_iso {A B : CommRingCat} (e : A ≅ B) (a : A) : IsUnit a ↔ IsUnit (e.hom a) := by
  constructor
  · exact fun h => h.map e.hom.hom
  · intro h
    have := h.map e.inv.hom
    simpa using this

theorem isUnit_germ_sectionOf_iff {w : ↥(XO p Γ hj O)} (𝔔 : PrimeSpectrum (↥(chartAlgFin p Γ hj) ⊗[R p] O))
    (hw : w = (chartFin p Γ hj O).base 𝔔) (hwU : w ∈ (chartFin p Γ hj O) ''ᵁ ⊤) (r : ↥(chartAlgFin p Γ hj) ⊗[R p] O) :
    IsUnit ((XO p Γ hj O).presheaf.germ _ w hwU (sectionOf p Γ hj O r)) ↔ r ∉ 𝔔.asIdeal := by
  subst hw
  rw [isUnit_iff_of_iso (stalkIso p Γ hj O 𝔔), stalkIso_germ_sectionOf]
  exact IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔔.asIdeal r

theorem germ_sectionOf_mem_maximalIdeal_iff {w : ↥(XO p Γ hj O)} (𝔔 : PrimeSpectrum (↥(chartAlgFin p Γ hj) ⊗[R p] O))
    (hw : w = (chartFin p Γ hj O).base 𝔔) (hwU : w ∈ (chartFin p Γ hj O) ''ᵁ ⊤) (r : ↥(chartAlgFin p Γ hj) ⊗[R p] O) :
    (XO p Γ hj O).presheaf.germ _ w hwU (sectionOf p Γ hj O r) ∈ IsLocalRing.maximalIdeal _ ↔ r ∈ 𝔔.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_germ_sectionOf_iff p Γ hj O 𝔔 hw hwU r, not_not]

theorem fst_chartFin (𝔔 : PrimeSpectrum (↥(chartAlgFin p Γ hj) ⊗[R p] O)) :
    (pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) O)))).base ((chartFin p Γ hj O).base 𝔔) =
      (ιFin p Γ hj).base (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥(chartAlgFin p Γ hj)) (B := O)) 𝔔) := by
  rw [← comp_base_apply', chartFin_fst, comp_base_apply']
  rfl

end RingStalk
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTH.RingStalk"

set_option maxHeartbeats 12800000 in
open RingStalk in
theorem main
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hinf : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)
    (hzero : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) :
    ∃ t t' : (XHDRLevel.XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n),
      t * t' = baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ((p : ℕ) : O) ^ 12 ∧
      t ∈ IsLocalRing.maximalIdeal ((XHDRLevel.XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)) ∧
      (IsUnit (((XHDRLevel.XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hinf).hom t) ∨
        IsUnit (((XHDRLevel.XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hzero).hom t)) := by
  classical
  letI : Algebra (R p) O := ρO.toAlgebra
  have hpP : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpP.ne_zero⟩
  set κ := IsLocalRing.ResidueField ↥A with hκ
  set τ : R p →+* κ := (IsLocalRing.residue ↥A).comp ρ with hτ

  set Af := ↥(chartAlgFin p (ΓM M H) hj) with hAfdef

  have hXO : XHDRLevel.XO (ΓM M H) hj ρO = XO p (ΓM M H) hj O := rfl

  obtain ⟨v₀, hv₀, hdict⟩ :=
    ModularCurve.XHDRModelAtP.exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one p M H hpM hpM2 hHp hj 𝔛
  obtain ⟨σ, hσ, -⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  obtain ⟨v, w, hv, hw, hvw, -⟩ := ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH p M H hpM hpM2 hHp hj σ hσ

  have hinjF : ∀ a b : ↥(qExpFunctionFieldC ℚ (ΓM M H)), (a : LaurentSeries ℚ) = (b : LaurentSeries ℚ) → a = b := fun a b h => Subtype.ext h
  have hinjA : ∀ a b : Af, ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) → a = b :=
    fun a b h => Subtype.ext (hinjF _ _ h)

  have hv₀vw : v₀ = v ∨ v₀ = w := by
    rcases hv₀ with h | h
    · left; exact hinjA _ _ (h.trans hv.symm)
    · right; exact hinjA _ _ (h.trans hw.symm)
  obtain ⟨v₀', hvv'⟩ : ∃ v₀' : Af, v₀ * v₀' = ((p : ℕ) : Af) ^ 12 := by
    have hvw' : v * w = ((p : ℕ) : Af) ^ 12 := by rw [hvw, map_pow, map_natCast]
    rcases hv₀vw with rfl | rfl
    · exact ⟨w, hvw'⟩
    · exact ⟨v, by rw [mul_comm]; exact hvw'⟩

  obtain ⟨W₀, W₁, hW1, hW2, hW3, hW5, -⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_pair_gammaH p M H hpM hpM2 hHp hj
  haveI : (ΓM M H).FiniteIndex := CuspForm.GammaH_finiteIndex M H
  have hT : ModularGroup.T ∈ ΓM M H := ModularCurve.translation_mem_GammaH M H
  obtain ⟨-, hii, -⟩ := ModularCurve.XHDRLevel.KerMinH.kerMin_of_pair p M H hj
    (ModularCurve.XHDRLevel.KerMinH.finiteDimensional_adjoin_jAt (ΓM M H) hT hj)
    (ModularCurve.XHDRLevel.KerMinH.isSeparable_adjoin_jAt (ΓM M H) hT hj) W₀ W₁ hW1 hW2 hW3 hW5

  obtain ⟨i, ⟨huW, huinvW⟩, ⟨hu'W, hu'invW⟩, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_modularUnit_mem_and_inv_mem_and_div_mem_of_valuationSubring_pair_chartAlgFin
      p M H hpM hpM2 hHp hj 𝔛 (v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) hv W₀ W₁ hW1 hW2 hW3 hW5

  have hp0F : ((p : ℕ) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≠ 0 := by exact_mod_cast hpP.ne_zero
  have hvF0 : (v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≠ 0 := by
    intro h
    apply ModularCurve.modularUnitSeries_ne_zero p
    rw [← hv, show ((v : Af) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = 0 from h]
    rfl
  have hwF : ((w : Af) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = ((p : ℕ) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ^ 12 * ((v : Af) : ↥(qExpFunctionFieldC ℚ (ΓM M H)))⁻¹ := by
    have h1 : ((v : Af) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) * ((w : Af) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = ((p : ℕ) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ^ 12 := by
      have := congrArg (fun x : Af => (x : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) hvw
      simpa using this
    rw [eq_comm, ← h1, mul_comm ((v : Af) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) _, mul_assoc, mul_inv_cancel₀ hvF0, mul_one]

  have hnotnonunit : ∀ (W : ValuationSubring ↥(qExpFunctionFieldC ℚ (ΓM M H))) (x : ↥(qExpFunctionFieldC ℚ (ΓM M H))), x ≠ 0 → x ∈ W → x⁻¹ ∈ W → x ∉ W.nonunits := by
    intro W x hx0 hx hxi hnu
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp hnu
    have hle : W.valuation x⁻¹ ≤ 1 := (W.valuation_le_one_iff _).mpr hxi
    rw [map_inv₀, inv_le_one₀ (by rw [Valuation.pos_iff]; exact hx0)] at hle
    exact not_lt.mpr hle hlt
  have hwF0 : ((p : ℕ) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ^ 12 * ((v : Af) : ↥(qExpFunctionFieldC ℚ (ΓM M H)))⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp0F) (inv_ne_zero hvF0)

  obtain ⟨𝔭, h𝔭min, hv₀𝔭⟩ : ∃ 𝔭 ∈ (Ideal.span {((p : ℕ) : Af)}).minimalPrimes, v₀ ∉ 𝔭 := by
    rcases hv₀vw with rfl | rfl
    · obtain ⟨𝔭, h𝔭, hiff⟩ := hii i
      exact ⟨𝔭, h𝔭, fun h => hnotnonunit _ _ hvF0 huW huinvW ((hiff _).mp h)⟩
    · obtain ⟨𝔭, h𝔭, hiff⟩ := hii (1 - i)
      refine ⟨𝔭, h𝔭, fun h => hnotnonunit _ _ (by rw [hwF]; exact hwF0) ?_ ?_ ((hiff _).mp h)⟩
      · rw [hwF]; exact hu'W
      · rw [hwF]; exact hu'invW
  haveI h𝔭prime : 𝔭.IsPrime := h𝔭min.1.1
  have hp𝔭 : ((p : ℕ) : Af) ∈ 𝔭 := h𝔭min.1.2 (Ideal.subset_span (Set.mem_singleton _))

  haveI : IsLocalRing (R p) := inferInstance
  have hmaxR : IsLocalRing.maximalIdeal (R p) = Ideal.span {((p : ℕ) : R p)} :=
    GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hpP
  have hcomap_eq : ∀ (I : Ideal (R p)), I.IsPrime → ((p : ℕ) : R p) ∈ I → I = IsLocalRing.maximalIdeal (R p) := by
    intro I hI hpI
    refine le_antisymm (IsLocalRing.le_maximalIdeal hI.ne_top) ?_
    rw [hmaxR, Ideal.span_singleton_le_iff_mem]
    exact hpI
  set xP : ↥(X p (ΓM M H) hj) := (ιFin p (ΓM M H) hj).base ⟨𝔭, h𝔭prime⟩ with hxP
  have hbase : (toBase p (ΓM M H) hj).base xP = (Spec.map (CommRingCat.ofHom τ)).base (IsLocalRing.closedPoint κ) := by
    rw [hxP, ← comp_base_apply',
      AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)]
    apply PrimeSpectrum.ext
    show Ideal.comap _ 𝔭 = Ideal.comap _ _
    rw [hcomap_eq _ (Ideal.comap_isPrime _ 𝔭) (by simpa [Ideal.mem_comap] using hp𝔭)]
    symm
    refine hcomap_eq _ (Ideal.comap_isPrime _ _) ?_
    show τ ((p : ℕ) : R p) ∈ (IsLocalRing.closedPoint κ).asIdeal
    rw [map_natCast, CharP.cast_eq_zero]
    exact Ideal.zero_mem _
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := toBase p (ΓM M H) hj)
    (g := Spec.map (CommRingCat.ofHom τ)) xP (IsLocalRing.closedPoint κ) hbase
  obtain ⟨⟨z₀, hz₀⟩, -⟩ := hdict A hA ρ hρ y ⟨𝔭, h𝔭prime⟩ hy hv₀𝔭

  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  set bc := bcMap (ΓM M H) hj ρO toκ htoκ with hbc
  have hbc_fst : bc ≫ pullback.fst _ _ = pullback.fst _ _ := bcMap_fst (ΓM M H) hj ρO toκ htoκ
  set U : (XHDRLevel.XO (ΓM M H) hj ρO).Opens := (chartFin p (ΓM M H) hj O) ''ᵁ ⊤ with hU
  have hUrange : ∀ x : ↥(XHDRLevel.XO (ΓM M H) hj ρO), x ∈ U ↔
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).base x ∈ Set.range (ιFin p (ΓM M H) hj).base := by
    intro x
    have := range_chartFin p (ΓM M H) hj O
    constructor
    · rintro ⟨𝔔, -, rfl⟩
      have h1 : (chartFin p (ΓM M H) hj O).base 𝔔 ∈ Set.range (chartFin p (ΓM M H) hj O).base := ⟨𝔔, rfl⟩
      rw [this] at h1
      exact h1
    · intro hx
      have h1 : x ∈ Set.range (chartFin p (ΓM M H) hj O).base := by rw [this]; exact hx
      obtain ⟨𝔔, h𝔔⟩ := h1
      exact ⟨𝔔, trivial, h𝔔⟩
  have hxU : 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n ∈ U :=
    (hUrange _).mpr (ModularCurve.XHDRModelAtP.crossingPt_mem_preimage_iotaFin p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO toκ htoκ n)
  have hinfU : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ∈ U := hinf.mem_open U.isOpen hxU
  have hzeroU : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ∈ U := hzero.mem_open U.isOpen hxU

  have hchart : ∀ x : ↥(XHDRLevel.XO (ΓM M H) hj ρO), x ∈ U → ∃ 𝔔 : PrimeSpectrum (Af ⊗[R p] O),
      x = (chartFin p (ΓM M H) hj O).base 𝔔 ∧
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).base x =
        (ιFin p (ΓM M H) hj).base (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := Af) (B := O)) 𝔔) := by
    rintro x ⟨𝔔, -, rfl⟩
    exact ⟨𝔔, rfl, fst_chartFin p (ΓM M H) hj O 𝔔⟩

  refine ⟨(XHDRLevel.XO (ΓM M H) hj ρO).presheaf.germ U (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) hxU (sectionOf p (ΓM M H) hj O (v₀ ⊗ₜ[R p] (1 : O))),
    (XHDRLevel.XO (ΓM M H) hj ρO).presheaf.germ U (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) hxU (sectionOf p (ΓM M H) hj O (v₀' ⊗ₜ[R p] (1 : O))), ?_, ?_, ?_⟩
  ·
    set G := (XHDRLevel.XO (ΓM M H) hj ρO).presheaf.germ U (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) hxU with hG
    show G.hom _ * G.hom _ = _
    rw [← map_mul G.hom]
    have hsec : sectionOf p (ΓM M H) hj O (v₀ ⊗ₜ[R p] (1 : O)) * sectionOf p (ΓM M H) hj O (v₀' ⊗ₜ[R p] (1 : O)) =
        ((p : ℕ) : Γ(XHDRLevel.XO (ΓM M H) hj ρO, U)) ^ 12 := by
      have htm : (v₀ ⊗ₜ[R p] (1 : O)) * (v₀' ⊗ₜ[R p] (1 : O)) = (((p : ℕ) : Af ⊗[R p] O)) ^ 12 := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hvv']
        have hincl : ((((p : ℕ) : Af) ^ 12) ⊗ₜ[R p] (1 : O) : Af ⊗[R p] O) =
            (Algebra.TensorProduct.includeLeftRingHom : Af →+* Af ⊗[R p] O) (((p : ℕ) : Af) ^ 12) := rfl
        rw [hincl, map_pow, map_natCast]
      show ((chartFin p (ΓM M H) hj O).appIso ⊤).inv.hom ((Scheme.ΓSpecIso _).inv.hom _) *
          ((chartFin p (ΓM M H) hj O).appIso ⊤).inv.hom ((Scheme.ΓSpecIso _).inv.hom _) = _
      rw [← map_mul, ← map_mul, htm, map_pow, map_pow, map_natCast, map_natCast]
    rw [hsec, map_pow, map_natCast]
    simp only [XHDRLevel.baseGerm, map_natCast]
  ·
    obtain ⟨𝔔₁, h𝔔₁, hfst₁⟩ := hchart _ hzeroU
    have hvQ : v₀ ⊗ₜ[R p] (1 : O) ∈ 𝔔₁.asIdeal := by
      set y₁ : ↥(fibre (Γ := ΓM M H) (hj := hj) τ) :=
        (𝔛.comp A hA ρ hρ 1).base ((𝔛.efib A hA ρ hρ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C)) with hy₁
      have hξ : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ = bc.base y₁ := rfl
      have hfst_y : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom τ))).base y₁ =
          (ιFin p (ΓM M H) hj).base (PrimeSpectrum.comap
            (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := Af) (B := O)) 𝔔₁) := by
        rw [← hfst₁, hξ, ← comp_base_apply' bc, hbc_fst]
      by_contra hv1
      have hv1' : v₀ ∉ (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := Af) (B := O)) 𝔔₁).asIdeal :=
        fun hmem => hv1 (by
          have h := Ideal.mem_comap.mp hmem
          rwa [Algebra.TensorProduct.includeLeftRingHom_apply] at h)
      have := (hdict A hA ρ hρ y₁ (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := Af) (B := O)) 𝔔₁) hfst_y hv1').2
      exact this ⟨_, hy₁.symm⟩
    have hzero_mem := (germ_sectionOf_mem_maximalIdeal_iff p (ΓM M H) hj O 𝔔₁ h𝔔₁ hzeroU _).mpr hvQ
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h2 := hunit.map ((XHDRLevel.XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hzero).hom
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply] at h2
    exact (IsLocalRing.mem_maximalIdeal _).mp hzero_mem h2
  ·
    left
    set x := bc.base y with hw
    have hwU : x ∈ U := by
      rw [hUrange, hw, ← comp_base_apply' bc, hbc_fst, hy]
      exact ⟨_, rfl⟩
    obtain ⟨𝔔, h𝔔, hfst⟩ := hchart x hwU
    have hPQ : PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := Af) (B := O)) 𝔔 = ⟨𝔭, h𝔭prime⟩ := by
      apply (ιFin p (ΓM M H) hj).isOpenEmbedding.injective
      rw [← hfst, hw, ← comp_base_apply' bc, hbc_fst, hy]
    have hvQ : v₀ ⊗ₜ[R p] (1 : O) ∉ 𝔔.asIdeal := by
      intro hmem
      apply hv₀𝔭
      have : v₀ ∈ (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := Af) (B := O)) 𝔔).asIdeal := by
        apply Ideal.mem_comap.mpr
        rw [Algebra.TensorProduct.includeLeftRingHom_apply]
        exact hmem
      rw [hPQ] at this
      exact this
    have hunit_w : IsUnit ((XHDRLevel.XO (ΓM M H) hj ρO).presheaf.germ U x hwU (sectionOf p (ΓM M H) hj O (v₀ ⊗ₜ[R p] (1 : O)))) :=
      (isUnit_germ_sectionOf_iff p (ΓM M H) hj O 𝔔 h𝔔 hwU _).mpr hvQ
    have hgen : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ x := by
      have h1 : (𝔛.efib A hA ρ hρ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) ⤳ z₀ := 𝔛.efib_genericPoint_specializes A hA ρ hρ z₀
      have h2 := (h1.map (𝔛.comp A hA ρ hρ 0).base.hom.continuous).map bc.base.hom.continuous
      rw [hz₀] at h2
      exact h2
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    have h3 := hunit_w.map ((XHDRLevel.XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hgen).hom
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply] at h3
    exact h3

end OggTH
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTH.RingStalk P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTH"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTH.RingStalk P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTH"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve _root_.ModularCurve.XHDRLevel _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.ModularCurve.XHDRLevel in
open scoped MatrixGroups in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hinf : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)
    (hzero : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) :
    ∃ t t' : (XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n),
      t * t' = baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ((p : ℕ) : O) ^ 12 ∧
      t ∈ IsLocalRing.maximalIdeal ((XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)) ∧
      (IsUnit (((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hinf).hom t) ∨
        IsUnit (((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hzero).hom t)) :=
  OggTH.main p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ n hinf hzero

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing (solution)
