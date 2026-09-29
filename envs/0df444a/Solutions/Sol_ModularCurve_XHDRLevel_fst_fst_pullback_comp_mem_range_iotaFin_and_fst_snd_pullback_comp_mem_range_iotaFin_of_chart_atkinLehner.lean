-- Prove2me | solution 1 for ModularCurve.XHDRLevel.fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d5989abf-f54f-59e3-a46c-521c05f2a5c4

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_ModularCurve_XHDRLevel_exists_minimalPrimes_chartAlgInf_map_le_of_mem_range_comp_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_chart_comp_fibreMap_eq_specMap_tensor_comp_chart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRLevel_fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner.ModularCurve.XHDRLevel NeronModelInfra"
open scoped MatrixGroups TensorProduct

noncomputable section

namespace CrossFinH

universe u

section Generic

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
  (κ : Type u) [CommRing κ] [Algebra R κ]

open AlgebraicCurve.TwoChartIntegralModel

abbrev Xκ : Scheme.{u} :=
  pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))

theorem isPullback_chartFin
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶ Xκ R F j κ)
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫
        ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgFin R F j))))) :
    IsPullback c (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) (pullback.fst _ _) (ιFin R F j) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ ↥(chartAlgFin R F j))
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιFin R F j ≫ toBase R F j) := by
    rw [hcsnd, ιFin_toBase]
    exact sq
  exact IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip

theorem isPullback_chartInf
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgInf R F j))) ⟶ Xκ R F j κ)
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom) ≫
        ιInf R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgInf R F j))))) :
    IsPullback c (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) (pullback.fst _ _) (ιInf R F j) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ ↥(chartAlgInf R F j))
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιInf R F j ≫ toBase R F j) := by
    rw [hcsnd, ιInf_toBase]
    exact sq
  exact IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip

theorem range_eq_preimage_of_isPullback {S T X Y : Scheme.{u}} {c : S ⟶ X} {g : S ⟶ T} {f : X ⟶ Y} {ι : T ⟶ Y}
    (H : IsPullback c g f ι) : Set.range c.base = f.base ⁻¹' Set.range ι.base := by
  have hc : c = H.isoPullback.hom ≫ pullback.fst _ _ := (H.isoPullback_hom_fst).symm
  rw [← Scheme.Pullback.range_fst, hc]
  ext x; constructor
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.hom.base y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩

theorem ιFin_eq_ιInf_iff (x₀ : ↥(XFin R F j)) (xi : ↥(XInf R F j)) :
    (ιFin R F j).base x₀ = (ιInf R F j).base xi ↔ ∃ m : ↥(XMid R F j), (fFin R F j).base m = x₀ ∧ (fInf R F j).base m = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, m, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨m, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨m, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base m = (fInf R F j ≫ ιInf R F j).base m
    rw [glue_condition]

theorem range_fInf :
    Set.range (fInf R F j).base =
      ((PrimeSpectrum.basicOpen (jInvChartInf R F j) : TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgInf R F j))) :
        Set (PrimeSpectrum ↥(chartAlgInf R F j))) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid R F j) (jInvChartInf R F j)

theorem ιInf_mem_range_ιFin_iff (xi : ↥(XInf R F j)) :
    (ιInf R F j).base xi ∈ Set.range (ιFin R F j).base ↔ jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨m, -, hm⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp h
    exact ⟨m, hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(fFin R F j).base m, (ιFin_eq_ιInf_iff R F j _ _).mpr ⟨m, rfl, rfl⟩⟩

end Generic

end CrossFinH

namespace ModularCurve p2m_export "ModularCurve" "qExpFunctionFieldC qExpand jqModC XHDRLevel.exists_minimalPrimes_chartAlgInf_map_le_of_mem_range_comp_gammaH XHDRLevel.sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_gammaH XHDRLevel.chart_comp_fibreMap_eq_specMap_tensor_comp_chart" namespace XHDRLevel p2m_export "ModularCurve.XHDRLevel" "R jAt X toBase chartAlgFin chartAlgInf ιFin ιInf fibre fibreMap overOfIso ΓN ΓM exists_minimalPrimes_chartAlgInf_map_le_of_mem_range_comp_gammaH sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_gammaH chart_comp_fibreMap_eq_specMap_tensor_comp_chart" end ModularCurve.XHDRLevel
p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in
open CrossFinH in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem ModularCurve.XHDRLevel.fst_pullback_comp_mem_range_iotaFin_and_snd_pullback_comp_mem_range_iotaFin
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)

    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hw : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_pi : comp 0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _)
    (comp_w : comp 0 ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) = comp 1) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra

    ∀ (c₀ : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶
          fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : c₀ ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
      (_ : c₀ ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))))
      (c : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶
          fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : c ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj)
      (_ : c ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))))
      (_ : c ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom) ≫ c),
    (∀ n : ↥(pullback (comp 0) (comp 1)),
      (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((pullback.fst (comp 0) (comp 1)).base n) ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base) ∧
    (∀ n : ↥(pullback (comp 0) (comp 1)),
      (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((pullback.snd (comp 0) (comp 1)).base n) ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base) := by
  letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  intro c₀ hc₀fst hc₀snd c hcfst hcsnd hcw

  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := (IsLocalRing.ResidueField ↥A))
        (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj) ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓM M H) hj)))) ≫
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (((IsLocalRing.residue ↥A).comp ρ) r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    rfl
  let c' : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) := pullback.lift _ _ hcompat
  have hc'fst : c' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p)
      (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj := pullback.lift_fst _ _ _
  have hc'snd : c' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p)
      (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓM M H) hj)))) := pullback.lift_snd _ _ _
  have hc'range := range_eq_preimage_of_isPullback (isPullback_chartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) (IsLocalRing.ResidueField ↥A) c' hc'fst hc'snd)
  have hcrange := range_eq_preimage_of_isPullback (isPullback_chartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) (IsLocalRing.ResidueField ↥A) c hcfst hcsnd)

  obtain ⟨P, hPmin, hPne, hPle⟩ :=
    ModularCurve.XHDRLevel.exists_minimalPrimes_chartAlgInf_map_le_of_mem_range_comp_gammaH p M H hpM hpM2 hHp hj
      π iota0 iota0_spec pi_chart w hw theta htheta A hA ρ hρ comp comp_over comp_isClosedImmersion comp_pi comp_w
      c₀ hc₀fst hc₀snd c hcfst hcsnd hcw c' hc'fst hc'snd

  have key : ∀ n : ↥(pullback (comp 0) (comp 1)),
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((comp 0).base ((pullback.fst (comp 0) (comp 1)).base n)) ∈ Set.range (ιFin p (ΓM M H) hj).base := by
    intro n
    by_contra hxfin
    obtain ⟨xi, hxi⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) _).resolve_left
      hxfin
    have hj' : AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ∈ xi.asIdeal := by
      by_contra h
      exact hxfin (hxi ▸ (ιInf_mem_range_ιFin_iff (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) xi).mpr h)

    have hyc : (comp 0).base ((pullback.fst (comp 0) (comp 1)).base n) ∈ Set.range c'.base := by
      rw [hc'range]; exact ⟨xi, hxi⟩
    obtain ⟨z, hz⟩ := hyc
    have hz0 : c'.base z ∈ Set.range (comp 0).base := ⟨_, hz.symm⟩
    have hz1 : c'.base z ∈ Set.range (comp 1).base := by
      refine ⟨(pullback.snd (comp 0) (comp 1)).base n, ?_⟩
      rw [hz]
      change (pullback.snd (comp 0) (comp 1) ≫ comp 1).base n = (pullback.fst (comp 0) (comp 1) ≫ comp 0).base n
      rw [pullback.condition]
    have h0 := hPle 0 z hz0
    have h1 := hPle 1 z hz1

    have hzx : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := (IsLocalRing.ResidueField ↥A))
        (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom)).base z = xi := by
      apply (ιInf p (ΓM M H) hj).isOpenEmbedding.injective
      change (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := (IsLocalRing.ResidueField ↥A))
        (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj).base z = _
      rw [← hc'fst, hxi]
      change (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base (c'.base z) = _
      rw [hz]
    have hjz : (Algebra.TensorProduct.includeRight (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓM M H) hj)))
        (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) ∈ z.asIdeal := by
      rw [← hzx] at hj'
      exact hj'

    let 𝔯 : Ideal ↥(chartAlgInf p (ΓM M H) hj) := Ideal.comap (Algebra.TensorProduct.includeRight :
        ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj)) z.asIdeal
    haveI h𝔯 : 𝔯.IsPrime := Ideal.IsPrime.comap _
    have hP0 : P 0 ≤ 𝔯 := Ideal.map_le_iff_le_comap.mp h0
    have hP1 : P 1 ≤ 𝔯 := Ideal.map_le_iff_le_comap.mp h1
    have hjr : AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ∈ 𝔯 := Ideal.mem_comap.mpr hjz
    have hle : P 0 ⊔ P 1 ⊔ Ideal.span {AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)} ≤ 𝔯 :=
      sup_le (sup_le hP0 hP1) ((Ideal.span_singleton_le_iff_mem _).mpr hjr)
    rw [ModularCurve.XHDRLevel.sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_gammaH p M H hpM hpM2 hHp hj
      (P 0) (P 1) (hPmin 0) (hPmin 1) hPne, top_le_iff] at hle
    exact h𝔯.ne_top hle

  have hread : ∀ y : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y =
        π.1.base ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base ((comp 0).base y)) := by
    intro y
    have e : pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) =
        comp 0 ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ≫ π.1 := by
      conv_lhs => rw [← Category.id_comp (pullback.fst _ _), ← comp_pi]
      simp only [Category.assoc, fibreMap, pullback.lift_fst]
    exact congrArg (fun f => f.base y) e |>.trans rfl

  have hπfin : ∀ x : ↥(X p (ΓM M H) hj), x ∈ Set.range (ιFin p (ΓM M H) hj).base →
      π.1.base x ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base := by
    rintro x ⟨x₀, rfl⟩
    change (ιFin p (ΓM M H) hj ≫ π.1).base x₀ ∈ _
    rw [pi_chart]
    exact ⟨(Spec.map (CommRingCat.ofHom iota0.toRingHom)).base x₀, rfl⟩
  refine ⟨fun n => ?_, fun n => ?_⟩
  ·
    rw [hread]
    exact hπfin _ (key n)
  ·
    rw [hread]
    apply hπfin

    have hx : (comp 1).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ Set.range c.base := by
      rw [hcrange, Set.mem_preimage]
      change (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((pullback.snd (comp 0) (comp 1) ≫ comp 1).base n) ∈ _
      rw [← pullback.condition]
      exact key n

    set y' := (comp 0).base ((pullback.snd (comp 0) (comp 1)).base n) with hy'
    have hwy : (fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ)).base y' = (comp 1).base ((pullback.snd (comp 0) (comp 1)).base n) := by
      rw [hy', ← Scheme.Hom.comp_apply, comp_w]

    have hwc : Set.range (c ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ)).base = Set.range c.base := by
      rw [hcw]
      haveI : IsIso (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A))
          theta.toAlgHom).toRingHom)) := by
        have e : CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A)
            (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom =
            ((Algebra.TensorProduct.congr (AlgEquiv.refl : IsLocalRing.ResidueField ↥A ≃ₐ[IsLocalRing.ResidueField ↥A]
              IsLocalRing.ResidueField ↥A) theta).toRingEquiv.toCommRingCatIso).hom := rfl
        rw [e]; infer_instance
      have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom)).base :=
        (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom))))).surjective
      ext x
      constructor
      · rintro ⟨s, rfl⟩; exact ⟨_, (Scheme.Hom.comp_apply _ _ s).symm⟩
      · rintro ⟨s, rfl⟩
        obtain ⟨t, ht⟩ := hsurj s
        exact ⟨t, by rw [Scheme.Hom.comp_apply, ht]⟩
    haveI : IsIso (fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ)) := by
      unfold fibreMap overOfIso
      infer_instance
    have hinj : Function.Injective (fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ)).base :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ))))).injective
    have : y' ∈ Set.range c.base := by
      have hx' : (fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ)).base y' ∈ Set.range (c ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ)).base := by
        rw [hwc, hwy]; exact hx
      obtain ⟨s, hs⟩ := hx'
      exact ⟨s, hinj (by simpa [Scheme.Hom.comp_apply] using hs)⟩
    rw [hcrange] at this
    exact this

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)

    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hw : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_pi : comp 0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _)
    (comp_w : comp 0 ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) = comp 1) :
    (∀ n : ↥(pullback (comp 0) (comp 1)),
      (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
          ((pullback.fst (comp 0) (comp 1)).base n) ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base) ∧
    (∀ n : ↥(pullback (comp 0) (comp 1)),
      (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
          ((pullback.snd (comp 0) (comp 1)).base n) ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base) := by
  letI := (((IsLocalRing.residue ↥A).comp ρ)).toAlgebra

  have hcompat_c₀ : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := (IsLocalRing.ResidueField ↥A))
        (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj) ≫ toBase p (ΓN p M H hpM) hj =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))) ≫
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (((IsLocalRing.residue ↥A).comp ρ) r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    rfl
  let c₀ : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶ fibre (Γ := (ΓN p M H hpM)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) := pullback.lift _ _ hcompat_c₀
  have hc₀fst : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p)
      (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj := pullback.lift_fst _ _ _
  have hc₀snd : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p)
      (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))) := pullback.lift_snd _ _ _

  have hcompat_c : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := (IsLocalRing.ResidueField ↥A))
        (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj) ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgFin p (ΓM M H) hj)))) ≫
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (((IsLocalRing.residue ↥A).comp ρ) r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    rfl
  let c : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ fibre (Γ := (ΓM M H)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) := pullback.lift _ _ hcompat_c
  have hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p)
      (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p)
      (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgFin p (ΓM M H) hj)))) := pullback.lift_snd _ _ _

  have hwchart' : ιFin p (ΓM M H) hj ≫ (overOfIso w hw).1 = Spec.map (CommRingCat.ofHom theta.toAlgHom.toRingHom) ≫ ιFin p (ΓM M H) hj :=
    hwchart
  have hcw : c ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom) ≫ c :=
    ModularCurve.XHDRLevel.chart_comp_fibreMap_eq_specMap_tensor_comp_chart p hj (overOfIso w hw) theta.toAlgHom hwchart'
      (IsLocalRing.ResidueField ↥A) c hcfst hcsnd c hcfst hcsnd
  exact ModularCurve.XHDRLevel.fst_pullback_comp_mem_range_iotaFin_and_snd_pullback_comp_mem_range_iotaFin p M H hpM hpM2 hHp hj
    π iota0 iota0_spec pi_chart w hw theta htheta A hA ρ hρ comp comp_over comp_isClosedImmersion comp_pi comp_w
    c₀ hc₀fst hc₀snd c hcfst hcsnd hcw

end

end S_ModularCurve_XHDRLevel_fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner (solution)
