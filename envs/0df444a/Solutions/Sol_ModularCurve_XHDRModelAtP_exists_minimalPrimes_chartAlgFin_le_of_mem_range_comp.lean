-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/69cf4803-a27a-552d-bbe5-6c224c500787

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_exists_retraction_chart_comp_zero_eq
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
import Theorems.Thm_ModularCurve_isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XHDRLevel_comap_atkinLehner_valuationSubring_gauss_gammaH
import Theorems.Thm_ModularCurve_qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_ModularCurve_X0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply"
p2m_attr_erase "simp" "ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace InfOffC1Geo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

universe u
variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
variable (κ : Type u) [CommRing κ] [Algebra R κ]

abbrev fib : Scheme.{u} := pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))

theorem chart_comm_fin :
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j) ≫
        toBase R F j =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgFin R F j)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
  rw [Category.assoc, ιFin_toBase, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem chart_comm_inf :
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom) ≫ ιInf R F j) ≫
        toBase R F j =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgInf R F j)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
  rw [Category.assoc, ιInf_toBase, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

def cFin : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶ fib R F j κ := pullback.lift _ _ (chart_comm_fin R F j κ)

def cInf : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgInf R F j))) ⟶ fib R F j κ := pullback.lift _ _ (chart_comm_inf R F j κ)

@[scoped simp] theorem cFin_fst : cFin R F j κ ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem cFin_snd : cFin R F j κ ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgFin R F j)))) :=
  pullback.lift_snd _ _ _
@[scoped simp] theorem cInf_fst : cInf R F j κ ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom) ≫ ιInf R F j :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem cInf_snd : cInf R F j κ ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgInf R F j)))) :=
  pullback.lift_snd _ _ _

theorem isPullback_cFin :
    IsPullback (cFin R F j κ) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom))
      (pullback.fst _ _) (ιFin R F j) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap R κ)))
    (h₂₂ := toBase R F j) ?_ (cFin_fst R F j κ) (IsPullback.of_hasPullback _ _).flip
  rw [cFin_snd, ιFin_toBase]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ ↥(chartAlgFin R F j))

theorem isPullback_cInf :
    IsPullback (cInf R F j κ) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom))
      (pullback.fst _ _) (ιInf R F j) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap R κ)))
    (h₂₂ := toBase R F j) ?_ (cInf_fst R F j κ) (IsPullback.of_hasPullback _ _).flip
  rw [cInf_snd, ιInf_toBase]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ ↥(chartAlgInf R F j))

scoped instance isOpenImmersion_cFin : IsOpenImmersion (cFin R F j κ) := by
  rw [← (isPullback_cFin R F j κ).isoPullback_hom_fst]; infer_instance

scoped instance isOpenImmersion_cInf : IsOpenImmersion (cInf R F j κ) := by
  rw [← (isPullback_cInf R F j κ).isoPullback_hom_fst]; infer_instance

theorem mem_range_cFin_iff (x : ↥(fib R F j κ)) :
    x ∈ Set.range (cFin R F j κ) ↔ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) x ∈ Set.range (ιFin R F j) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, cFin_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · intro hx
    have H := isPullback_cFin R F j κ
    have hx' : x ∈ Set.range (pullback.fst (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) (ιFin R F j)) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨t, rfl⟩ := hx'
    exact ⟨H.isoPullback.inv t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

theorem mem_range_cInf_iff (x : ↥(fib R F j κ)) :
    x ∈ Set.range (cInf R F j κ) ↔ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) x ∈ Set.range (ιInf R F j) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, cInf_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · intro hx
    have H := isPullback_cInf R F j κ
    have hx' : x ∈ Set.range (pullback.fst (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) (ιInf R F j)) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨t, rfl⟩ := hx'
    exact ⟨H.isoPullback.inv t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

theorem mem_range_cFin_or (x : ↥(fib R F j κ)) : x ∈ Set.range (cFin R F j κ) ∨ x ∈ Set.range (cInf R F j κ) := by
  rw [mem_range_cFin_iff, mem_range_cInf_iff]
  exact mem_range_ιFin_or_mem_range_ιInf R F j _

theorem specMap_inclFin_cFin :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclFin R F j)).toRingHom) ≫ cFin R F j κ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclInf R F j)).toRingHom) ≫ cInf R F j κ := by
  have e1 : (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclFin R F j)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgMid R F j))).toRingHom.comp (inclFin R F j).toRingHom :=
    RingHom.ext fun b => by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e2 : (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclInf R F j)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgMid R F j))).toRingHom.comp (inclInf R F j).toRingHom :=
    RingHom.ext fun b => by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e3 : (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclFin R F j)).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgFin R F j))) = Algebra.TensorProduct.includeLeftRingHom :=
    RingHom.ext fun a => by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  have e4 : (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclInf R F j)).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgInf R F j))) = Algebra.TensorProduct.includeLeftRingHom :=
    RingHom.ext fun a => by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, cFin_fst, cInf_fst, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1, e2, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
      Spec.map_comp_assoc, Spec.map_comp_assoc]
    show _ ≫ fFin R F j ≫ ιFin R F j = _ ≫ fInf R F j ≫ ιInf R F j
    rw [glue_condition]
  · rw [Category.assoc, Category.assoc, cFin_snd, cInf_snd, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, e3, e4]

theorem specializes_of_cFin {x y : PrimeSpectrum (κ ⊗[R] ↥(chartAlgFin R F j))} (h : cFin R F j κ x ⤳ cFin R F j κ y) : x ≤ y :=
  (PrimeSpectrum.le_iff_specializes x y).mpr ((cFin R F j κ).isOpenEmbedding.isInducing.specializes_iff.mp h)

theorem specializes_of_cInf {x y : PrimeSpectrum (κ ⊗[R] ↥(chartAlgInf R F j))} (h : cInf R F j κ x ⤳ cInf R F j κ y) : x ≤ y :=
  (PrimeSpectrum.le_iff_specializes x y).mpr ((cInf R F j κ).isOpenEmbedding.isInducing.specializes_iff.mp h)

end InfOffC1Geo
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped TensorProduct MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve AlgebraicCurve"

namespace InfOffC1Tensor

variable {p : ℕ} [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

theorem ringHom_ext_zp {P : Type*} [Semiring P] (f g : ℤp →+* P) : f = g := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  haveI : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

def tensorAddHom {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) : A ⊗[ℤp] M →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun b => F x * G b) (fun b b' => by simp only [map_add, mul_add]))
      (fun x x' => by ext b; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]))
    (fun r x b => by
      have key := RingHom.congr_fun (ringHom_ext_zp (p := p) (F.comp (algebraMap ℤp A)) (G.comp (algebraMap ℤp M))) r
      simp only [RingHom.coe_comp, Function.comp_apply] at key
      show F (r • x) * G b = F x * G (r • b)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, key]
      ring)

theorem tensorAddHom_tmul {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) (x : A) (b : M) :
    tensorAddHom (p := p) F G (x ⊗ₜ[ℤp] b) = F x * G b := by
  unfold tensorAddHom
  rw [TensorProduct.liftAddHom_tmul]
  rfl

def tensorRingHom {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) : A ⊗[ℤp] M →+* L :=
  { tensorAddHom (p := p) F G with
    map_one' := by
      show tensorAddHom (p := p) F G 1 = 1
      rw [Algebra.TensorProduct.one_def, tensorAddHom_tmul, map_one, map_one, one_mul]
    map_mul' := fun s t => by
      show tensorAddHom (p := p) F G (s * t) = tensorAddHom (p := p) F G s * tensorAddHom (p := p) F G t
      induction s using TensorProduct.induction_on with
      | zero => rw [zero_mul, map_zero, zero_mul]
      | tmul x b =>
        induction t using TensorProduct.induction_on with
        | zero => rw [mul_zero, map_zero, mul_zero]
        | tmul x' b' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, tensorAddHom_tmul, tensorAddHom_tmul, tensorAddHom_tmul, map_mul,
            map_mul]
          ring
        | add t₁ t₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
      | add s₁ s₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂] }

theorem tensorRingHom_tmul {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) (x : A) (b : M) :
    tensorRingHom (p := p) F G (x ⊗ₜ[ℤp] b) = F x * G b :=
  tensorAddHom_tmul (p := p) F G x b

theorem one_tmul_natCast_mul (κ : Type*) [CommRing κ] [CharP κ p] [Algebra ℤp κ] {M : Type*} [CommRing M] [Algebra ℤp M] (c : M) :
    (1 : κ) ⊗ₜ[ℤp] (((p : ℕ) : M) * c) = 0 := by
  rw [show ((p : ℕ) : M) * c = ((p : ℕ) : ℤp) • c by rw [Algebra.smul_def, map_natCast],
    ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_natCast, CharP.cast_eq_zero, TensorProduct.zero_tmul]

end InfOffC1Tensor
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo"

namespace InfOffC1Alg

variable {p : ℕ} [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

theorem false_of_one_tmul_eq_pow
    (κ : Type*) [CommRing κ] [Algebra ℤp κ] {B : Type*} [CommRing B] [Algebra ℤp B] (jB : B)
    (K : Type) [Field K] (cst : κ →+* K) (g₀ : B →+* LaurentSeries K) (hg₀ : g₀ jB = jqModC K)
    (s : κ ⊗[ℤp] B) (hs : (1 : κ) ⊗ₜ[ℤp] jB = s ^ p) : False := by
  let χ : κ ⊗[ℤp] B →+* LaurentSeries K :=
    InfOffC1Tensor.tensorRingHom (p := p) ((algebraMap K (LaurentSeries K)).comp cst) g₀
  have hχj : χ ((1 : κ) ⊗ₜ[ℤp] jB) = jqModC K := by
    show InfOffC1Tensor.tensorRingHom (p := p) _ _ _ = _
    rw [InfOffC1Tensor.tensorRingHom_tmul, map_one, one_mul]
    exact hg₀
  have hpow : (χ s) ^ p = jqModC K := by rw [← map_pow, ← hs, hχj]
  set x := χ s with hx
  have hx0 : x ≠ 0 := by
    intro h0'
    rw [h0', zero_pow (Fact.out : p.Prime).ne_zero] at hpow
    have := congrArg HahnSeries.order hpow
    rw [HahnSeries.order_zero, order_jqModC_def] at this
    norm_num at this
  have hord : ∀ n : ℕ, (x ^ n).order = n * x.order := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero n hx0) hx0, ih]; push_cast; ring
  have h := congrArg HahnSeries.order hpow
  rw [hord, order_jqModC_def] at h
  have hdvd : (p : ℤ) ∣ 1 := ⟨-x.order, by linarith⟩
  have hp1 : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdvd
  exact (Fact.out : p.Prime).one_lt.ne' hp1

theorem map_ker_mul_map_ker_le
    (κ : Type*) [CommRing κ] [CharP κ p] [Algebra ℤp κ] {O : Type*} [CommRing O] [Algebra ℤp O]
    {L : Type*} [CommRing L] (θ : Fin 2 → (O →+* L))
    (hmin : (Ideal.span {((p : ℕ) : O)}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (P : Ideal (κ ⊗[ℤp] O)) [hP : P.IsPrime] :
    Ideal.map (Algebra.TensorProduct.includeRight : O →ₐ[ℤp] κ ⊗[ℤp] O) (RingHom.ker (θ 0)) *
      Ideal.map (Algebra.TensorProduct.includeRight : O →ₐ[ℤp] κ ⊗[ℤp] O) (RingHom.ker (θ 1)) ≤ P := by
  have hrad : (Ideal.span {((p : ℕ) : O)}).radical ≤ P.comap (Algebra.TensorProduct.includeRight : O →ₐ[ℤp] κ ⊗[ℤp] O) := by
    intro z hz
    obtain ⟨n, hn⟩ := hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
    have hc' : z ^ n = ((p : ℕ) : O) * c := by rw [← hc]; exact mul_comm c _
    rw [Ideal.mem_comap]
    refine hP.mem_of_pow_mem n ?_
    rw [← map_pow, hc', Algebra.TensorProduct.includeRight_apply, InfOffC1Tensor.one_tmul_natCast_mul κ]
    exact Ideal.zero_mem _
  rw [← Ideal.map_mul]
  refine (Ideal.map_mono ?_).trans (Ideal.map_le_iff_le_comap.mpr hrad)
  rw [← Ideal.sInf_minimalPrimes, hmin, sInf_pair]
  exact Ideal.mul_le_inf

theorem one_tmul_eq_pow_of_case_one
    (κ : Type*) [CommRing κ] [Algebra ℤp κ] {B O : Type*} [CommRing B] [Algebra ℤp B] [CommRing O] [Algebra ℤp O]
    (ι : B →ₐ[ℤp] O) (jB : B) (jO : O) (hιj : ι jB = jO)
    (w : O ≃ₐ[ℤp] O)
    {L : Type*} [CommRing L] (θ : Fin 2 → (O →+* L))
    (hθ1 : ∀ c, θ 1 c = θ 0 (w c))
    (hfrob : ∀ b : B, θ 0 (w (ι b)) = θ 0 (ι b) ^ p)
    (σ0 : κ ⊗[ℤp] O →ₐ[κ] κ ⊗[ℤp] B)
    (h0 : ∀ z, σ0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (hI1 : Ideal.map (Algebra.TensorProduct.includeRight : O →ₐ[ℤp] κ ⊗[ℤp] O) (RingHom.ker (θ 1)) ≤ RingHom.ker σ0.toRingHom) :
    (1 : κ) ⊗ₜ[ℤp] jB = (σ0 ((1 : κ) ⊗ₜ[ℤp] w.symm jO)) ^ p := by
  have hv : (1 : κ) ⊗ₜ[ℤp] (jO - (w.symm jO) ^ p) ∈ RingHom.ker σ0.toRingHom := by
    refine hI1 (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, hθ1, map_sub, map_pow, AlgEquiv.apply_symm_apply, ← hιj, map_sub, map_pow, hfrob, sub_self]
  have h : σ0 ((1 : κ) ⊗ₜ[ℤp] (jO - (w.symm jO) ^ p)) = 0 := RingHom.mem_ker.mp hv
  rw [TensorProduct.tmul_sub, map_sub, sub_eq_zero] at h
  have hl : σ0 ((1 : κ) ⊗ₜ[ℤp] jO) = (1 : κ) ⊗ₜ[ℤp] jB := by
    rw [← hιj, ← h0 ((1 : κ) ⊗ₜ[ℤp] jB), Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [← hl, h, ← map_pow σ0, Algebra.TensorProduct.tmul_pow, one_pow]

end InfOffC1Alg
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo"

namespace InfOffC1AlgH

p2m_open "ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel"

variable {p : ℕ} [Fact p.Prime]

private theorem _root_.InfOffC1AlgH.coeffMap_jqModC {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') :
    coeffMap f (jqModC K) = jqModC K' := by
  ext k
  rw [coeffMap_coeff, ← map_jqModC f, HahnSeries.map_coeff]

p2m_export "InfOffC1AlgH" "coeffMap_jqModC"
variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem iota0_jChartFin
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) :
    iota0 (jChartFin p (ΓN p M H hpM) hj) = jChartFin p (ΓM M H) hj := by
  have h1 : (((iota0 (jChartFin p (ΓN p M H hpM) hj) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) :
      LaurentSeries ℚ) = jqModC ℚ := by
    rw [iota0_spec, show ((jChartFin p (ΓN p M H hpM) hj : ↥(chartAlgFin p (ΓN p M H hpM) hj)) : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) =
      jAt (ΓN p M H hpM) hj from AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin _ _ _, coe_jAt]
  have h2 : (((jChartFin p (ΓM M H) hj : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) :
      LaurentSeries ℚ) = jqModC ℚ := by
    rw [show ((jChartFin p (ΓM M H) hj : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) =
      jAt (ΓM M H) hj from AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin _ _ _, coe_jAt]
  exact Subtype.ext (Subtype.ext (h1.trans h2.symm))

theorem case_one_false
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (κ : Type) [Field κ] [Algebra (R p) κ] (res : ↥A →+* κ)
    (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries κ))
    (hθ1 : ∀ c, θ 1 c = θ 0 (theta c))
    (hθ2 : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        θ 0 c = coeffMap res y)
    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = θ 0 (iota0 b) ^ p)
    (σ0 : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ0 (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z)
    (hI1 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))
        (RingHom.ker (θ 1)) ≤ RingHom.ker σ0.toRingHom) : False := by
  have hιj := iota0_jChartFin (p := p) M H hpM hj iota0 iota0_spec
  have hs := InfOffC1Alg.one_tmul_eq_pow_of_case_one (p := p) κ iota0 _ _ hιj theta θ hθ1 hfrob σ0 h0 hI1
  refine InfOffC1Alg.false_of_one_tmul_eq_pow (p := p) κ (jChartFin p (ΓN p M H hpM) hj) κ (RingHom.id κ)
    ((θ 0).comp iota0.toRingHom) ?_ _ hs
  show θ 0 (iota0 (jChartFin p (ΓN p M H hpM) hj)) = jqModC κ
  rw [hιj, hθ2 (jChartFin p (ΓM M H) hj) (jqModC ↥A)]
  · exact coeffMap_jqModC res
  · rw [coeffMap_jqModC]
    show jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ)
    exact (coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm

end InfOffC1AlgH
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace InfOffC1Main

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel"
open scoped TensorProduct MatrixGroups

theorem eq_closedPoint_of_field (κ : Type) [Field κ] (z : ↥(Spec (CommRingCat.of κ))) : z = IsLocalRing.closedPoint κ := by
  apply PrimeSpectrum.ext
  rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum κ).asIdeal]
  exact (Ideal.eq_bot_of_prime _).symm

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem sectionFibre_eq
    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    (rhoInf : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] R p)
    (εinf_chart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ ιInf p (ΓM M H) hj)
    (κ : Type) [Field κ] [Algebra (R p) κ] :
    sectionFibre εinf (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (Algebra.ofId κ κ)
          ((Algebra.ofId (R p) κ).comp rhoInf) (fun _ _ => Commute.all _ _)).toRingHom) ≫
        InfOffC1Geo.cInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) κ := by
  set φ := Algebra.TensorProduct.lift (Algebra.ofId κ κ) ((Algebra.ofId (R p) κ).comp rhoInf) (fun _ _ => Commute.all _ _)
  apply pullback.hom_ext
  · rw [Category.assoc, InfOffC1Geo.cInf_fst, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    show pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst, εinf_chart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    ext b
    show (algebraMap (R p) κ) (rhoInf b) = φ ((1 : κ) ⊗ₜ[R p] b)
    rw [Algebra.TensorProduct.lift_tmul]
    simp [Algebra.ofId_apply]
  · rw [Category.assoc, InfOffC1Geo.cInf_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    show pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd]
    have : φ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))) =
        RingHom.id κ := by
      ext a
      simp [φ, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
    rw [this, CommRingCat.ofHom_id, Spec.map_id]

theorem mul_mem_nonunits {F : Type*} [Field F] (W : ValuationSubring F) {x y : F} (hx : x ∈ W)
    (hy : y ∈ W.nonunits) : x * y ∈ W.nonunits := by
  obtain ⟨hy', hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hy
  refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨mul_mem hx hy', ?_⟩
  have : (⟨x * y, mul_mem hx hy'⟩ : W) = ⟨x, hx⟩ * ⟨y, hy'⟩ := rfl
  rw [this]
  exact Ideal.mul_mem_left _ _ hm

theorem exists_specMap_eq_of_not_mem {R : Type} [CommRing R] (κ : Type) [Field κ] [Algebra R κ]
    {A M : Type} [CommRing A] [CommRing M] [Algebra R A] [Algebra R M] (f : A →ₐ[R] M) (s : A)
    (hM : letI := f.toRingHom.toAlgebra; IsLocalization.Away s M)
    (Q : PrimeSpectrum (κ ⊗[R] A)) (hs : (1 : κ) ⊗ₜ[R] s ∉ Q.asIdeal) :
    ∃ 𝔐 : PrimeSpectrum (κ ⊗[R] M),
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) f).toRingHom) 𝔐 = Q := by
  letI algAM : Algebra A M := f.toRingHom.toAlgebra
  haveI : IsScalarTower R A M := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  letI algT : Algebra (κ ⊗[R] A) (κ ⊗[R] M) := (Algebra.TensorProduct.map (AlgHom.id κ κ) f).toRingHom.toAlgebra
  haveI : IsScalarTower κ (κ ⊗[R] A) (κ ⊗[R] M) := IsScalarTower.of_algebraMap_eq' <| by
    show algebraMap κ (κ ⊗[R] M) = (Algebra.TensorProduct.map (AlgHom.id κ κ) f).toRingHom.comp (algebraMap κ (κ ⊗[R] A))
    rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
  haveI : IsLocalization ((Submonoid.powers s).map (Algebra.TensorProduct.includeRight (R := R) (A := κ))) (κ ⊗[R] M) :=
    IsLocalization.tensorProduct_tensorProduct_right R κ (Submonoid.powers s) M (by
      show (Algebra.TensorProduct.map (AlgHom.id κ κ) f).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
        (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := M)).toRingHom.comp f.toRingHom
      exact RingHom.ext fun b => by
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply])
  have hQ : Q ∈ Set.range (PrimeSpectrum.comap (algebraMap (κ ⊗[R] A) (κ ⊗[R] M))) := by
    rw [PrimeSpectrum.localization_comap_range (κ ⊗[R] M) ((Submonoid.powers s).map
      (Algebra.TensorProduct.includeRight (R := R) (A := κ)))]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ hmem
    apply hs
    refine Q.2.mem_of_pow_mem n ?_
    simp only [Algebra.TensorProduct.includeRight_apply, map_pow, Algebra.TensorProduct.tmul_pow, one_pow,
      SetLike.mem_coe] at hmem ⊢
    exact hmem
  obtain ⟨𝔐, h𝔐⟩ := hQ
  refine ⟨𝔐, ?_⟩
  rw [Spec.map_apply, CommRingCat.hom_ofHom]
  exact h𝔐

set_option maxHeartbeats 12800000 in

theorem dict (hpM2 : ¬ p ^ 2 ∣ M)
    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (R p) κ]
    (comp0 : fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hcomp_over : comp0 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp_ci : IsClosedImmersion comp0]
    (hcomp_pi : comp0 ≫ fibreMap π (algebraMap (R p) κ) = 𝟙 _)
    (comp1 : fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hcomp1_over : comp1 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp1_ci : IsClosedImmersion comp1]
    (hjoint : ∀ y : ↥(fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ)), y ∈ Set.range comp0.base ∨ y ∈ Set.range comp1.base)

    [hint0 : IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (res : ↥A →+* κ)
    (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries κ))
    (σst : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (hθ1 : ∀ c, θ 1 c = θ 0 (theta c))
    (hθ2 : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        θ 0 c = coeffMap res y)
    (hker_ne : RingHom.ker (θ 0) ≠ RingHom.ker (θ 1))
    (hmin : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = θ 0 (iota0 b) ^ p)
    (hminκ : minimalPrimes (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) =
        {RingHom.ker σst.toRingHom,
         Ideal.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) (theta : _ →ₐ[R p] _)).toRingHom (RingHom.ker σst.toRingHom)})
    (hlink : ∀ c : ↥(chartAlgFin p (ΓM M H) hj), σst ((1 : κ) ⊗ₜ[R p] c) = 0 ↔ θ 0 c = 0) :
    ∀ 𝔓 : PrimeSpectrum (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)),
      ((InfOffC1Geo.cFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) κ).base 𝔓 ∈ Set.range comp0.base →
        Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))
          (RingHom.ker (θ 0)) ≤ 𝔓.asIdeal) ∧
      ((InfOffC1Geo.cFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) κ).base 𝔓 ∈ Set.range comp1.base →
        Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))
          (RingHom.ker (θ 1)) ≤ 𝔓.asIdeal) := by
  classical

  let F : Type := ↥(qExpFunctionFieldC ℚ (ΓM M H))
  let F0 : Type := ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))
  let O : Type := ↥(chartAlgFin p (ΓM M H) hj)
  let B : Type := ↥(chartAlgInf p (ΓM M H) hj)
  let Mid : Type := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid (R p) F (jAt (ΓM M H) hj))
  let O0 : Type := ↥(chartAlgFin p (ΓN p M H hpM) hj)
  let cF := InfOffC1Geo.cFin (R p) F (jAt (ΓM M H) hj) κ
  let cI := InfOffC1Geo.cInf (R p) F (jAt (ΓM M H) hj) κ
  let c0 := InfOffC1Geo.cFin (R p) F0 (jAt (ΓN p M H hpM) hj) κ
  let jO : O := jChartFin p (ΓM M H) hj
  let K₀ : Ideal (κ ⊗[R p] O) := RingHom.ker σst.toRingHom
  let Tθ := Algebra.TensorProduct.map (AlgHom.id κ κ) (theta : O →ₐ[R p] O)
  let K₁ : Ideal (κ ⊗[R p] O) := Ideal.comap Tθ.toRingHom K₀
  let I : Fin 2 → Ideal (κ ⊗[R p] O) := fun i =>
    Ideal.map (Algebra.TensorProduct.includeRight : O →ₐ[R p] κ ⊗[R p] O) (RingHom.ker (θ i))

  have hK₀min : K₀ ∈ minimalPrimes (κ ⊗[R p] O) := by rw [hminκ]; exact Set.mem_insert _ _
  have hK₁min : K₁ ∈ minimalPrimes (κ ⊗[R p] O) := by rw [hminκ]; exact Set.mem_insert_of_mem _ rfl
  haveI hK₀p : K₀.IsPrime := hK₀min.1.1
  haveI hK₁p : K₁.IsPrime := hK₁min.1.1

  have hI0K0 : I 0 ≤ K₀ := by
    refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
    rw [Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply]
    exact RingHom.mem_ker.mpr ((hlink c).mpr (RingHom.mem_ker.mp hc))
  have hI1K1 : I 1 ≤ K₁ := by
    refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
    rw [Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply, Ideal.mem_comap]
    show Tθ ((1 : κ) ⊗ₜ[R p] c) ∈ K₀
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    refine RingHom.mem_ker.mpr ((hlink (theta c)).mpr ?_)
    rw [← hθ1]; exact RingHom.mem_ker.mp hc

  have hθmin : ∀ i : Fin 2, RingHom.ker (θ i) ∈ (Ideal.span {((p : ℕ) : O)}).minimalPrimes := by
    intro i; fin_cases i
    · rw [hmin]; exact Set.mem_insert _ _
    · rw [hmin]; exact Set.mem_insert_of_mem _ rfl
  have hincomp : ∀ i k : Fin 2, RingHom.ker (θ i) ≤ RingHom.ker (θ k) → RingHom.ker (θ i) = RingHom.ker (θ k) := by
    intro i k h
    exact le_antisymm h ((hθmin k).2 ⟨(hθmin i).1.1, (hθmin i).1.2⟩ h)

  have hnogo0 : ¬ I 0 ≤ K₁ := by
    intro h
    apply hker_ne
    refine hincomp 0 1 fun c hc => ?_
    have h1 : (1 : κ) ⊗ₜ[R p] c ∈ K₁ := h (Ideal.mem_map_of_mem _ hc)
    rw [Ideal.mem_comap] at h1
    change Tθ ((1 : κ) ⊗ₜ[R p] c) ∈ K₀ at h1
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at h1
    have := (hlink (theta c)).mp (RingHom.mem_ker.mp h1)
    rw [RingHom.mem_ker, hθ1]; exact this
  have hnogo1 : ¬ I 1 ≤ K₀ := by
    intro h
    apply hker_ne
    refine (hincomp 1 0 fun c hc => ?_).symm
    have h1 : (1 : κ) ⊗ₜ[R p] c ∈ K₀ := h (Ideal.mem_map_of_mem _ hc)
    exact RingHom.mem_ker.mpr ((hlink c).mp (RingHom.mem_ker.mp h1))

  have hK01 : ∀ 𝔓 : PrimeSpectrum (κ ⊗[R p] O), K₀ ≤ 𝔓.asIdeal ∨ K₁ ≤ 𝔓.asIdeal := by
    intro 𝔓
    obtain ⟨q, hq, hq𝔓⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal (κ ⊗[R p] O)) ≤ 𝔓.asIdeal from bot_le)
    have hq' : q ∈ minimalPrimes (κ ⊗[R p] O) := hq
    rw [hminκ] at hq'
    rcases hq' with rfl | rfl
    · exact Or.inl hq𝔓
    · exact Or.inr hq𝔓

  haveI : Nontrivial (κ ⊗[R p] O0) :=
    (InfOffC1Tensor.tensorRingHom (p := p) (algebraMap κ (LaurentSeries κ)) ((θ 0).comp iota0.toRingHom)).domain_nontrivial
  haveI : Nonempty ↥(Spec (CommRingCat.of (κ ⊗[R p] O0))) := inferInstance
  haveI hdom0 : IsDomain (κ ⊗[R p] O0) := by
    have := isIntegral_of_isOpenImmersion c0
    exact (affine_isIntegral_iff (CommRingCat.of (κ ⊗[R p] O0))).mp this

  obtain ⟨σ₀, h0, hcompσ, -⟩ := ModularCurve.XHDRLevel.exists_retraction_chart_comp_zero_eq p M H hpM hpM2 hj π iota0 iota0_spec
    pi_chart κ c0 (InfOffC1Geo.cFin_fst (R p) F0 (jAt (ΓN p M H hpM) hj) κ) (InfOffC1Geo.cFin_snd (R p) F0 (jAt (ΓN p M H hpM) hj) κ)
    cF (InfOffC1Geo.cFin_fst (R p) F (jAt (ΓM M H) hj) κ) (InfOffC1Geo.cFin_snd (R p) F (jAt (ΓM M H) hj) κ) ![comp0, comp1]
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> simp <;> infer_instance)
    (by show comp0 ≫ _ = _; exact hcomp_pi)
  replace hcompσ : c0 ≫ comp0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ cF := hcompσ

  haveI hσp : (RingHom.ker σ₀.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hI0σ : I 0 ≤ RingHom.ker σ₀.toRingHom := by
    rcases hσp.mul_le.mp (InfOffC1Alg.map_ker_mul_map_ker_le (p := p) κ θ hmin (RingHom.ker σ₀.toRingHom)) with h | h
    · exact h
    · exact (InfOffC1AlgH.case_one_false (p := p) M H hpM hj iota0 iota0_spec theta A κ res θ hθ1 hθ2 hfrob σ₀ h0 h).elim

  let ξ : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ)) := genericPoint _
  have hξ : ∀ z : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ)), ξ ⤳ z := fun z => genericPoint_specializes z
  have hC0 : ∀ y ∈ Set.range comp0.base, comp0.base ξ ⤳ y := by
    rintro _ ⟨z, rfl⟩; exact (hξ z).map comp0.base.hom.continuous
  have hC1 : ∀ y ∈ Set.range comp1.base, comp1.base ξ ⤳ y := by
    rintro _ ⟨z, rfl⟩; exact (hξ z).map comp1.base.hom.continuous

  have hξc0 : ξ ∈ Set.range c0 := by
    rw [(genericPoint_spec _).mem_open_set_iff c0.isOpenEmbedding.isOpen_range]
    obtain ⟨pt⟩ := (inferInstance : Nonempty (PrimeSpectrum (κ ⊗[R p] O0)))
    exact ⟨c0 pt, trivial, pt, rfl⟩
  obtain ⟨x0, hx0⟩ := hξc0
  let p₀ : PrimeSpectrum (κ ⊗[R p] O) := PrimeSpectrum.comap σ₀.toRingHom x0
  have hη₀ : comp0.base ξ = cF p₀ := by
    rw [← hx0, ← Scheme.Hom.comp_apply, hcompσ, Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom]
  have hp₀ : I 0 ≤ p₀.asIdeal := by
    refine hI0σ.trans ?_
    intro z hz
    show z ∈ Ideal.comap σ₀.toRingHom (x0 : PrimeSpectrum _).asIdeal
    rw [Ideal.mem_comap, RingHom.mem_ker.mp hz]
    exact Ideal.zero_mem _

  have hη1F : comp1.base ξ ∈ Set.range cF := by
    by_contra hno
    apply hnogo0
    have : ∀ 𝔓 : PrimeSpectrum (κ ⊗[R p] O), p₀ ≤ 𝔓 := by
      intro 𝔓
      have hmem : cF 𝔓 ∈ Set.range comp0.base := by
        rcases hjoint (cF 𝔓) with h | h
        · exact h
        · exact absurd ((hC1 _ h).mem_open cF.isOpenEmbedding.isOpen_range ⟨𝔓, rfl⟩) hno
      exact InfOffC1Geo.specializes_of_cFin (R p) F (jAt (ΓM M H) hj) κ (hη₀ ▸ hC0 _ hmem)
    exact hp₀.trans (this ⟨K₁, hK₁p⟩)
  obtain ⟨Q, hQ⟩ := hη1F
  change PrimeSpectrum (κ ⊗[R p] O) at Q

  have hcov : ∀ 𝔓 : PrimeSpectrum (κ ⊗[R p] O), p₀ ≤ 𝔓 ∨ Q ≤ 𝔓 := by
    intro 𝔓
    rcases hjoint (cF 𝔓) with h | h
    · exact Or.inl (InfOffC1Geo.specializes_of_cFin (R p) F (jAt (ΓM M H) hj) κ (hη₀ ▸ hC0 _ h))
    · exact Or.inr (InfOffC1Geo.specializes_of_cFin (R p) F (jAt (ΓM M H) hj) κ (hQ ▸ hC1 _ h))

  have hQK1 : K₁ ≤ Q.asIdeal := by
    rcases hK01 Q with h | h
    · exfalso
      apply hnogo0
      rcases hcov ⟨K₁, hK₁p⟩ with h' | h'
      · exact hp₀.trans h'
      · exact (hI0K0.trans h).trans h'
    · exact h

  intro 𝔓
  refine ⟨fun h => hp₀.trans (InfOffC1Geo.specializes_of_cFin (R p) F (jAt (ΓM M H) hj) κ (hη₀ ▸ hC0 _ h)),
    fun h => (hI1K1.trans hQK1).trans (InfOffC1Geo.specializes_of_cFin (R p) F (jAt (ΓM M H) hj) κ (hQ ▸ hC1 _ h))⟩

end InfOffC1Main
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo"

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel AlgebraicCurve.TwoChartIntegralModel"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP infSubgroup Gamma1_le_GammaH qExpFunctionFieldC qExpFunctionFieldC_mono qExpand qExpand_single jNum jq jqN evalAtJ evalAtJ_X coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff qExpand_ofPowerSeries_eq_expand coeffMap_jqModC jqModC jqModC_rat map_jqModC order_jqModC_def jqModC_ne_zero_def XHDRLevel.exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH XHDRLevel.exists_retraction_chart_comp_zero_eq XHDRLevel.exists_valuationSubring_pair_gammaH isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC XHDRLevel.comap_atkinLehner_valuationSubring_gauss_gammaH diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 transcendental_of_coe_eq_coeffEmb_jq finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH nonempty_modularPolynomialData"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X toBase chartAlgFin chartAlgInf ιFin ιInf jChartFin fibre sectionFibre fibreMap ΓN ΓM exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH exists_retraction_chart_comp_zero_eq exists_valuationSubring_pair_gammaH exists_valuationSubring_gauss_qExpFunctionFieldC comap_atkinLehner_valuationSubring_gauss_gammaH valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH"
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
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel.KerMinH"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve"

namespace HDictS1

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel"

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem gamma1_le_gammaH : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]; exact one_mem _

scoped instance finiteIndex_gammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma1_le_gammaH M H)

theorem T_mem_gammaH : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  apply gamma1_le_gammaH
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.T]

theorem coeffMap_jqModC {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') :
    coeffMap f (jqModC K) = jqModC K' := by
  ext k
  rw [coeffMap_coeff, ← map_jqModC f, HahnSeries.map_coeff]

theorem order_pow' {K : Type*} [Field K] (x : LaurentSeries K) (hx : x ≠ 0) (n : ℕ) : (x ^ n).order = n * x.order := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem mem_nonunits_comap_iff {F : Type*} [Field F] (W₀ : ValuationSubring F) (σ : F ≃+* F) (x : F) :
    x ∈ (W₀.comap σ.toRingHom).nonunits ↔ σ x ∈ W₀.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap]
  constructor
  · rintro (h | h)
    · left; rw [h, map_zero]
    · right; rw [← map_inv₀]; exact h
  · rintro (h | h)
    · left; exact (map_eq_zero_iff _ σ.injective).mp h
    · right; rw [← map_inv₀] at h; exact h

theorem exists_expand_jNum_sub_pow :
    ∃ w : PowerSeries ↥(GaloisRep.ratLocalizedAt p), PowerSeries.expand p (Fact.out : p.Prime).ne_zero (jNum.map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p))) -
      (jNum.map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p))) ^ p = PowerSeries.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) * w := by
  set u := jNum.map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p)) with hu
  set D := PowerSeries.expand p (Fact.out : p.Prime).ne_zero u - u ^ p with hD

  have hred : D.map (GaloisRep.ratLocalizedAtResidue p) = 0 := by
    rw [hD, map_sub, map_pow, PowerSeries.map_expand]
    set v := u.map (GaloisRep.ratLocalizedAtResidue p)
    have hv : PowerSeries.expand p (Fact.out : p.Prime).ne_zero v = v ^ p := by
      have h := MvPowerSeries.map_frobenius_expand p (Fact.out : p.Prime).ne_zero (f := v)
      rw [ZMod.frobenius_zmod] at h

      have hid : ∀ x : PowerSeries (ZMod p), MvPowerSeries.map (RingHom.id (ZMod p)) x = x := fun x => by
        rw [MvPowerSeries.map_id]; rfl
      rw [hid] at h
      exact h
    rw [hv, sub_self]
  have hdiv : ∀ i, ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ PowerSeries.coeff i D := fun i =>
    (KerMinH.res_eq_zero_iff p _).mp (by have := congrArg (PowerSeries.coeff i) hred; rwa [PowerSeries.coeff_map, map_zero] at this)
  choose t ht using hdiv
  exact ⟨PowerSeries.mk t, by ext i; rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ht i]⟩

theorem exists_qExpand_jqModC_sub_pow :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ w : PowerSeries ↥(GaloisRep.ratLocalizedAt p), qExpand ℚ p (jqModC ℚ) - jqModC ℚ ^ p =
      HahnSeries.single (-(p : ℤ)) (1 : ℚ) * ((p : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (w.map (GaloisRep.ratLocalizedAt p).subtype)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨w, hw⟩ := exists_expand_jNum_sub_pow p
  refine ⟨w, ?_⟩
  have hjNumQ : (jNum.map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p))).map (GaloisRep.ratLocalizedAt p).subtype = jNum.map (Int.castRingHom ℚ) := by
    rw [← RingHom.ext_int ((GaloisRep.ratLocalizedAt p).subtype.comp (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p))) (Int.castRingHom ℚ)]
    exact (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p)) (GaloisRep.ratLocalizedAt p).subtype)) jNum).symm
  have hj' : jqModC ℚ = HahnSeries.single (-1 : ℤ) (1 : ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := rfl
  have hexp' : PowerSeries.expand p (NeZero.ne p) (PowerSeries.map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p)) jNum) -
      PowerSeries.map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p)) jNum ^ p = PowerSeries.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) * w := hw
  rw [hj', map_mul, qExpand_single, mul_pow, HahnSeries.single_pow, one_pow, ← hjNumQ, ModularCurve.qExpand_ofPowerSeries_eq_expand,
    ← map_pow (HahnSeries.ofPowerSeries ℤ ℚ), ← map_pow (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype), ← PowerSeries.map_expand,
    show (p : ℤ) * (-1 : ℤ) = p • (-1 : ℤ) from by simp, ← mul_sub, ← map_sub, ← map_sub, hexp', map_mul, PowerSeries.map_C,
    map_natCast, map_mul, HahnSeries.ofPowerSeries_C, map_natCast]
  congr 1
  simp

theorem sub_pow_mem_nonunits (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (hx : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; (x : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ))
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (hW₀p : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀.nonunits) :
    x - (jAt (CohCarrier.GammaH M H) hj) ^ p ∈ W₀.nonunits := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp := (Fact.out : p.Prime)
  obtain ⟨w, hw⟩ := exists_qExpand_jqModC_sub_pow p
  have hP0L : (p : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := ℚ)) p]
    exact fun h => (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℚ) ≠ 0) (HahnSeries.C_injective (h.trans HahnSeries.C_zero.symm))
  have hp0F : (p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≠ 0 := by exact_mod_cast hp.ne_zero
  set g : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := (x - (jAt (CohCarrier.GammaH M H) hj) ^ p) * ((p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))⁻¹ with hg
  have hgW : g ∈ W₀ := by
    rw [hW₀]
    refine ⟨w, PowerSeries.X ^ p, ?_, ?_⟩
    · rw [map_pow, PowerSeries.map_X]; exact pow_ne_zero _ PowerSeries.X_ne_zero
    · rw [hg]; push_cast
      rw [hx, coe_jAt, map_pow, PowerSeries.map_X, map_pow, HahnSeries.ofPowerSeries_X, hw]
      have e : HahnSeries.single (-(p : ℤ)) (1 : ℚ) * HahnSeries.single (1 : ℤ) (1 : ℚ) ^ p = 1 := by
        rw [HahnSeries.single_pow, one_pow, HahnSeries.single_mul_single, mul_one, ← HahnSeries.single_zero_one]; congr 1; simp
      calc HahnSeries.single (-(p : ℤ)) (1 : ℚ) * ((p : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (w.map (GaloisRep.ratLocalizedAt p).subtype)) *
            (p : LaurentSeries ℚ)⁻¹ * HahnSeries.single (1 : ℤ) (1 : ℚ) ^ p
          = (HahnSeries.single (-(p : ℤ)) (1 : ℚ) * HahnSeries.single (1 : ℤ) (1 : ℚ) ^ p) *
            ((p : LaurentSeries ℚ) * (p : LaurentSeries ℚ)⁻¹) * HahnSeries.ofPowerSeries ℤ ℚ (w.map (GaloisRep.ratLocalizedAt p).subtype) := by ring
        _ = _ := by rw [e, mul_inv_cancel₀ hP0L, one_mul, one_mul]
  have hPF : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) = (p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := map_natCast _ p
  have heq : x - (jAt (CohCarrier.GammaH M H) hj) ^ p = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) * g := by
    rw [hPF, hg, mul_comm, inv_mul_cancel_right₀ hp0F]
  rw [heq, ValuationSubring.mem_nonunits_iff, map_mul]
  have h1 := (ValuationSubring.mem_nonunits_iff _).mp (hW₀p _ (Ideal.mem_span_singleton_self _))
  have h2 := (W₀.valuation_le_one_iff _).mpr hgW
  calc W₀.valuation (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) * W₀.valuation g
      ≤ W₀.valuation (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact h1

end HDictS1
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.HDictS1"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve _root_.ModularCurve.XHDRLevel _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel in

theorem orientation_witness
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (κ : Type) [Field κ] [CharP κ p] (res : ↥A →+* κ)
    (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries κ))
    (hθ1 : ∀ c, θ 1 c = θ 0 (theta c))
    (hθ2 : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ↥A), coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) → θ 0 c = coeffMap res y)
    (hker_ne : RingHom.ker (θ 0) ≠ RingHom.ker (θ 1))
    (hmin : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = θ 0 (iota0 b) ^ p)
    (σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) → ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ))
    (hσj' : σ (σ (jAt (ΓM M H) hj)) = jAt (ΓM M H) hj)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (hW₀R : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀)
    (hW₀p : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀.nonunits)
    (hW₀j : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ W₀ ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ W₀) :
    ∃ c₀ : ↥(chartAlgFin p (ΓM M H) hj), θ 0 c₀ ≠ 0 ∧ ((c₀ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ (W₀.comap σ.toAlgHom.toRingHom).nonunits := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp := (Fact.out : p.Prime)
  set W₁ := W₀.comap σ.toAlgHom.toRingHom with hW₁

  set jN : ↥(chartAlgFin p (ΓN p M H hpM) hj) := AlgebraicCurve.TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) with hjN
  have hjNL : (((jN : ↥(chartAlgFin p (ΓN p M H hpM) hj)) : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = jqModC ℚ := by
    rw [hjN, AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin, coe_jAt]
  set jM : ↥(chartAlgFin p (ΓM M H) hj) := iota0 jN with hjM
  have hjML : (((jM : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = jqModC ℚ := by rw [hjM, iota0_spec, hjNL]
  have hjMF : ((jM : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = jAt (ΓM M H) hj := Subtype.ext (by rw [hjML, coe_jAt])
  set e₁ : ↥(chartAlgFin p (ΓM M H) hj) := theta (iota0 jN) with he₁
  have he₁F : ((e₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = σ (jAt (ΓM M H) hj) := by
    apply Subtype.ext
    rw [he₁, htheta, hσ (jAt (ΓM M H) hj) (jAt (ΓN p M H hpM) hj) (by rw [coe_jAt, coe_jAt]),
      AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin]
  set c₀ : ↥(chartAlgFin p (ΓM M H) hj) := jM - e₁ ^ p with hc₀

  have hθjM : θ 0 jM = jqModC κ := by
    rw [hθ2 jM (jqModC ↥A)]
    · exact HDictS1.coeffMap_jqModC res
    · rw [HDictS1.coeffMap_jqModC, hjML]
      exact (HDictS1.coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm
  have hθe₁ : θ 0 e₁ = jqModC κ ^ p := by rw [he₁, hfrob, ← hjM, hθjM]
  have hθc₀ : θ 0 c₀ ≠ 0 := by
    rw [hc₀, map_sub, map_pow, hθjM, hθe₁, ← pow_mul]
    intro h
    have h' : jqModC κ = jqModC κ ^ (p * p) := sub_eq_zero.mp h
    have ho := congrArg HahnSeries.order h'
    rw [HDictS1.order_pow' _ (jqModC_ne_zero_def κ), order_jqModC_def] at ho
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    push_cast at ho
    nlinarith

  have hc₀F : ((c₀ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = jAt (ΓM M H) hj - (σ (jAt (ΓM M H) hj)) ^ p := by
    rw [hc₀]; push_cast; rw [hjMF, he₁F]
  have hσc₀ : σ ((c₀ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = σ (jAt (ΓM M H) hj) - (jAt (ΓM M H) hj) ^ p := by
    rw [hc₀F, map_sub, map_pow, hσj']
  have hσc₀nu : σ ((c₀ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits := by
    rw [hσc₀]
    exact HDictS1.sub_pow_mem_nonunits p M H hpM hj _
      (hσ (jAt (ΓM M H) hj) (jAt (ΓN p M H hpM) hj) (by rw [coe_jAt, coe_jAt])) W₀ hW₀ hW₀p
  have hc₀W₁ : ((c₀ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits := by
    rw [hW₁, ValuationSubring.mem_nonunits_iff_or]
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp hσc₀nu with h | h
    · left; exact (map_eq_zero_iff σ σ.injective).mp h
    · right
      intro hm
      apply h
      have := ValuationSubring.mem_comap.mp hm
      simpa [map_inv₀] using this
  exact ⟨c₀, hθc₀, hc₀W₁⟩

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve _root_.ModularCurve.XHDRLevel _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel in

theorem hdict_lemma
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (κ : Type) [Field κ] [CharP κ p] (res : ↥A →+* κ)
    (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries κ))
    (hθ1 : ∀ c, θ 1 c = θ 0 (theta c))
    (hθ2 : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ↥A), coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) → θ 0 c = coeffMap res y)
    (hker_ne : RingHom.ker (θ 0) ≠ RingHom.ker (θ 1))
    (hmin : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = θ 0 (iota0 b) ^ p)
    (σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) → ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ))
    (hσj' : σ (σ (jAt (ΓM M H) hj)) = jAt (ΓM M H) hj)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (hW₀R : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀)
    (hW₀p : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀.nonunits)
    (hW₀j : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ W₀ ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ W₀) :
    ∀ c : ↥(chartAlgFin p (ΓM M H) hj), ((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ (W₀.comap σ.toAlgHom.toRingHom).nonunits → θ 1 c = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp := (Fact.out : p.Prime)
  set W₁ := W₀.comap σ.toAlgHom.toRingHom with hW₁

  obtain ⟨⟨g1, g1'⟩, g2, g6, hne⟩ :=
    ModularCurve.XHDRLevel.comap_atkinLehner_valuationSubring_gauss_gammaH p M H hpM hpM2 hHp hj σ hσ W₀ hW₀
  have hcompl : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V) →
      (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ := fun V h1 h2 h3 =>
    ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH p M H hpM hpM2 hHp hj σ hσ W₀ hW₀ V h1 h2 h3
  have hW1 : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits := by
    intro i; fin_cases i
    · exact ⟨hW₀R, hW₀p⟩
    · exact ⟨g1, g1'⟩
  have hW2 : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i) := by
    intro i; fin_cases i
    · exact hW₀j
    · exact g2
  haveI : (CohCarrier.GammaH M H).FiniteIndex := HDictS1.finiteIndex_gammaH M H
  have hFD := KerMinH.finiteDimensional_adjoin_jAt (CohCarrier.GammaH M H) (HDictS1.T_mem_gammaH M H) hj
  have hsep := KerMinH.isSeparable_adjoin_jAt (CohCarrier.GammaH M H) (HDictS1.T_mem_gammaH M H) hj
  obtain ⟨hi, -, -⟩ := KerMinH.kerMin_of_pair p M H hj hFD hsep W₀ W₁ hW1 hW2 (fun h => hne h.symm) hcompl

  obtain ⟨c₀, hθc₀, hc₀W₁⟩ := orientation_witness p M H hpM hpM2 hHp hj iota0 iota0_spec theta htheta A κ res θ hθ1 hθ2 hker_ne hmin hfrob
    σ hσ hσj' W₀ hW₀ hW₀R hW₀p hW₀j

  have hk0 : RingHom.ker (θ 0) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert _ _
  have hk1 : RingHom.ker (θ 1) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert_of_mem _ rfl
  rcases hi _ hk0 with h0W₀ | h0W₁
  · rcases hi _ hk1 with h1W₀ | h1W₁
    · exfalso; apply hker_ne; ext b; rw [h0W₀ b, h1W₀ b]
    · intro c hc
      exact RingHom.mem_ker.mp ((h1W₁ c).mpr hc)
  · exfalso
    exact hθc₀ (RingHom.mem_ker.mp ((h0W₁ c₀).mpr hc₀W₁))

theorem hdict2
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (κ : Type) [Field κ] [CharP κ p] (res : ↥A →+* κ)
    (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries κ))
    (hθ1 : ∀ c, θ 1 c = θ 0 (theta c))
    (hθ2 : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ↥A), coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) → θ 0 c = coeffMap res y)
    (hker_ne : RingHom.ker (θ 0) ≠ RingHom.ker (θ 1))
    (hmin : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = θ 0 (iota0 b) ^ p)
    (σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) → ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ))
    (hσj' : σ (σ (jAt (ΓM M H) hj)) = jAt (ΓM M H) hj)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (hW₀R : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀)
    (hW₀p : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀.nonunits)
    (hW₀j : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ W₀ ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ W₀) :
    (∀ c : ↥(chartAlgFin p (ΓM M H) hj), c ∈ RingHom.ker (θ 0) ↔ ((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₀.nonunits) ∧
    (∀ c : ↥(chartAlgFin p (ΓM M H) hj), c ∈ RingHom.ker (θ 1) ↔ ((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ (W₀.comap σ.toAlgHom.toRingHom).nonunits) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp := (Fact.out : p.Prime)
  set W₁ := W₀.comap σ.toAlgHom.toRingHom with hW₁

  obtain ⟨⟨g1, g1'⟩, g2, g6, hne⟩ :=
    ModularCurve.XHDRLevel.comap_atkinLehner_valuationSubring_gauss_gammaH p M H hpM hpM2 hHp hj σ hσ W₀ hW₀
  have hcompl : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V) →
      (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ := fun V h1 h2 h3 =>
    ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH p M H hpM hpM2 hHp hj σ hσ W₀ hW₀ V h1 h2 h3
  have hW1 : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits := by
    intro i; fin_cases i
    · exact ⟨hW₀R, hW₀p⟩
    · exact ⟨g1, g1'⟩
  have hW2 : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i) := by
    intro i; fin_cases i
    · exact hW₀j
    · exact g2
  haveI : (CohCarrier.GammaH M H).FiniteIndex := HDictS1.finiteIndex_gammaH M H
  have hFD := KerMinH.finiteDimensional_adjoin_jAt (CohCarrier.GammaH M H) (HDictS1.T_mem_gammaH M H) hj
  have hsep := KerMinH.isSeparable_adjoin_jAt (CohCarrier.GammaH M H) (HDictS1.T_mem_gammaH M H) hj
  obtain ⟨hi, -, -⟩ := KerMinH.kerMin_of_pair p M H hj hFD hsep W₀ W₁ hW1 hW2 (fun h => hne h.symm) hcompl

  obtain ⟨c₀, hθc₀, hc₀W₁⟩ := orientation_witness p M H hpM hpM2 hHp hj iota0 iota0_spec theta htheta A κ res θ hθ1 hθ2 hker_ne hmin hfrob
    σ hσ hσj' W₀ hW₀ hW₀R hW₀p hW₀j

  have hk0 : RingHom.ker (θ 0) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert _ _
  have hk1 : RingHom.ker (θ 1) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert_of_mem _ rfl
  rcases hi _ hk0 with h0W₀ | h0W₁
  · rcases hi _ hk1 with h1W₀ | h1W₁
    · exfalso; apply hker_ne; ext b; rw [h0W₀ b, h1W₀ b]
    · exact ⟨fun c => h0W₀ c, fun c => h1W₁ c⟩
  · exfalso
    exact hθc₀ (RingHom.mem_ker.mp ((h0W₁ c₀).mpr hc₀W₁))

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.HDictS1"

namespace WChartField

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel Polynomial"

theorem mem_chartAlgFin_of_coe_eq_qExpand_jqModC (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ))
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (y : ↥(qExpFunctionFieldC ℚ Γ))
    (hy : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; (y : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ)) :
    y ∈ chartAlgFin p Γ hj := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  let F : Type := ↥(qExpFunctionFieldC ℚ Γ)
  let A : Subalgebra (R p) F := Algebra.adjoin (R p) ({jAt Γ hj} : Set F)
  let jA : ↥A := ⟨jAt Γ hj, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  let P : Polynomial ↥A := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥A) jA)
  have hPmonic : P.Monic := data.monic.map _
  show IsIntegral (↥A) y
  refine ⟨P, hPmonic, ?_⟩
  let c : F →+* LaurentSeries ℚ := (qExpFunctionFieldC ℚ Γ).toSubfield.subtype
  have hc : ∀ z : F, c z = (z : LaurentSeries ℚ) := fun _ => rfl
  have hcinj : Function.Injective c := Subtype.coe_injective
  apply hcinj
  rw [map_zero, Polynomial.eval₂_map, Polynomial.hom_eval₂, hc y, hy]
  have step : c.comp ((algebraMap (↥A) F).comp (Polynomial.eval₂RingHom (Int.castRingHom ↥A) jA)) = evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJ_X, hc]
    show ((jAt Γ hj : F) : LaurentSeries ℚ) = jq
    rw [coe_jAt, jqModC_rat]
  rw [step]
  have e : qExpand ℚ p (jqModC ℚ) = jqN p := by rw [jqModC_rat]; rfl
  rw [e]
  exact data.eval_eq_zero

theorem exists_algEquiv_chartAlgFin_coe_eq (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ))
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σ : ↥(qExpFunctionFieldC ℚ Γ) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ Γ))
    (h1 : σ (jAt Γ hj) ∈ chartAlgFin p Γ hj) (h2 : σ.symm (jAt Γ hj) ∈ chartAlgFin p Γ hj) :
    ∃ theta : ↥(chartAlgFin p Γ hj) ≃ₐ[R p] ↥(chartAlgFin p Γ hj),
      ∀ b : ↥(chartAlgFin p Γ hj), ((theta b : ↥(chartAlgFin p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) = σ (b : ↥(qExpFunctionFieldC ℚ Γ)) := by
  classical
  let F : Type := ↥(qExpFunctionFieldC ℚ Γ)
  let O : Subalgebra (R p) F := chartAlgFin p Γ hj
  let A : Subalgebra (R p) F := Algebra.adjoin (R p) ({jAt Γ hj} : Set F)

  have hfixR : ∀ (τ : F ≃ₐ[ℚ] F) (r : R p), τ (algebraMap (R p) F r) = algebraMap (R p) F r := by
    intro τ r
    have hext : ∀ (f g : R p →+* F), f = g := by
      intro f g
      haveI : IsLocalization.AtPrime (R p) (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
      exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)
    have e : algebraMap (R p) F = (algebraMap ℚ F).comp (algebraMap (R p) ℚ) := hext _ _
    rw [e, RingHom.comp_apply, AlgEquiv.commutes]

  have hstab : ∀ (τ : F ≃ₐ[ℚ] F), τ (jAt Γ hj) ∈ O → ∀ x ∈ O, τ x ∈ O := by
    intro τ hτj x hx
    have hA : ∀ a ∈ A, τ a ∈ O := by
      intro a ha
      refine Algebra.adjoin_induction (hx := ha) ?_ ?_ ?_ ?_
      · rintro _ rfl; exact hτj
      · intro r; rw [hfixR]; exact Subalgebra.algebraMap_mem _ r
      · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
      · intro a b _ _ ha hb; rw [map_mul]; exact mul_mem ha hb
    have hxint : IsIntegral (↥A) x := hx

    let IC : Subalgebra (↥A) F := integralClosure (↥A) F
    have hICO : ∀ z : F, z ∈ IC ↔ z ∈ O := fun z => Iff.rfl
    let φ : ↥A →+* ↥IC := ((τ : F →+* F).comp A.val.toRingHom).codRestrict IC.toSubring (fun a => (hICO _).mpr (hA a a.2))
    have hcomp : (algebraMap (↥IC) F).comp φ = (τ : F →+* F).comp (algebraMap (↥A) F) := by
      ext a; rfl
    have hint : IsIntegral (↥IC) (τ x) := IsIntegral.map_of_comp_eq φ (τ : F →+* F) hcomp hxint
    exact (hICO _).mp (isIntegral_trans (R := ↥A) (τ x) hint)
  have hσO : ∀ x ∈ O, σ x ∈ O := hstab σ h1
  have hσ'O : ∀ x ∈ O, σ.symm x ∈ O := hstab σ.symm h2

  let t : ↥O →ₐ[R p] ↥O :=
    { toFun := fun b => ⟨σ b, hσO b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp)
      commutes' := fun r => Subtype.ext (by
        show σ (algebraMap (R p) F r) = algebraMap (R p) F r
        exact hfixR σ r) }
  let t' : ↥O →ₐ[R p] ↥O :=
    { toFun := fun b => ⟨σ.symm b, hσ'O b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp)
      commutes' := fun r => Subtype.ext (by
        show σ.symm (algebraMap (R p) F r) = algebraMap (R p) F r
        exact hfixR σ.symm r) }
  refine ⟨AlgEquiv.ofAlgHom t t' (AlgHom.ext fun b => Subtype.ext (σ.apply_symm_apply _)) (AlgHom.ext fun b => Subtype.ext (σ.symm_apply_apply _)), fun b => rfl⟩

end WChartField
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.InfOffC1Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.HDictS1"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp.ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∃ P : Fin 2 → Ideal ↥(chartAlgFin p (ΓM M H) hj),
      (∀ i, P i ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes) ∧ P 0 ≠ P 1 ∧
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
        [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
        (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
        (i : Fin 2) (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
        (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)),
        (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y =
          (ιFin p (ΓM M H) hj).base 𝔮 →
        y ∈ Set.range (𝔛.comp A hA ρ hρ i).base → P i ≤ 𝔮.asIdeal := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : p.Prime := Fact.out

  let F : Type := ↥(qExpFunctionFieldC ℚ (ΓM M H))
  let O : Type := ↥(chartAlgFin p (ΓM M H) hj)
  let jF : F := jAt (ΓM M H) hj

  have hpN : ¬ p ∣ M / p := by
    intro h; apply hpM2; rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) hp.pos).ne'⟩
  obtain ⟨σ, hσi, hσii⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  obtain ⟨W₀, hW₀, hW₀R, hW₀p, hW₀j, -⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC p (ΓM M H) hj
  set W₁ := W₀.comap σ.toAlgHom.toRingHom with hW₁
  obtain ⟨⟨g1, g1'⟩, g2, g6, hne⟩ :=
    ModularCurve.XHDRLevel.comap_atkinLehner_valuationSubring_gauss_gammaH p M H hpM hpM2 hHp hj σ hσi W₀ hW₀
  have hcompl : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V) →
      (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ := fun V h1 h2 h3 =>
    ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH p M H hpM hpM2 hHp hj σ hσi W₀ hW₀ V h1 h2 h3
  have hW1 : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits := by
    intro i; fin_cases i
    · exact ⟨hW₀R, hW₀p⟩
    · exact ⟨g1, g1'⟩
  have hW2 : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i) := by
    intro i; fin_cases i
    · exact hW₀j
    · exact g2
  haveI : (CohCarrier.GammaH M H).FiniteIndex := HDictS1.finiteIndex_gammaH M H
  have hFD := ModularCurve.XHDRLevel.KerMinH.finiteDimensional_adjoin_jAt (CohCarrier.GammaH M H) (HDictS1.T_mem_gammaH M H) hj
  have hsep := ModularCurve.XHDRLevel.KerMinH.isSeparable_adjoin_jAt (CohCarrier.GammaH M H) (HDictS1.T_mem_gammaH M H) hj
  obtain ⟨-, hii, ⟨b0, hb0W0, hb0W1⟩, -⟩ := ModularCurve.XHDRLevel.KerMinH.kerMin_of_pair p M H hj hFD hsep W₀ W₁ hW1 hW2 (fun h => hne h.symm) hcompl
  choose Pf hPf using hii
  refine ⟨Pf, fun i => (hPf i).1, ?_, ?_⟩
  ·
    intro heq
    have h0 : b0 ∈ Pf 0 := ((hPf 0).2 b0).mpr hb0W0
    rw [heq] at h0
    exact hb0W1 (((hPf 1).2 b0).mp h0)

  intro A hA _ _ ρ hρ i y 𝔮 hy hyc
  letI instAlg : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  let κ : Type := IsLocalRing.ResidueField ↥A

  let j0 : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) := jAt (ΓN p M H hpM) hj
  have hjF : ((jF : F) : LaurentSeries ℚ) = jqModC ℚ := coe_jAt _ _
  have hj0 : ((j0 : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = jqModC ℚ := coe_jAt _ _
  have hσj : ((σ jF : F) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ) := by
    rw [hσi jF j0 (by rw [hjF, hj0]), hj0]
  have h1 : σ jF ∈ chartAlgFin p (ΓM M H) hj := WChartField.mem_chartAlgFin_of_coe_eq_qExpand_jqModC p (ΓM M H) hj _ hσj
  have hσσj : σ (σ jF) = jF := by
    have hcop : Nat.Coprime p (M / p) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
    have key := hσii (ZMod.unitOfCoprime p hcop) (ZMod.coe_unitOfCoprime p hcop) (σ jF) j0 (by rw [hσj, hj0])
    rw [ModularCurve.diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 (M / p) (infSubgroup p M H hpM) _ _
      (jqModC ℚ) (qExpFunctionFieldC_mono ℚ le_top hj) (by show coeffEmb _ _ = _; rw [hj0])] at key
    apply Subtype.ext
    apply HahnSeries.ext
    funext k
    have hk := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff k) key
    simp only [coeffEmb_coeff] at hk
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective hk
  have h2 : σ.symm jF ∈ chartAlgFin p (ΓM M H) hj := by
    have : σ.symm jF = σ jF := by rw [AlgEquiv.symm_apply_eq, hσσj]
    rw [this]; exact h1
  obtain ⟨theta, htb⟩ := WChartField.exists_algEquiv_chartAlgFin_coe_eq p (ΓM M H) hj σ h1 h2
  have htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (𝔛.iota0 b) : O) : F) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := by
    intro b
    rw [htb]
    exact hσi _ b (𝔛.iota0_spec b)
  have hσj' : σ (σ (jAt (ΓM M H) hj)) = jAt (ΓM M H) hj := hσσj

  obtain ⟨θ, σst, hθ1, hθ2, hker_ne, hmin, hfrob, -, -, -, hminκ, -, hlink⟩ :=
    ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH
      p M H hpM hpM2 hHp hj 𝔛.iota0 𝔛.iota0_spec theta htheta A hA ρ hρ

  haveI hint0 : IsIntegral (fibre (Γ := (ΓN p M H hpM)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
    ModularCurve.isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP (M / p)
      (ΓN p M H hpM) (ModularCurve.Gamma1_le_GammaH (M / p) _) (CohCarrier.GammaH_le_Gamma0 _) p hpN
      (jAt (ΓN p M H hpM) hj) (coe_jAt _ _) κ

  obtain ⟨hk0, hk1⟩ := hdict2 p M H hpM hpM2 hHp hj 𝔛.iota0 𝔛.iota0_spec theta htheta A κ (IsLocalRing.residue ↥A) θ hθ1 hθ2 hker_ne hmin hfrob
    σ hσi hσj' W₀ hW₀ hW₀R hW₀p hW₀j
  have hPk : ∀ (k : Fin 2) (b : O), b ∈ Pf k → b ∈ RingHom.ker (θ k) := by
    intro k b hb
    fin_cases k
    · exact (hk0 b).mpr (((hPf 0).2 b).mp hb)
    · exact (hk1 b).mpr (((hPf 1).2 b).mp hb)

  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  obtain ⟨𝔓, h𝔓⟩ : y ∈ Set.range (InfOffC1Geo.cFin (R p) F (jAt (ΓM M H) hj) κ).base :=
    (InfOffC1Geo.mem_range_cFin_iff (R p) F (jAt (ΓM M H) hj) κ y).mpr ⟨𝔮, hy.symm⟩
  have h𝔮 : 𝔮 = PrimeSpectrum.comap (Algebra.TensorProduct.includeRight (R := R p) (A := κ) (B := O)).toRingHom 𝔓 := by
    apply (ιFin p (ΓM M H) hj).isOpenEmbedding.injective
    rw [← hy, ← h𝔓, ← Scheme.Hom.comp_apply, InfOffC1Geo.cFin_fst, Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom]

  have hd := InfOffC1Main.dict p M H hpM hj hpM2 𝔛.π 𝔛.iota0 𝔛.iota0_spec 𝔛.pi_chart theta κ (𝔛.comp A hA ρ hρ 0) (𝔛.comp_over A hA ρ hρ 0)
    (𝔛.comp_pi A hA ρ hρ) (𝔛.comp A hA ρ hρ 1) (𝔛.comp_over A hA ρ hρ 1) (𝔛.comp_jointly_surjective A hA ρ hρ)
    A (IsLocalRing.residue ↥A) θ σst hθ1 hθ2 hker_ne hmin hfrob hminκ hlink 𝔓

  have hIle : Ideal.map (Algebra.TensorProduct.includeRight : O →ₐ[R p] κ ⊗[R p] O) (RingHom.ker (θ i)) ≤ 𝔓.asIdeal := by
    fin_cases i
    · exact hd.1 (h𝔓 ▸ hyc)
    · exact hd.2 (h𝔓 ▸ hyc)
  intro b hb
  have hbk : b ∈ RingHom.ker (θ i) := hPk i b hb
  have : (1 : κ) ⊗ₜ[R p] b ∈ 𝔓.asIdeal := hIle (Ideal.mem_map_of_mem _ hbk)
  rw [h𝔮]
  show b ∈ Ideal.comap _ 𝔓.asIdeal
  rw [Ideal.mem_comap]
  exact this

end S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgFin_le_of_mem_range_comp (solution)
