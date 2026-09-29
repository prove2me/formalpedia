-- Prove2me | solution 1 for ModularCurve.XHDRLevel.comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4581e8db-e741-57cf-ba86-dfa1da6e5621

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_ModularCurve_FrobeniusModL
import Theorems.Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_XHDRLevel_exists_retraction_chart_comp_zero_eq
import Theorems.Thm_ModularCurve_XHDRLevel_retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime
import Theorems.Thm_ModularCurve_XHDRLevel_chart_comp_fibreMap_eq_specMap_tensor_comp_chart
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel NeronModelInfra"
open scoped MatrixGroups TensorProduct

section
open AlgebraicCurve.TwoChartIntegralModel
namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC qExpand qExpand_coeff_of_not_dvd jq coeffMap_coeff coeffEmb coeffEmb_coeff pow_char_eq_coeffMap_frobenius_qExpand jqModC coeff_jqModC_neg_one exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed order_jqModC XHDRLevel.exists_retraction_chart_comp_zero_eq XHDRLevel.retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime XHDRLevel.chart_comp_fibreMap_eq_specMap_tensor_comp_chart transcendental_of_coe_eq_coeffEmb_jq XHDRLevel.exists_valuationSubring_pair_gammaH finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X toBase chartAlgFin chartAlgInf ιFin ιInf jChartFin fibre fibreMap overOfIso ΓN ΓM exists_retraction_chart_comp_zero_eq retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime chart_comp_fibreMap_eq_specMap_tensor_comp_chart exists_valuationSubring_pair_gammaH"
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
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel.KerMinH"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve"
end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel.KerMinH"

namespace NoSecH

variable {p : ℕ} [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

theorem ringHom_ext_zp {P : Type*} [Semiring P] (f g : ℤp →+* P) : f = g := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  haveI : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

def algHomOfRingHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤp A] [Algebra ℤp B] (f : A →+* B) :
    A →ₐ[ℤp] B :=
  { f with
    commutes' := fun c => RingHom.congr_fun (ringHom_ext_zp (p := p) (f.comp (algebraMap ℤp A)) (algebraMap ℤp B)) c }

theorem algHomOfRingHom_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤp A] [Algebra ℤp B]
    (f : A →+* B) (a : A) : algHomOfRingHom (p := p) f a = f a := rfl

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

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

theorem one_tmul_natCast_mul {M : Type*} [CommRing M] [Algebra ℤp M] (c : M) :
    (1 : κ) ⊗ₜ[ℤp] (((p : ℕ) : M) * c) = 0 := by
  rw [show ((p : ℕ) : M) * c = ((p : ℕ) : ℤp) • c by rw [Algebra.smul_def, map_natCast],
    ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_natCast, CharP.cast_eq_zero, TensorProduct.zero_tmul]

theorem false_of_one_tmul_j_eq_pow
    (K : Type) [Field K] [Algebra κ K] (g₀ : ↥(chartAlgFin p (ΓN p M H hpM) hj) →+* LaurentSeries K)
    (hg₀ : g₀ (jChartFin p (ΓN p M H hpM) hj) = jqModC K)
    (s : κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj)) (hs : (1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj = s ^ p) : False := by

  let χ : κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj) →+* LaurentSeries K :=
    tensorRingHom (p := p) ((algebraMap K (LaurentSeries K)).comp (algebraMap κ K)) g₀
  have hχj : χ ((1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj) = jqModC K := by
    show tensorRingHom (p := p) _ _ _ = _
    rw [tensorRingHom_tmul, map_one, one_mul]
    exact hg₀
  have hpow : (χ s) ^ p = jqModC K := by rw [← map_pow, ← hs, hχj]
  set x := χ s with hx
  have hx0 : x ≠ 0 := by
    intro h0'
    rw [h0', zero_pow (Fact.out : p.Prime).ne_zero] at hpow
    have := congrArg HahnSeries.order hpow
    rw [HahnSeries.order_zero, order_jqModC] at this
    norm_num at this
  have hord : ∀ n : ℕ, (x ^ n).order = n * x.order := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero n hx0) hx0, ih]; push_cast; ring
  have h := congrArg HahnSeries.order hpow
  rw [hord, order_jqModC] at h
  have hdvd : (p : ℤ) ∣ 1 := ⟨-x.order, by linarith⟩
  have hp1 : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdvd
  exact (Fact.out : p.Prime).one_lt.ne' hp1

theorem map_ker_mul_map_ker_le
    {L : Type*} [CommRing L] (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* L))
    (hmin : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (P : Ideal (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))) [hP : P.IsPrime] :
    Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
        (RingHom.ker (θ 0)) *
      Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
        (RingHom.ker (θ 1)) ≤ P := by
  have hrad : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).radical ≤
      P.comap (Algebra.TensorProduct.includeRight : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj)) := by
    intro z hz
    obtain ⟨n, hn⟩ := hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
    have hc' : z ^ n = ((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj)) * c := by rw [← hc]; exact mul_comm c _
    rw [Ideal.mem_comap]
    refine hP.mem_of_pow_mem n ?_
    rw [← map_pow, hc', Algebra.TensorProduct.includeRight_apply, one_tmul_natCast_mul (p := p) κ]
    exact Ideal.zero_mem _
  rw [← Ideal.map_mul]
  refine (Ideal.map_mono ?_).trans (Ideal.map_le_iff_le_comap.mpr hrad)
  rw [← Ideal.sInf_minimalPrimes, hmin, sInf_pair]
  exact Ideal.mul_le_inf

theorem case_zero
    (ι : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
    (w : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
    {L : Type*} [CommRing L] (θ₀ : ↥(chartAlgFin p (ΓM M H) hj) →+* L)
    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ₀ (w (ι b)) = θ₀ (ι b) ^ p)
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (h1 : ∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom z))
    (hI0 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
        (RingHom.ker θ₀) ≤ RingHom.ker (σ 0).toRingHom)
    (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) :
    σ 1 ((1 : κ) ⊗ₜ[ℤp] ι b) = ((1 : κ) ⊗ₜ[ℤp] b) ^ p := by
  have hu : (1 : κ) ⊗ₜ[ℤp] (w (ι b) - (ι b) ^ p) ∈ RingHom.ker (σ 0).toRingHom :=
    hI0 (Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, map_sub, map_pow, hfrob b, sub_self]))
  have hu' : σ 0 ((1 : κ) ⊗ₜ[ℤp] w (ι b)) = σ 0 ((1 : κ) ⊗ₜ[ℤp] ((ι b) ^ p)) := by
    rw [← sub_eq_zero, ← map_sub, ← TensorProduct.tmul_sub]
    exact hu
  calc σ 1 ((1 : κ) ⊗ₜ[ℤp] ι b)
      = σ 0 ((1 : κ) ⊗ₜ[ℤp] w (ι b)) := by
        rw [h1, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_apply]
    _ = σ 0 ((1 : κ) ⊗ₜ[ℤp] ((ι b) ^ p)) := hu'
    _ = σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι (((1 : κ) ⊗ₜ[ℤp] b) ^ p)) := by
        rw [map_pow (Algebra.TensorProduct.map (AlgHom.id κ κ) ι), Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.tmul_pow, one_pow]
    _ = ((1 : κ) ⊗ₜ[ℤp] b) ^ p := h0 _

theorem one_tmul_j_eq_pow_of_case_one
    (ι : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[ℤp] ↥(chartAlgFin p (ΓM M H) hj)) (hιj : ι (jChartFin p (ΓN p M H hpM) hj) = jChartFin p (ΓM M H) hj)
    (w : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
    {L : Type*} [CommRing L] (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* L))
    (hθ1 : ∀ c, θ 1 c = θ 0 (w c))
    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (w (ι b)) = θ 0 (ι b) ^ p)
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (hI1 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
        (RingHom.ker (θ 1)) ≤ RingHom.ker (σ 0).toRingHom) :
    (1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj = (σ 0 ((1 : κ) ⊗ₜ[ℤp] w.symm (jChartFin p (ΓM M H) hj))) ^ p := by
  have hv : (1 : κ) ⊗ₜ[ℤp] (jChartFin p (ΓM M H) hj - (w.symm (jChartFin p (ΓM M H) hj)) ^ p) ∈
      RingHom.ker (σ 0).toRingHom := by
    refine hI1 (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, hθ1, map_sub, map_pow, AlgEquiv.apply_symm_apply, ← hιj, map_sub, map_pow, hfrob, sub_self]
  have h : σ 0 ((1 : κ) ⊗ₜ[ℤp] (jChartFin p (ΓM M H) hj - (w.symm (jChartFin p (ΓM M H) hj)) ^ p)) = 0 :=
    RingHom.mem_ker.mp hv
  rw [TensorProduct.tmul_sub, map_sub, sub_eq_zero] at h
  have hl : σ 0 ((1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓM M H) hj) = (1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj := by
    rw [← hιj, ← h0 ((1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj), Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [← hl, h, ← map_pow (σ 0), Algebra.TensorProduct.tmul_pow, one_pow]

theorem case_one_false
    (ι : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (K : Type) [Field K] [Algebra κ K] (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries K))
    (hθ1 : ∀ c, θ 1 c = θ 0 (w c))
    (hθj : θ 0 (jChartFin p (ΓM M H) hj) = jqModC K)
    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (w (ι b)) = θ 0 (ι b) ^ p)
    (hI1 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
        (RingHom.ker (θ 1)) ≤ RingHom.ker (σ 0).toRingHom) : False := by

  have hj1 : (((ι (jChartFin p (ΓN p M H hpM) hj) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) :
      LaurentSeries ℚ) = jqModC ℚ := by rw [hι]; rfl
  have hj2 : (((jChartFin p (ΓM M H) hj : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) :
      LaurentSeries ℚ) = jqModC ℚ := rfl
  have hιj : ι (jChartFin p (ΓN p M H hpM) hj) = jChartFin p (ΓM M H) hj := Subtype.ext (Subtype.ext (hj1.trans hj2.symm))
  have hs := one_tmul_j_eq_pow_of_case_one M H hpM hj κ ι hιj w θ hθ1 hfrob σ h0 hI1
  refine false_of_one_tmul_j_eq_pow M H hpM hj κ K ((θ 0).comp ι.toRingHom) ?_ _ hs
  show θ 0 (ι (jChartFin p (ΓN p M H hpM) hj)) = jqModC K
  rw [hιj, hθj]

theorem isDomain_tensor_chartAlgFin_place (hpM2 : ¬ p ^ 2 ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : ℤp →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap ℤp (AlgebraicClosure ℚ)) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    IsDomain ((IsLocalRing.ResidueField ↥A) ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := by
  letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra

  haveI : NeZero (M / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩
  have hpM' : ¬ p ∣ M / p := fun h => hpM2 (by
    rw [pow_two, ← Nat.mul_div_cancel' hpM]; exact Nat.mul_dvd_mul_left p h)
  have hΓ₀ : ΓN p M H hpM ≤ CongruenceSubgroup.Gamma0 (M / p) := CohCarrier.GammaH_le_Gamma0 _
  have hΓ₁ : CongruenceSubgroup.Gamma1 (M / p) ≤ ΓN p M H hpM := by
    intro γ hγ
    obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem (M / p) γ).mp hγ
    refine CohCarrier.mem_GammaH_iff.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
    have h1 : CohCarrier.gamma0Units (M / p) ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr h10⟩ = 1 :=
      Units.ext (by rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11)
    rw [h1]
    exact Subgroup.one_mem _

  have hT : ModularGroup.T ∈ ΓN p M H hpM := hΓ₁ (by
    rw [CongruenceSubgroup.Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T])
  haveI : (ΓN p M H hpM).FiniteIndex := by
    haveI : (CongruenceSubgroup.Gamma1 (M / p)).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma1 (M / p)
    exact Subgroup.finiteIndex_of_le hΓ₁
  obtain ⟨x, hx, -, -⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) hT
  obtain ⟨⟨eFin, -, -⟩, -⟩ :=
    ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
      (M / p) (ΓN p M H hpM) hΓ₁ hΓ₀ p hpM' (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj) A hA ρ hρ x hx
  exact eFin.toRingEquiv.injective.isDomain eFin.toRingEquiv.toRingHom

end Main
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel.KerMinH"

end NoSecH
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel.KerMinH"

namespace NoSecGeo

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
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel.KerMinH"

end NoSecGeo
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel.KerMinH"

namespace NoSecAlg

theorem finite_setOf_tmul_mem {R : Type} [CommRing R] (κ : Type) [Field κ] [Algebra R κ]
    (B : Type) [CommRing B] [Algebra R B] (u : B)
    (hfin : letI := (Polynomial.aeval u : Polynomial R →ₐ[R] B).toRingHom.toAlgebra; Module.Finite (Polynomial R) B) :
    {z : PrimeSpectrum (κ ⊗[R] B) | ((1 : κ) ⊗ₜ[R] u) ∈ z.asIdeal}.Finite := by
  classical
  letI algP : Algebra (Polynomial R) B := (Polynomial.aeval u : Polynomial R →ₐ[R] B).toRingHom.toAlgebra
  haveI : Module.Finite (Polynomial R) B := hfin
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Polynomial R) (M := B)
  let I : Ideal (κ ⊗[R] B) := Ideal.span {((1 : κ) ⊗ₜ[R] u)}
  let mk : κ ⊗[R] B →ₐ[κ] (κ ⊗[R] B) ⧸ I := Ideal.Quotient.mkₐ κ I
  let gen : B → (κ ⊗[R] B) ⧸ I := fun m => mk ((1 : κ) ⊗ₜ[R] m)

  have htmul_smul : ∀ (r : R) (m : B), ((1 : κ) ⊗ₜ[R] (algebraMap R B r * m)) = (algebraMap R κ r) • ((1 : κ) ⊗ₜ[R] m) := by
    intro r m
    rw [algebraMap_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def]
  have hspan : ∀ m : B, gen m ∈ Submodule.span κ (gen '' (s : Set B)) := by
    intro m
    have hm : m ∈ Submodule.span (Polynomial R) (s : Set B) := by rw [hs]; exact Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => exact Submodule.subset_span ⟨m, hm, rfl⟩
    | zero => simp only [gen, TensorProduct.tmul_zero, map_zero]; exact zero_mem _
    | add m m' _ _ h h' => simp only [gen, TensorProduct.tmul_add, map_add]; exact add_mem h h'
    | smul P m _ h =>
      have hsm : P • m = (Polynomial.aeval u P) * m := rfl
      have hX : Polynomial.X ∣ P - Polynomial.C (P.coeff 0) := by rw [Polynomial.X_dvd_iff]; simp
      obtain ⟨P₁, hP₁⟩ := hX
      have hP : P = Polynomial.C (P.coeff 0) + Polynomial.X * P₁ := by rw [← hP₁]; ring
      have hdecomp : Polynomial.aeval u P = algebraMap R B (P.coeff 0) + u * Polynomial.aeval u P₁ := by
        conv_lhs => rw [hP]
        rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      have hzero : mk ((1 : κ) ⊗ₜ[R] (u * (Polynomial.aeval u P₁ * m))) = 0 := by
        rw [show (1 : κ) ⊗ₜ[R] (u * (Polynomial.aeval u P₁ * m)) =
          ((1 : κ) ⊗ₜ[R] u) * ((1 : κ) ⊗ₜ[R] (Polynomial.aeval u P₁ * m)) by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
        rw [map_mul]
        have : mk ((1 : κ) ⊗ₜ[R] u) = 0 := by
          show Ideal.Quotient.mk I ((1 : κ) ⊗ₜ[R] u) = 0
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
        rw [this]; exact zero_mul (mk ((1 : κ) ⊗ₜ[R] (Polynomial.aeval u P₁ * m)))
      have hgen : gen (P • m) = (algebraMap R κ (P.coeff 0)) • gen m := by
        simp only [gen]
        rw [hsm, hdecomp, add_mul, mul_assoc, TensorProduct.tmul_add, map_add, hzero, add_zero, htmul_smul, map_smul]
      rw [hgen]
      exact Submodule.smul_mem _ _ h

  have htop : Submodule.span κ (gen '' (s : Set B)) = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
    change mk z ∈ _
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a m =>
      rw [show a ⊗ₜ[R] m = a • ((1 : κ) ⊗ₜ[R] m) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      exact Submodule.smul_mem _ _ (hspan m)
    | add z₁ z₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  haveI : Module.Finite κ ((κ ⊗[R] B) ⧸ I) :=
    ⟨⟨(s.image gen), by rw [Finset.coe_image]; exact htop⟩⟩
  haveI hart : IsArtinianRing ((κ ⊗[R] B) ⧸ I) := IsArtinianRing.of_finite κ _
  haveI : Finite {J : Ideal ((κ ⊗[R] B) ⧸ I) // J.IsPrime} := (IsArtinianRing.setOf_isPrime_finite ((κ ⊗[R] B) ⧸ I)).to_subtype

  let g : {z : PrimeSpectrum (κ ⊗[R] B) | ((1 : κ) ⊗ₜ[R] u) ∈ z.asIdeal} → {J : Ideal ((κ ⊗[R] B) ⧸ I) // J.IsPrime} := fun z =>
    ⟨Ideal.map (Ideal.Quotient.mk I) z.1.asIdeal,
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]; exact (Ideal.span_singleton_le_iff_mem _).mpr z.2)⟩
  have hg : Function.Injective g := by
    intro z₁ z₂ h
    have h' := congrArg (fun q : {J : Ideal ((κ ⊗[R] B) ⧸ I) // J.IsPrime} => Ideal.comap (Ideal.Quotient.mk I) q.1) h
    simp only [g] at h'
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at h'
    have e₁ : Ideal.comap (Ideal.Quotient.mk I) ⊥ ≤ z₁.1.asIdeal := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]; exact (Ideal.span_singleton_le_iff_mem _).mpr z₁.2
    have e₂ : Ideal.comap (Ideal.Quotient.mk I) ⊥ ≤ z₂.1.asIdeal := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]; exact (Ideal.span_singleton_le_iff_mem _).mpr z₂.2
    rw [sup_eq_left.mpr e₁, sup_eq_left.mpr e₂] at h'
    exact Subtype.ext (PrimeSpectrum.ext h')
  haveI : Finite {z : PrimeSpectrum (κ ⊗[R] B) | ((1 : κ) ⊗ₜ[R] u) ∈ z.asIdeal} := Finite.of_injective g hg
  exact Set.toFinite _

theorem pow_ne_jqModC (κ : Type) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] (y : LaurentSeries κ) :
    y ^ p ≠ jqModC κ := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries κ => z.coeff (-1)) h
  beta_reduce at h1
  rw [coeff_jqModC_neg_one, ModularCurve.pow_char_eq_coeffMap_frobenius_qExpand, coeffMap_coeff,
    ModularCurve.qExpand_coeff_of_not_dvd p y (k := -1) (by
      intro hd
      have h2 : ((p : ℤ)) ∣ 1 := (Int.dvd_neg).mp hd
      have h3 := Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h2
      have h4 : (p : ℤ) ≠ 1 := by exact_mod_cast (Fact.out : p.Prime).one_lt.ne'
      exact h4 h3), map_zero] at h1
  exact zero_ne_one h1

end NoSecAlg
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel.KerMinH"

namespace NoSecGeoStep

universe u

theorem exists_ringHom_comp_eq_algebraMap {Y : Scheme.{u}} {S : Type u} [CommRing S]
    (c₀ : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion c₀]
    (f β : Y ⟶ Y) (Φ : S →+* S) (hcf : c₀ ≫ f = Spec.map (CommRingCat.ofHom Φ) ≫ c₀) (hβ : β ≫ f = 𝟙 Y)
    (z₀ : ↥(Spec (CommRingCat.of S))) (hz₀ : β.base (c₀.base z₀) ∈ Set.range c₀.base) :
    ∃ (s : S) (ψ : S →+* Localization.Away s), s ∉ z₀.asIdeal ∧ ψ.comp Φ = algebraMap S (Localization.Away s) := by
  classical

  set W : Set ↥(Spec (CommRingCat.of S)) := (c₀ ≫ β).base ⁻¹' Set.range c₀.base with hW
  have hWopen : IsOpen W := (c₀.isOpenEmbedding.isOpen_range).preimage (c₀ ≫ β).base.hom.continuous
  have hz₀W : z₀ ∈ W := by rw [hW, Set.mem_preimage, Scheme.Hom.comp_apply]; exact hz₀
  obtain ⟨_, ⟨s, rfl⟩, hsz, hsW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz₀W hWopen
  have hs : s ∉ z₀.asIdeal := (PrimeSpectrum.mem_basicOpen _ _).mp hsz
  refine ⟨s, ?_⟩

  let L := Localization.Away s
  let h : Spec (CommRingCat.of L) ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap S L)) ≫ c₀
  have hrange : Set.range (h ≫ β).base ⊆ Set.range c₀.base := by
    rintro _ ⟨t, rfl⟩
    have ht : PrimeSpectrum.comap (algebraMap S L) t ∈ PrimeSpectrum.basicOpen s := by
      rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range L s]
      exact ⟨t, rfl⟩
    have ht' : (Spec.map (CommRingCat.ofHom (algebraMap S L))).base t ∈ W := by
      apply hsW
      rw [Spec.map_apply, CommRingCat.hom_ofHom]
      exact ht
    rw [hW, Set.mem_preimage] at ht'
    rw [Scheme.Hom.comp_apply, show h.base t = c₀.base ((Spec.map (CommRingCat.ofHom (algebraMap S L))).base t) from
      Scheme.Hom.comp_apply _ _ t]
    rw [Scheme.Hom.comp_apply] at ht'
    exact ht'
  let g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of S) := IsOpenImmersion.lift c₀ (h ≫ β) hrange
  have hg : g ≫ c₀ = h ≫ β := IsOpenImmersion.lift_fac _ _ _
  let ψ' : CommRingCat.of S ⟶ CommRingCat.of L := Spec.preimage g
  have hψ' : Spec.map ψ' = g := Spec.map_preimage g
  refine ⟨ψ'.hom, hs, ?_⟩

  have e : Spec.map (CommRingCat.ofHom (algebraMap S L)) ≫ c₀ = Spec.map (CommRingCat.ofHom Φ ≫ ψ') ≫ c₀ := by
    calc Spec.map (CommRingCat.ofHom (algebraMap S L)) ≫ c₀ = h := rfl
      _ = h ≫ β ≫ f := by rw [hβ, Category.comp_id]
      _ = g ≫ c₀ ≫ f := by rw [← Category.assoc, ← hg, Category.assoc]
      _ = g ≫ Spec.map (CommRingCat.ofHom Φ) ≫ c₀ := by rw [hcf]
      _ = Spec.map (CommRingCat.ofHom Φ ≫ ψ') ≫ c₀ := by rw [Spec.map_comp, Category.assoc, hψ']
  have e' := Spec.map_injective ((cancel_mono c₀).mp e)
  have e'' := congrArg CommRingCat.Hom.hom e'
  rw [CommRingCat.hom_ofHom, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e''
  exact e''.symm

end NoSecGeoStep
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel.KerMinH"

open NoSecH NoSecGeo AlgebraicCurve.TwoChartIntegralModel in
set_option maxHeartbeats 12800000 in
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
    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_pi : comp 0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _)
    (comp_w : comp 0 ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) = comp 1) :
    ∀ β : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
      β ≫ comp 1 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) ≠ 𝟙 _ := by
  classical
  letI instκ : Algebra (R p) (IsLocalRing.ResidueField ↥A) := (((IsLocalRing.residue ↥A).comp ρ)).toAlgebra
  intro β hβ

  have hcompat_c₀ : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj) ≫ toBase p (ΓN p M H hpM) hj =
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
  have hc₀fst : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj :=
    pullback.lift_fst _ _ _
  have hc₀snd : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p)
      (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))) := pullback.lift_snd _ _ _

  have hcompat_c₀' : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj) ≫ toBase p (ΓN p M H hpM) hj =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj)))) ≫
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (((IsLocalRing.residue ↥A).comp ρ) r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    rfl
  let c₀' : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) ⟶ fibre (Γ := (ΓN p M H hpM)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) := pullback.lift _ _ hcompat_c₀'
  have hc₀'fst : c₀' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj :=
    pullback.lift_fst _ _ _
  have hc₀'snd : c₀' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p)
      (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj)))) := pullback.lift_snd _ _ _

  have hcompat_c : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj) ≫ toBase p (ΓM M H) hj =
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
  have hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj :=
    pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p)
      (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgFin p (ΓM M H) hj)))) := pullback.lift_snd _ _ _
  have Hc₀ := isPullback_chartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) (IsLocalRing.ResidueField ↥A) c₀ hc₀fst hc₀snd
  have Hc₀' := isPullback_chartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) (IsLocalRing.ResidueField ↥A) c₀' hc₀'fst hc₀'snd
  have Hc := isPullback_chartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) (IsLocalRing.ResidueField ↥A) c hcfst hcsnd
  have hc₀range := range_eq_preimage_of_isPullback Hc₀
  have hc₀'range := range_eq_preimage_of_isPullback Hc₀'
  haveI : IsOpenImmersion c₀ := by rw [(Hc₀.isoPullback_hom_fst).symm]; infer_instance
  haveI : IsOpenImmersion c₀' := by rw [(Hc₀'.isoPullback_hom_fst).symm]; infer_instance
  haveI : IsOpenImmersion c := by rw [(Hc.isoPullback_hom_fst).symm]; infer_instance

  have hwchart' : ιFin p (ΓM M H) hj ≫ (overOfIso w hw).1 = Spec.map (CommRingCat.ofHom theta.toAlgHom.toRingHom) ≫ ιFin p (ΓM M H) hj :=
    hwchart
  have hcw : c ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom) ≫ c :=
    ModularCurve.XHDRLevel.chart_comp_fibreMap_eq_specMap_tensor_comp_chart p hj (overOfIso w hw) theta.toAlgHom hwchart'
      (IsLocalRing.ResidueField ↥A) c hcfst hcsnd c hcfst hcsnd
  have hcπ : c ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) iota0).toRingHom) ≫ c₀ :=
    ModularCurve.XHDRLevel.chart_comp_fibreMap_eq_specMap_tensor_comp_chart p hj π iota0 pi_chart
      (IsLocalRing.ResidueField ↥A) c hcfst hcsnd c₀ hc₀fst hc₀snd
  obtain ⟨σ₀, h0, hsq₀, hii⟩ := ModularCurve.XHDRLevel.exists_retraction_chart_comp_zero_eq p M H hpM hpM2 hj π iota0 iota0_spec
    pi_chart (IsLocalRing.ResidueField ↥A) c₀ hc₀fst hc₀snd c hcfst hcsnd comp comp_over comp_isClosedImmersion comp_pi
  let Tθ : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) :=
    Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom
  have hsq₁ : c₀ ≫ comp 1 = Spec.map (CommRingCat.ofHom (σ₀.comp Tθ).toRingHom) ≫ c := hii w hw theta hcw comp_w
  let σ : Fin 2 → ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := ![σ₀, σ₀.comp Tθ]
  have hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), σ 1 ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] iota0 b) = ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) ^ p :=
    ModularCurve.XHDRLevel.retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime p M H hpM hpM2 hHp hj
      iota0 iota0_spec theta htheta A hA ρ hρ σ h0 (fun _ => rfl)

  let mapι : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[IsLocalRing.ResidueField ↥A] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) :=
    Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) iota0
  let Φ : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[IsLocalRing.ResidueField ↥A] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) := (σ₀.comp Tθ).comp mapι
  have hΦ : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), Φ ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) = ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) ^ p := by
    intro b
    show σ 1 (mapι ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b)) = _
    rw [show mapι ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) = (1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] iota0 b from by
      simp [mapι, Algebra.TensorProduct.map_tmul]]
    exact hfrob b
  set f := comp 1 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) with hf
  have hcf : c₀ ≫ f = Spec.map (CommRingCat.ofHom Φ.toRingHom) ≫ c₀ := by
    rw [hf, ← Category.assoc, hsq₁, Category.assoc, hcπ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  haveI : NeZero (M / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩
  have hpM' : ¬ p ∣ M / p := fun h => hpM2 (by
    rw [pow_two, ← Nat.mul_div_cancel' hpM]; exact Nat.mul_dvd_mul_left p h)
  have hΓ₀ : ΓN p M H hpM ≤ CongruenceSubgroup.Gamma0 (M / p) := CohCarrier.GammaH_le_Gamma0 _
  have hΓ₁ : CongruenceSubgroup.Gamma1 (M / p) ≤ ΓN p M H hpM := by
    intro γ hγ
    obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem (M / p) γ).mp hγ
    refine CohCarrier.mem_GammaH_iff.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
    have h1 : CohCarrier.gamma0Units (M / p) ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr h10⟩ = 1 :=
      Units.ext (by rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11)
    rw [h1]
    exact Subgroup.one_mem _
  have hT : ModularGroup.T ∈ ΓN p M H hpM := hΓ₁ (by
    rw [CongruenceSubgroup.Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T])
  haveI : (ΓN p M H hpM).FiniteIndex := by
    haveI : (CongruenceSubgroup.Gamma1 (M / p)).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma1 (M / p)
    exact Subgroup.finiteIndex_of_le hΓ₁
  obtain ⟨x, hx, htx, -⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) hT
  obtain ⟨⟨eFin, hjF, -⟩, -⟩ :=
    ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing (M / p)
      (ΓN p M H hpM) hΓ₁ hΓ₀ p hpM' (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj) A hA ρ hρ x hx
  haveI hdom : IsDomain ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := MulEquiv.isDomain _ eFin.toMulEquiv

  let Ψ : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →+* LaurentSeries (IsLocalRing.ResidueField ↥A) :=
    ((qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)).toSubalgebra.val.toRingHom.comp (CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))).val.toRingHom).comp eFin.toAlgHom.toRingHom
  have hΨ : ∀ z, Ψ z = (((eFin z : ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) := fun z => rfl
  have hΨinj : Function.Injective Ψ := by
    intro a b h
    rw [hΨ, hΨ] at h
    exact eFin.injective (Subtype.ext (Subtype.ext h))
  have hΨj : Ψ ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj) = jqModC (IsLocalRing.ResidueField ↥A) := by
    rw [hΨ]
    have : ((eFin ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj) : ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) = x := hjF
    rw [this, hx]

  have hle : (Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ≤ (CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) := fun y hy =>
    (CurveModel.mem_chartRing_iff _).mpr (isIntegral_algebraMap (R := ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))) (A := ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) (x := ⟨y, hy⟩))
  letI algAC : Algebra ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  haveI towerAC : IsScalarTower ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hintAC : Algebra.IsIntegral ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) := by
    refine ⟨fun y => ?_⟩
    have hy : IsIntegral ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ((y : ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) := (CurveModel.mem_chartRing_iff _).mp y.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) Subtype.val_injective).mp hy
  let iso : Polynomial (IsLocalRing.ResidueField ↥A) ≃ₐ[IsLocalRing.ResidueField ↥A] ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) :=
    (AlgEquiv.ofInjective (Polynomial.aeval x) ((transcendental_iff_injective).mp htx)).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval (IsLocalRing.ResidueField ↥A) x).symm)
  let ev : IsLocalRing.ResidueField ↥A → (↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) →ₐ[IsLocalRing.ResidueField ↥A] IsLocalRing.ResidueField ↥A) := fun a => (Polynomial.aeval a).comp iso.symm.toAlgHom
  have hev_surj : ∀ a, Function.Surjective (ev a) := fun a c => ⟨algebraMap _ _ c, by simp [ev]⟩
  let 𝔪 : IsLocalRing.ResidueField ↥A → Ideal ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) := fun a => RingHom.ker (ev a).toRingHom
  haveI h𝔪max : ∀ a, (𝔪 a).IsMaximal := fun a => RingHom.ker_isMaximal_of_surjective _ (hev_surj a)
  have hx𝔪 : ∀ a, (iso Polynomial.X - algebraMap _ _ a : ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))) ∈ 𝔪 a := by
    intro a
    rw [RingHom.mem_ker]
    show (Polynomial.aeval a) (iso.symm (iso Polynomial.X - algebraMap (IsLocalRing.ResidueField ↥A) ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) a)) = 0
    rw [map_sub, AlgEquiv.symm_apply_apply, AlgEquiv.commutes, map_sub, Polynomial.aeval_X, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hover : ∀ a : IsLocalRing.ResidueField ↥A, ∃ Q : Ideal ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))), Q.IsMaximal ∧ Q.comap (algebraMap ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))) = 𝔪 a := by
    intro a
    refine Ideal.exists_ideal_over_maximal_of_isIntegral (𝔪 a) ?_
    have : RingHom.ker (algebraMap ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ↥(CurveModel.chartRing (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp (Subalgebra.inclusion_injective hle)
    rw [this]; exact bot_le
  choose 𝔐 h𝔐max h𝔐comap using hover
  have h𝔪inj : Function.Injective 𝔪 := by
    intro a b hab
    by_contra hne
    have h1 : (iso Polynomial.X - algebraMap _ _ a : ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))) ∈ 𝔪 b := hab ▸ hx𝔪 a
    have h2 := hx𝔪 b
    have h3 : (algebraMap (IsLocalRing.ResidueField ↥A) ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) (b - a)) ∈ 𝔪 b := by
      have := sub_mem h1 h2
      rwa [sub_sub_sub_cancel_left, ← map_sub] at this
    have hu : IsUnit (algebraMap (IsLocalRing.ResidueField ↥A) ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) (b - a)) :=
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))).map _
    exact (h𝔪max b).ne_top (Ideal.eq_top_of_isUnit_mem _ h3 hu)
  have h𝔐inj : Function.Injective 𝔐 := fun a b h => h𝔪inj (by rw [← h𝔐comap a, ← h𝔐comap b, h])
  let Ppt : IsLocalRing.ResidueField ↥A → ↥(Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)))) := fun a =>
    ⟨Ideal.comap eFin.toAlgHom.toRingHom (𝔐 a), Ideal.IsPrime.comap _⟩
  have hPinj : Function.Injective Ppt := by
    intro a b h
    apply h𝔐inj
    have h' : Ideal.comap eFin.toAlgHom.toRingHom (𝔐 a) = Ideal.comap eFin.toAlgHom.toRingHom (𝔐 b) :=
      congrArg PrimeSpectrum.asIdeal h
    exact Ideal.comap_injective_of_surjective _ eFin.surjective h'
  have hUinf : (Set.range c₀.base).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun a => c₀.base (Ppt a))
      (c₀.isOpenEmbedding.injective.comp hPinj) (fun a => ⟨_, rfl⟩)

  have hcov : ∀ y : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), y ∈ Set.range c₀.base ∨ y ∈ Set.range c₀'.base := by
    intro y
    rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)
      ((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y) with h | h
    · left; rw [hc₀range]; exact h
    · right; rw [hc₀'range]; exact h
  have hFsub : (Set.range c₀.base)ᶜ ⊆ c₀'.base '' {z | ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))) ∈ z.asIdeal} := by
    intro y hy
    rcases hcov y with h | ⟨z, rfl⟩
    · exact absurd h hy
    refine ⟨z, ?_, rfl⟩
    by_contra hz
    apply hy
    rw [hc₀range, Set.mem_preimage]
    change (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base (c₀'.base z) ∈ _
    rw [← Scheme.Hom.comp_apply, hc₀'fst, Scheme.Hom.comp_apply]
    refine (ιInf_mem_range_ιFin_iff (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) _).mpr ?_
    rw [Spec.map_apply, CommRingCat.hom_ofHom, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    exact hz
  have hVfin : {z : ↥(Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj)))) | ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))) ∈ z.asIdeal}.Finite := by
    haveI := ModularCurve.XHDRLevel.KerMinH.instDVR_R p
    have htjN := ModularCurve.XHDRLevel.KerMinH.transcendental_jAt p (ΓN p M H hpM) hj
    have hFDN := ModularCurve.XHDRLevel.KerMinH.finiteDimensional_adjoin_jAt (ΓN p M H hpM) hT hj
    have hsepN := ModularCurve.XHDRLevel.KerMinH.isSeparable_adjoin_jAt (ΓN p M H hpM) hT hj
    obtain ⟨-, hfinI⟩ := AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))
      (jAt (ΓN p M H hpM) hj) htjN hFDN hsepN
    exact NoSecAlg.finite_setOf_tmul_mem (IsLocalRing.ResidueField ↥A) ↥(chartAlgInf p (ΓN p M H hpM) hj) (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) hfinI
  have hFfin : (Set.range c₀.base)ᶜ.Finite := (hVfin.image _).subset hFsub

  have hβinj : Function.Injective β.base := by
    intro a b h
    have := congrArg f.base h
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hβ] at this
    simpa using this
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ↥(Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)))), β.base (c₀.base z₀) ∈ Set.range c₀.base := by
    by_contra hcon
    push Not at hcon
    have hsub : β.base '' (Set.range c₀.base) ⊆ (Set.range c₀.base)ᶜ := by
      rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩; exact hcon z
    exact hUinf ((hFfin.subset hsub).of_finite_image hβinj.injOn)

  obtain ⟨s, ψ, hs, hψ⟩ := NoSecGeoStep.exists_ringHom_comp_eq_algebraMap c₀ f β Φ.toRingHom hcf hβ z₀ hz₀
  have hΨs : IsUnit (Ψ s) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hs
    have : s = 0 := hΨinj (by rw [h0, map_zero])
    rw [this]; exact Ideal.zero_mem _
  let ΨL : Localization.Away s →+* LaurentSeries (IsLocalRing.ResidueField ↥A) := IsLocalization.Away.lift s hΨs
  have hΨL : ∀ a, ΨL (algebraMap _ (Localization.Away s) a) = Ψ a := fun a => IsLocalization.Away.lift_eq s hΨs a
  have key : algebraMap _ (Localization.Away s) ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj) = (ψ ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj)) ^ p := by
    rw [← hψ, RingHom.comp_apply, show Φ.toRingHom ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj) = Φ ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj) from rfl,
      hΦ, map_pow]
  have key' := congrArg ΨL key
  rw [hΨL, hΨj, map_pow] at key'
  exact NoSecAlg.pow_ne_jqModC (IsLocalRing.ResidueField ↥A) p _ key'.symm

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime.ModularCurve.XHDRLevel.KerMinH"

end S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime (solution)
