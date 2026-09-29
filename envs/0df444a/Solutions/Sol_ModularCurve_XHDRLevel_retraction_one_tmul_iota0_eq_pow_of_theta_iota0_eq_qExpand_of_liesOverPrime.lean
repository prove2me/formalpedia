-- Prove2me | solution 1 for ModularCurve.XHDRLevel.retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1d7f8143-28aa-51d1-8157-490a7bfc44fb

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

namespace XHFrobRing

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

theorem main (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ι : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[ℤp] ↥(chartAlgFin p (ΓM M H) hj))
    (hw : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((w (ι b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : ℤp →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap ℤp (AlgebraicClosure ℚ)) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (σ : Fin 2 → ((IsLocalRing.ResidueField ↥A) ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A] (IsLocalRing.ResidueField ↥A) ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj)))
      (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) ι z) = z)
      (h1 : ∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) w.toAlgHom z))
      (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)),
      σ 1 ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[ℤp] ι b) = ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[ℤp] b) ^ p := by
  letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  intro σ h0 h1 b
  haveI : IsDomain ((IsLocalRing.ResidueField ↥A) ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := isDomain_tensor_chartAlgFin_place M H hpM hj hpM2 A hA ρ hρ
  obtain ⟨θ, σ₀, hθ1, hread, -, hmin, hfrob, -⟩ :=
    ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH
      p M H hpM hpM2 hHp hj ι hι w hw A hA ρ hρ

  have hθj : θ 0 (jChartFin p (ΓM M H) hj) = jqModC (IsLocalRing.ResidueField ↥A) := by
    rw [hread (jChartFin p (ΓM M H) hj) (jqModC ↥A)]
    · exact map_jqModC _
    · rw [coeffMap_jqModC]
      change jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)
      rw [coe_jAt]
      exact (map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm
  haveI hP : (RingHom.ker (σ 0).toRingHom).IsPrime := RingHom.ker_isPrime _
  rcases hP.mul_le.mp (map_ker_mul_map_ker_le M H hj (IsLocalRing.ResidueField ↥A) θ hmin (RingHom.ker (σ 0).toRingHom)) with hI0 | hI1
  · exact case_zero M H hpM hj (IsLocalRing.ResidueField ↥A) ι w (θ 0) hfrob σ h0 h1 hI0 b
  · exact (case_one_false M H hpM hj (IsLocalRing.ResidueField ↥A) ι hι w σ h0 (IsLocalRing.ResidueField ↥A) θ hθ1 hθj hfrob hI1).elim

end Main

end XHFrobRing

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra

    ∀ (σ : Fin 2 → ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A]
        (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)))
      (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map
        (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) iota0 z) = z)
      (h1 : ∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map
        (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom z)),
    ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      σ 1 ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] iota0 b) = ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) ^ p := by
  intro σ h0 h1 b
  exact XHFrobRing.main M H hpM hj hpM2 hHp iota0 iota0_spec theta htheta A hA ρ hρ σ h0 h1 b

end

end S_ModularCurve_XHDRLevel_retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime (solution)
