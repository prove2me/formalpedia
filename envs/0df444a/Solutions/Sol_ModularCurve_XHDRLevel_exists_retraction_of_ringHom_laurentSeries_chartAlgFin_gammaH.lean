-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_retraction_of_ringHom_laurentSeries_chartAlgFin_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/85429bf9-4580-56d5-9c5d-135742d0706f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_retraction_of_ringHom_laurentSeries_chartAlgFin_gammaH
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel IsLocalRing Polynomial AlgebraicGeometry.Polynomial"

open scoped MatrixGroups TensorProduct

namespace XHSigma

variable {p : ℕ} [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

theorem ringHom_ext_zp {P : Type*} [Semiring P] (f g : ℤp →+* P) : f = g := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  haveI : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

theorem coeffMap_coeffMap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (y : LaurentSeries R) : coeffMap g (coeffMap f y) = coeffMap (g.comp f) y := by
  ext n; rfl

theorem coeffEmb_coeffMap_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (R : Type*) [CommRing R] [Algebra R ℚ]
    [Algebra R L] [IsScalarTower R ℚ L] (y : LaurentSeries R) :
    coeffMap (algebraMap R L) y = coeffEmb L (coeffMap (algebraMap R ℚ) y) := by
  ext n
  show algebraMap R L (y.coeff n) = algebraMap ℚ L (algebraMap R ℚ (y.coeff n))
  rw [← IsScalarTower.algebraMap_apply]

section Bivariate

variable (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev evJ : ℤp[X] →+* ↥(chartAlgFin p Γ hj) := (Polynomial.aeval (jChartFin p Γ hj)).toRingHom

theorem val_comp_evJ : (chartAlgFin p Γ hj).val.toRingHom.comp (evJ (p := p) Γ hj) =
    (Polynomial.aeval (jAt Γ hj) : ℤp[X] →ₐ[ℤp] ↥(qExpFunctionFieldC ℚ Γ)).toRingHom := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp
  · simp

theorem exists_bivariate (b : ↥(chartAlgFin p Γ hj)) :
    ∃ P : Polynomial (Polynomial ℤp), P.Monic ∧ P.eval₂ (evJ (p := p) Γ hj) b = 0 := by
  classical
  obtain ⟨P₁, hmonic, hroot⟩ := (TwoChartIntegralModel.mem_chartAlg_iff ℤp ↥(qExpFunctionFieldC ℚ Γ)).mp b.2

  have hlifts : P₁.map (algebraMap _ ↥(qExpFunctionFieldC ℚ Γ)) ∈
      Polynomial.lifts (Polynomial.aeval (jAt Γ hj) : ℤp[X] →ₐ[ℤp] ↥(qExpFunctionFieldC ℚ Γ)).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_map]
    have hk : ((P₁.coeff k : ↥(Algebra.adjoin ℤp ({(jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ))} :
        Set ↥(qExpFunctionFieldC ℚ Γ)))) : ↥(qExpFunctionFieldC ℚ Γ)) ∈
        (Polynomial.aeval (jAt Γ hj) : ℤp[X] →ₐ[ℤp] ↥(qExpFunctionFieldC ℚ Γ)).range :=
      (SetLike.ext_iff.mp (Algebra.adjoin_singleton_eq_range_aeval ℤp (jAt Γ hj)) _).mp (P₁.coeff k).2
    obtain ⟨Q, hQ⟩ := (AlgHom.mem_range _).mp hk
    exact ⟨Q, hQ⟩
  obtain ⟨P, hPmap, -, hPmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hmonic.map _)
  refine ⟨P, hPmonic, ?_⟩
  apply Subtype.val_injective
  have h1 := Polynomial.hom_eval₂ P (evJ (p := p) Γ hj) (chartAlgFin p Γ hj).val.toRingHom b
  rw [val_comp_evJ] at h1
  rw [show ((chartAlgFin p Γ hj).val.toRingHom (Polynomial.eval₂ (evJ (p := p) Γ hj) b P)) =
      ((Polynomial.eval₂ (evJ (p := p) Γ hj) b P : ↥(chartAlgFin p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) from rfl] at h1
  rw [h1, ← Polynomial.eval_map, hPmap, Polynomial.eval_map]
  exact hroot

end Bivariate

section Tensor

def tensorAddHom {Aκ OO L : Type*} [CommRing Aκ] [Algebra ℤp Aκ] [CommRing OO] [Algebra ℤp OO] [CommRing L]
    (F : Aκ →+* L) (G : OO →+* L) : Aκ ⊗[ℤp] OO →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun b => F x * G b) (fun b b' => by simp only [map_add, mul_add]))
      (fun x x' => by ext b; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]))
    (fun r x b => by
      have key := RingHom.congr_fun (ringHom_ext_zp (p := p) (F.comp (algebraMap ℤp Aκ)) (G.comp (algebraMap ℤp OO))) r
      simp only [RingHom.coe_comp, Function.comp_apply] at key
      show F (r • x) * G b = F x * G (r • b)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, key]
      ring)

theorem tensorAddHom_tmul {Aκ OO L : Type*} [CommRing Aκ] [Algebra ℤp Aκ] [CommRing OO] [Algebra ℤp OO] [CommRing L]
    (F : Aκ →+* L) (G : OO →+* L) (x : Aκ) (b : OO) :
    tensorAddHom (p := p) F G (x ⊗ₜ[ℤp] b) = F x * G b := by
  unfold tensorAddHom
  rw [TensorProduct.liftAddHom_tmul]
  rfl

def tensorRingHom {Aκ OO L : Type*} [CommRing Aκ] [Algebra ℤp Aκ] [CommRing OO] [Algebra ℤp OO] [CommRing L]
    (F : Aκ →+* L) (G : OO →+* L) : Aκ ⊗[ℤp] OO →+* L :=
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

theorem tensorRingHom_tmul {Aκ OO L : Type*} [CommRing Aκ] [Algebra ℤp Aκ] [CommRing OO] [Algebra ℤp OO] [CommRing L]
    (F : Aκ →+* L) (G : OO →+* L) (x : Aκ) (b : OO) :
    tensorRingHom (p := p) F G (x ⊗ₜ[ℤp] b) = F x * G b :=
  tensorAddHom_tmul (p := p) F G x b

end Tensor

structure Ctx where
  M : ℕ
  [hM : NeZero M]
  H : Subgroup (ZMod M)ˣ
  hpM : p ∣ M
  hpM2 : ¬ p ^ 2 ∣ M
  hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))
  iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[ℤp] ↥(chartAlgFin p (ΓM M H) hj)
  iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)
  A : ValuationSubring (AlgebraicClosure ℚ)
  hA : A.LiesOverPrime p
  [hchar : CharP (ResidueField ↥A) p]
  [hac : IsAlgClosed (ResidueField ↥A)]
  ρ : ℤp →+* ↥A
  hρ : A.subtype.comp ρ = algebraMap ℤp (AlgebraicClosure ℚ)
  θ₀ : ↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (ResidueField ↥A)
  hθ₀C : ∀ c : ℤp, θ₀ (algebraMap ℤp ↥(chartAlgFin p (ΓM M H) hj) c) = HahnSeries.C ((residue ↥A) (ρ c))
  hθ₀read : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ↥A),
      coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ)
        (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      θ₀ c = coeffMap (residue ↥A) y
  hθ₀range : ∀ c : ↥(chartAlgFin p (ΓM M H) hj), θ₀ c ∈ qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)

namespace Ctx

variable (C : Ctx (p := p))

attribute [scoped instance] Ctx.hM Ctx.hchar Ctx.hac

abbrev κ : Type := ResidueField ↥C.A
abbrev OM : Type := ↥(chartAlgFin p (ΓM C.M C.H) C.hj)
abbrev ON : Type := ↥(chartAlgFin p (ΓN p C.M C.H C.hpM) C.hj)

abbrev Fb : Type := ↥(qExpFunctionFieldC C.κ (ΓN p C.M C.H C.hpM))

scoped instance algκ : Algebra ℤp C.κ := ((residue ↥C.A).comp C.ρ).toAlgebra

theorem algebraMap_κ (c : ℤp) : algebraMap ℤp C.κ c = residue ↥C.A (C.ρ c) := rfl

scoped instance neZero_div : NeZero (C.M / p) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne C.M)) C.hpM) (Fact.out : p.Prime).pos).ne'⟩

theorem not_dvd_div : ¬ p ∣ C.M / p := fun h => C.hpM2 (by
  rw [pow_two, ← Nat.mul_div_cancel' C.hpM]; exact Nat.mul_dvd_mul_left p h)

theorem gamma0_ge : ΓN p C.M C.H C.hpM ≤ CongruenceSubgroup.Gamma0 (C.M / p) := CohCarrier.GammaH_le_Gamma0 _

theorem gamma1_le : CongruenceSubgroup.Gamma1 (C.M / p) ≤ ΓN p C.M C.H C.hpM := by
  intro γ hγ
  obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem (C.M / p) γ).mp hγ
  refine CohCarrier.mem_GammaH_iff.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
  have h1 : CohCarrier.gamma0Units (C.M / p) ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr h10⟩ = 1 :=
    Units.ext (by rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11)
  rw [h1]
  exact Subgroup.one_mem _

theorem T_mem : ModularGroup.T ∈ ΓN p C.M C.H C.hpM := C.gamma1_le (by
  rw [CongruenceSubgroup.Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T])

scoped instance finiteIndex : (ΓN p C.M C.H C.hpM).FiniteIndex := by
  haveI : (CongruenceSubgroup.Gamma1 (C.M / p)).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma1 (C.M / p)
  exact Subgroup.finiteIndex_of_le C.gamma1_le

theorem exists_x : ∃ x : C.Fb, (x : LaurentSeries C.κ) = jqModC C.κ ∧ Transcendental C.κ x := by
  obtain ⟨x, hx, htx, -⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed C.κ (ΓN p C.M C.H C.hpM) C.T_mem
  exact ⟨x, hx, htx⟩

def x : C.Fb := C.exists_x.choose
theorem coe_x : (C.x : LaurentSeries C.κ) = jqModC C.κ := C.exists_x.choose_spec.1
theorem transcendental_x : Transcendental C.κ C.x := C.exists_x.choose_spec.2

def θF : C.OM →+* C.Fb := C.θ₀.codRestrict (qExpFunctionFieldC C.κ (ΓN p C.M C.H C.hpM)) C.hθ₀range

theorem coe_θF (c : C.OM) : (C.θF c : LaurentSeries C.κ) = C.θ₀ c := rfl

theorem coe_algebraMap_Fb (y : C.κ) : ((algebraMap C.κ C.Fb y : C.Fb) : LaurentSeries C.κ) = HahnSeries.C y := by
  change algebraMap C.κ (LaurentSeries C.κ) y = _
  exact LaurentSeries.algebraMap_apply C.κ y

theorem θF_algebraMap (c : ℤp) : C.θF (algebraMap ℤp C.OM c) = algebraMap C.κ C.Fb (algebraMap ℤp C.κ c) := by
  apply Subtype.ext
  rw [coe_θF, C.hθ₀C, coe_algebraMap_Fb, algebraMap_κ]

theorem θF_j : C.θF (jChartFin p (ΓM C.M C.H) C.hj) = C.x := by
  apply Subtype.ext
  rw [coe_θF, coe_x, C.hθ₀read (jChartFin p (ΓM C.M C.H) C.hj) (jqModC ↥C.A)]
  · exact map_jqModC _
  · rw [coeffMap_jqModC]
    change jqModC (AlgebraicClosure ℚ) =
      coeffEmb (AlgebraicClosure ℚ) ((jAt (ΓM C.M C.H) C.hj : ↥(qExpFunctionFieldC ℚ (ΓM C.M C.H))) : LaurentSeries ℚ)
    rw [coe_jAt]
    exact (map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm

theorem isIntegral_adjoin_of_eval₂ {L : Type} [Field L] [Algebra C.κ L] (s t x : L)
    (ht : t ∈ Algebra.adjoin C.κ ({s} : Set L)) (P : Polynomial (Polynomial C.κ)) (hP : P.Monic)
    (h : P.eval₂ (Polynomial.aeval t : C.κ[X] →ₐ[C.κ] L).toRingHom x = 0) :
    IsIntegral (Algebra.adjoin C.κ ({s} : Set L)) x := by
  let θ : C.κ[X] →+* ↥(Algebra.adjoin C.κ ({s} : Set L)) :=
    (Polynomial.aeval (⟨t, ht⟩ : ↥(Algebra.adjoin C.κ ({s} : Set L)))).toRingHom
  refine ⟨P.map θ, hP.map θ, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap ↥(Algebra.adjoin C.κ ({s} : Set L)) L).comp θ =
      (Polynomial.aeval t : C.κ[X] →ₐ[C.κ] L).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · show ((Polynomial.aeval (⟨t, ht⟩ : ↥(Algebra.adjoin C.κ ({s} : Set L))) (Polynomial.C c) :
          ↥(Algebra.adjoin C.κ ({s} : Set L))) : L) = (Polynomial.aeval t : C.κ[X] →ₐ[C.κ] L) (Polynomial.C c)
      rw [Polynomial.aeval_C, Polynomial.aeval_C, Subalgebra.coe_algebraMap]
    · show ((Polynomial.aeval (⟨t, ht⟩ : ↥(Algebra.adjoin C.κ ({s} : Set L))) (Polynomial.X) :
          ↥(Algebra.adjoin C.κ ({s} : Set L))) : L) = (Polynomial.aeval t : C.κ[X] →ₐ[C.κ] L) Polynomial.X
      rw [Polynomial.aeval_X, Polynomial.aeval_X]
  rw [hcomp]
  exact h

theorem θF_comp_evJ :
    C.θF.comp (evJ (p := p) (ΓM C.M C.H) C.hj) =
      (Polynomial.aeval C.x : C.κ[X] →ₐ[C.κ] C.Fb).toRingHom.comp (Polynomial.mapRingHom (algebraMap ℤp C.κ)) := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.aeval_C]
    exact C.θF_algebraMap c
  · simp [θF_j]

theorem θF_mem_chartRing (b : C.OM) : C.θF b ∈ CurveModel.chartRing C.κ ({C.x} : Set C.Fb) := by
  rw [CurveModel.mem_chartRing_iff]
  obtain ⟨P, hPmonic, hProot⟩ := exists_bivariate (p := p) (ΓM C.M C.H) C.hj b
  refine C.isIntegral_adjoin_of_eval₂ C.x C.x (C.θF b) (Algebra.self_mem_adjoin_singleton _ _)
    (P.map (Polynomial.mapRingHom (algebraMap ℤp C.κ))) (hPmonic.map _) ?_
  rw [Polynomial.eval₂_map, ← θF_comp_evJ, ← Polynomial.hom_eval₂, hProot, map_zero]

def Φ : C.κ ⊗[ℤp] C.OM →ₐ[C.κ] C.Fb :=
  { tensorRingHom (p := p) (algebraMap C.κ C.Fb) C.θF with
    commutes' := fun r => by
      show tensorRingHom (p := p) (algebraMap C.κ C.Fb) C.θF (algebraMap C.κ (C.κ ⊗[ℤp] C.OM) r) = algebraMap C.κ C.Fb r
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, tensorRingHom_tmul, map_one,
        mul_one] }

theorem Φ_tmul (a : C.κ) (c : C.OM) : C.Φ (a ⊗ₜ[ℤp] c) = algebraMap C.κ C.Fb a * C.θF c :=
  tensorRingHom_tmul (p := p) _ _ a c

theorem Φ_mem_chartRing (z : C.κ ⊗[ℤp] C.OM) : C.Φ z ∈ CurveModel.chartRing C.κ ({C.x} : Set C.Fb) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a c =>
    rw [Φ_tmul]
    exact mul_mem (Subalgebra.algebraMap_mem _ a) (C.θF_mem_chartRing c)
  | add z₁ z₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂

def Φc : C.κ ⊗[ℤp] C.OM →ₐ[C.κ] ↥(CurveModel.chartRing C.κ ({C.x} : Set C.Fb)) :=
  C.Φ.codRestrict (CurveModel.chartRing C.κ ({C.x} : Set C.Fb)) C.Φ_mem_chartRing

theorem coe_Φc (z : C.κ ⊗[ℤp] C.OM) : (C.Φc z : C.Fb) = C.Φ z := rfl

def Φ₀ : C.κ ⊗[ℤp] C.OM →ₐ[C.κ] LaurentSeries C.κ :=
  (qExpFunctionFieldC C.κ (ΓN p C.M C.H C.hpM)).val.comp C.Φ

theorem Φ₀_apply (z : C.κ ⊗[ℤp] C.OM) : C.Φ₀ z = (C.Φ z : LaurentSeries C.κ) := rfl

theorem Φ₀_tmul (a : C.κ) (c : C.OM) : C.Φ₀ (a ⊗ₜ[ℤp] c) = a • C.θ₀ c := by
  rw [Φ₀_apply, Φ_tmul, MulMemClass.coe_mul, coe_algebraMap_Fb, coe_θF, HahnSeries.C_mul_eq_smul]

theorem exists_eFin : ∃ eFin : C.κ ⊗[ℤp] C.ON ≃ₐ[C.κ] ↥(CurveModel.chartRing C.κ ({C.x} : Set C.Fb)),
    (eFin ((1 : C.κ) ⊗ₜ[ℤp] jChartFin p (ΓN p C.M C.H C.hpM) C.hj)).1 = C.x ∧
    ∀ (b : C.ON) (y : LaurentSeries ↥C.A),
      coeffMap C.A.subtype y = coeffEmb (AlgebraicClosure ℚ)
        (((b : C.ON) : ↥(qExpFunctionFieldC ℚ (ΓN p C.M C.H C.hpM))) : LaurentSeries ℚ) →
      (((eFin ((1 : C.κ) ⊗ₜ[ℤp] b)).1 : C.Fb) : LaurentSeries C.κ) = coeffMap (residue ↥C.A) y :=
  (ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
    (C.M / p) (ΓN p C.M C.H C.hpM) C.gamma1_le C.gamma0_ge p C.not_dvd_div (jAt (ΓN p C.M C.H C.hpM) C.hj)
    (coe_jAt _ C.hj) C.A C.hA C.ρ C.hρ C.x C.coe_x).1

def eFin : C.κ ⊗[ℤp] C.ON ≃ₐ[C.κ] ↥(CurveModel.chartRing C.κ ({C.x} : Set C.Fb)) := C.exists_eFin.choose

theorem eFin_read (b : C.ON) (y : LaurentSeries ↥C.A)
    (hy : coeffMap C.A.subtype y = coeffEmb (AlgebraicClosure ℚ)
      (((b : C.ON) : ↥(qExpFunctionFieldC ℚ (ΓN p C.M C.H C.hpM))) : LaurentSeries ℚ)) :
    (((C.eFin ((1 : C.κ) ⊗ₜ[ℤp] b)).1 : C.Fb) : LaurentSeries C.κ) = coeffMap (residue ↥C.A) y :=
  C.exists_eFin.choose_spec.2 b y hy

theorem exists_lift (b : C.ON) : ∃ y : LaurentSeries ↥C.A,
    coeffMap C.A.subtype y = coeffEmb (AlgebraicClosure ℚ)
      (((b : C.ON) : ↥(qExpFunctionFieldC ℚ (ΓN p C.M C.H C.hpM))) : LaurentSeries ℚ) := by
  obtain ⟨y₀, hy₀⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓN p C.M C.H C.hpM) p (jAt (ΓN p C.M C.H C.hpM) C.hj) (coe_jAt _ C.hj)).1 b
  refine ⟨coeffMap C.ρ y₀, ?_⟩
  rw [coeffMap_coeffMap, C.hρ, ← hy₀, coeffEmb_coeffMap_algebraMap]

theorem θF_iota0 (b : C.ON) : C.θF (C.iota0 b) = (C.eFin ((1 : C.κ) ⊗ₜ[ℤp] b)).1 := by
  obtain ⟨y, hy⟩ := C.exists_lift b
  apply Subtype.ext
  rw [coe_θF, C.eFin_read b y hy]
  refine C.hθ₀read (C.iota0 b) y ?_
  rw [C.iota0_spec]
  exact hy

def σ₀ : C.κ ⊗[ℤp] C.OM →ₐ[C.κ] C.κ ⊗[ℤp] C.ON := (C.eFin.symm : _ →ₐ[C.κ] _).comp C.Φc

abbrev mapι : C.κ ⊗[ℤp] C.ON →ₐ[C.κ] C.κ ⊗[ℤp] C.OM := Algebra.TensorProduct.map (AlgHom.id C.κ C.κ) C.iota0

theorem σ₀_mapι (z : C.κ ⊗[ℤp] C.ON) : C.σ₀ (C.mapι z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    show C.eFin.symm (C.Φc (a ⊗ₜ[ℤp] C.iota0 b)) = a ⊗ₜ[ℤp] b
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_Φc, Φ_tmul, θF_iota0,
      show a ⊗ₜ[ℤp] b = algebraMap C.κ (C.κ ⊗[ℤp] C.ON) a * ((1 : C.κ) ⊗ₜ[ℤp] b) by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
      map_mul, AlgEquiv.commutes, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

theorem σ₀_surjective : Function.Surjective C.σ₀ := fun w => ⟨C.mapι w, C.σ₀_mapι w⟩

theorem ker_σ₀ : RingHom.ker C.σ₀.toRingHom = RingHom.ker C.Φ₀.toRingHom := by
  ext z
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  show C.eFin.symm (C.Φc z) = 0 ↔ C.Φ₀ z = 0
  rw [map_eq_zero_iff _ C.eFin.symm.injective, Φ₀_apply, ← coe_Φc, ZeroMemClass.coe_eq_zero, ZeroMemClass.coe_eq_zero]

abbrev B : Type := C.κ ⊗[ℤp] C.OM

abbrev fB : C.κ[X] →+* C.B :=
  (Polynomial.aeval ((1 : C.κ) ⊗ₜ[ℤp] jChartFin p (ΓM C.M C.H) C.hj) : C.κ[X] →ₐ[C.κ] C.B).toRingHom

theorem algebraMap_B_int (c : ℤp) : algebraMap ℤp C.B c = algebraMap C.κ C.B (algebraMap ℤp C.κ c) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem includeRight_comp_evJ :
    (Algebra.TensorProduct.includeRight : C.OM →ₐ[ℤp] C.B).toRingHom.comp (evJ (p := p) (ΓM C.M C.H) C.hj) =
      C.fB.comp (Polynomial.mapRingHom (algebraMap ℤp C.κ)) := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.aeval_C, AlgHom.commutes]
    exact C.algebraMap_B_int c
  · simp

theorem isIntegralElem_B (z : C.B) : C.fB.IsIntegralElem z := by
  induction z using TensorProduct.induction_on with
  | zero => simpa using C.fB.isIntegralElem_map (x := 0)
  | tmul a b =>
    have ha : C.fB.IsIntegralElem (a ⊗ₜ[ℤp] (1 : C.OM)) := by
      have : C.fB (Polynomial.C a) = a ⊗ₜ[ℤp] (1 : C.OM) := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [← this]
      exact C.fB.isIntegralElem_map
    have hb : C.fB.IsIntegralElem ((1 : C.κ) ⊗ₜ[ℤp] b) := by
      obtain ⟨P, hPmonic, hProot⟩ := exists_bivariate (p := p) (ΓM C.M C.H) C.hj b
      refine ⟨P.map (Polynomial.mapRingHom (algebraMap ℤp C.κ)), hPmonic.map _, ?_⟩
      have h1 := Polynomial.hom_eval₂ P (evJ (p := p) (ΓM C.M C.H) C.hj)
        (Algebra.TensorProduct.includeRight : C.OM →ₐ[ℤp] C.B).toRingHom b
      rw [hProot, map_zero, includeRight_comp_evJ] at h1
      rw [Polynomial.eval₂_map]
      exact h1.symm
    have := ha.mul C.fB hb
    rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
  | add z₁ z₂ h₁ h₂ => exact h₁.add _ h₂

theorem Φ₀_fB (Q : C.κ[X]) : C.Φ₀ (C.fB Q) = Polynomial.aeval (C.x : LaurentSeries C.κ) Q := by
  show C.Φ₀ (Polynomial.aeval _ Q) = _
  rw [← Polynomial.aeval_algHom_apply, Φ₀_tmul, one_smul]
  congr 1
  rw [← coe_θF, θF_j]

theorem transcendental_x_coe : Transcendental C.κ (C.x : LaurentSeries C.κ) := by
  have ht := C.transcendental_x
  rw [transcendental_iff] at ht ⊢
  intro Q hQ
  apply ht Q
  apply Subtype.ext
  have h1 : Polynomial.aeval ((C.x : C.Fb) : LaurentSeries C.κ) Q = ((Polynomial.aeval C.x Q : C.Fb) : LaurentSeries C.κ) :=
    Polynomial.aeval_algHom_apply (qExpFunctionFieldC C.κ (ΓN p C.M C.H C.hpM)).val C.x Q
  rw [← h1, hQ]
  rfl

theorem comap_ker_Φ₀ : (RingHom.ker C.Φ₀.toRingHom).comap C.fB = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun Q hQ => ?_
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Φ₀_fB] at hQ
  exact (transcendental_iff.mp C.transcendental_x_coe) Q hQ

theorem ker_Φ₀_mem_minimalPrimes : RingHom.ker C.Φ₀.toRingHom ∈ minimalPrimes C.B := by
  haveI hprime : (RingHom.ker C.Φ₀.toRingHom).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨hprime, bot_le⟩, ?_⟩
  rintro q ⟨hq, -⟩ hle
  by_contra hnot
  obtain ⟨z, hzK, hzq⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨P, hPmonic, hProot⟩ := C.isIntegralElem_B z
  haveI := hq
  have hlt := Ideal.comap_lt_comap_of_root_mem_sdiff (f := C.fB) hle ⟨hzK, hzq⟩
    (p := P) ?_ (by rw [hProot]; exact q.zero_mem)
  · rw [comap_ker_Φ₀] at hlt
    exact not_lt_bot hlt
  · haveI : Nontrivial (C.κ[X] ⧸ Ideal.comap C.fB q) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.comap_ne_top _ hq.ne_top)
    exact (hPmonic.map _).ne_zero

theorem ker_σ₀_mem_minimalPrimes : RingHom.ker C.σ₀.toRingHom ∈ minimalPrimes C.B := by
  rw [ker_σ₀]; exact C.ker_Φ₀_mem_minimalPrimes

theorem main :
    ∃ (σ₀ : C.κ ⊗[ℤp] C.OM →ₐ[C.κ] C.κ ⊗[ℤp] C.ON) (Φ₀ : C.κ ⊗[ℤp] C.OM →ₐ[C.κ] LaurentSeries C.κ),
      (∀ (x : C.κ) (c : C.OM), Φ₀ (x ⊗ₜ[ℤp] c) = x • C.θ₀ c) ∧
      (∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id C.κ C.κ) C.iota0 z) = z) ∧
      Function.Surjective σ₀ ∧
      RingHom.ker σ₀.toRingHom = RingHom.ker Φ₀.toRingHom ∧
      RingHom.ker σ₀.toRingHom ∈ minimalPrimes (C.κ ⊗[ℤp] C.OM) :=
  ⟨C.σ₀, C.Φ₀, C.Φ₀_tmul, C.σ₀_mapι, C.σ₀_surjective, C.ker_σ₀, C.ker_σ₀_mem_minimalPrimes⟩

end Ctx
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_retraction_of_ringHom_laurentSeries_chartAlgFin_gammaH.XHSigma.Ctx"

end XHSigma
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_retraction_of_ringHom_laurentSeries_chartAlgFin_gammaH.XHSigma.Ctx P2MW.S_ModularCurve_XHDRLevel_exists_retraction_of_ringHom_laurentSeries_chartAlgFin_gammaH.XHSigma"

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ₀ : ↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (IsLocalRing.ResidueField ↥A))
    (hθ₀C : ∀ c : R p, θ₀ (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) c) = HahnSeries.C ((IsLocalRing.residue ↥A) (ρ c)))
    (hθ₀read : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        θ₀ c = coeffMap (IsLocalRing.residue ↥A) y)
    (hθ₀range : ∀ c : ↥(chartAlgFin p (ΓM M H) hj), θ₀ c ∈ qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∃ (σ₀ : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
      (Φ₀ : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A] LaurentSeries (IsLocalRing.ResidueField ↥A)),
      (∀ (x : IsLocalRing.ResidueField ↥A) (c : ↥(chartAlgFin p (ΓM M H) hj)), Φ₀ (x ⊗ₜ[R p] c) = x • θ₀ c) ∧
      (∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) iota0 z) = z) ∧
      Function.Surjective σ₀ ∧
      RingHom.ker σ₀.toRingHom = RingHom.ker Φ₀.toRingHom ∧
      RingHom.ker σ₀.toRingHom ∈ minimalPrimes ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) := by
  let C : XHSigma.Ctx (p := p) :=
    { M := M, H := H, hpM := hpM, hpM2 := hpM2, hj := hj, iota0 := iota0, iota0_spec := iota0_spec, A := A, hA := hA,
      ρ := ρ, hρ := hρ, θ₀ := θ₀, hθ₀C := hθ₀C, hθ₀read := hθ₀read, hθ₀range := hθ₀range }
  exact C.main

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_retraction_of_ringHom_laurentSeries_chartAlgFin_gammaH.XHSigma.Ctx P2MW.S_ModularCurve_XHDRLevel_exists_retraction_of_ringHom_laurentSeries_chartAlgFin_gammaH.XHSigma"

end S_ModularCurve_XHDRLevel_exists_retraction_of_ringHom_laurentSeries_chartAlgFin_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_retraction_of_ringHom_laurentSeries_chartAlgFin_gammaH (solution)
