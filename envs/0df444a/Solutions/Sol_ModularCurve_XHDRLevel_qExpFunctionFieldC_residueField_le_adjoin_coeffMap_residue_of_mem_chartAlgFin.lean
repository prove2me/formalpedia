-- Prove2me | solution 1 for ModularCurve.XHDRLevel.qExpFunctionFieldC_residueField_le_adjoin_coeffMap_residue_of_mem_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ec012358-c663-5fb9-bce7-49b71a4369e1

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_LaurentSeries_exists_forall_coeff_eq_of_isIntegral_of_mem_closure_range_ofPowerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_qExpFunctionFieldC_residueField_le_adjoin_coeffMap_residue_of_mem_chartAlgFin
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

open IsLocalRing ModularCurve ModularCurve.XHDRLevel AlgebraicCurve
open scoped MatrixGroups

namespace PIRAux

p2m_open "GaloisRep~isPrincipalIdealRing_ratLocalizedAt"

variable (p : ℕ) [hp : Fact p.Prime]

theorem mem_iff (q : ℚ) : q ∈ ratLocalizedAt p ↔ q.den.Coprime p := Iff.rfl

theorem inv_intCast_mem {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) : ((s : ℚ)⁻¹) ∈ ratLocalizedAt p := by
  rw [mem_iff]
  have hs0 : s ≠ 0 := by rintro rfl; exact hs (dvd_zero _)
  rw [Rat.inv_intCast_den, if_neg hs0]
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  apply hs
  have : (p : ℤ) ∣ (s.natAbs : ℤ) := by exact_mod_cast h
  exact Int.dvd_natAbs.mp this

scoped instance : Algebra ℤ ↥(ratLocalizedAt p) := Int.castRingHom _ |>.toAlgebra

private theorem _root_.PIRAux.algebraMap_apply (n : ℤ) : (algebraMap ℤ ↥(ratLocalizedAt p) n : ℚ) = n := by
  show ((Int.castRingHom ↥(ratLocalizedAt p) n : ↥(ratLocalizedAt p)) : ℚ) = n
  simp

p2m_export "PIRAux" "algebraMap_apply"
theorem isLocalization : IsLocalization.AtPrime ↥(ratLocalizedAt p) (Ideal.span {(p : ℤ)}) := by
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨s, hs⟩
    have hs' : ¬ (p : ℤ) ∣ s := by
      intro h; exact hs (Ideal.mem_span_singleton.mpr h)
    have hs0 : (s : ℚ) ≠ 0 := by
      have : s ≠ 0 := by rintro rfl; exact hs' (dvd_zero _)
      exact_mod_cast this
    refine ⟨⟨algebraMap ℤ _ s, ⟨(s : ℚ)⁻¹, inv_intCast_mem p hs'⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; show ((algebraMap ℤ ↥(ratLocalizedAt p) s : ℚ)) * (s : ℚ)⁻¹ = 1
      rw [algebraMap_apply, mul_inv_cancel₀ hs0]
    · apply Subtype.ext; show (s : ℚ)⁻¹ * ((algebraMap ℤ ↥(ratLocalizedAt p) s : ℚ)) = 1
      rw [algebraMap_apply, inv_mul_cancel₀ hs0]
  ·
    rintro ⟨q, hq⟩
    have hden : (q.den : ℤ) ∉ Ideal.span {(p : ℤ)} := by
      intro h
      rw [Ideal.mem_span_singleton] at h
      have h' : p ∣ q.den := by exact_mod_cast h
      rw [mem_iff, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out] at hq
      exact hq h'
    refine ⟨⟨q.num, ⟨q.den, hden⟩⟩, ?_⟩
    apply Subtype.ext
    show q * ((algebraMap ℤ ↥(ratLocalizedAt p) (q.den : ℤ) : ℚ)) = ((algebraMap ℤ ↥(ratLocalizedAt p) q.num : ℚ))
    rw [algebraMap_apply, algebraMap_apply]
    push_cast
    exact Rat.mul_den_eq_num q
  ·
    intro a b h
    refine ⟨1, ?_⟩
    have : (a : ℚ) = b := by
      have := congrArg (fun x : ↥(ratLocalizedAt p) => (x : ℚ)) h
      simpa [algebraMap_apply] using this
    simpa using (Int.cast_injective this : a = b)

theorem isPrincipalIdealRing : IsPrincipalIdealRing ↥(ratLocalizedAt p) := by
  haveI := isLocalization p
  haveI : IsDomain ↥(ratLocalizedAt p) := inferInstance
  have hp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.out.ne_zero
  haveI : IsDiscreteValuationRing ↥(ratLocalizedAt p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hp0 _
  infer_instance

end PIRAux
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_qExpFunctionFieldC_residueField_le_adjoin_coeffMap_residue_of_mem_chartAlgFin.PIRAux"

theorem isPrincipalIdealRing_ratLocalizedAt (p : ℕ) [Fact p.Prime] : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt p) :=
  PIRAux.isPrincipalIdealRing p

namespace ResFieldGen

theorem coe_mem_of_liesOverPrime (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (r : ↥(GaloisRep.ratLocalizedAt p)) : (algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ)) ∈ A := by
  obtain ⟨hpA, hpm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hA
  set q : ℚ := (r : ℚ) with hq
  have hcop : q.den.Coprime p := r.2
  obtain ⟨u, v, huv⟩ : IsCoprime (q.den : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop

  have hden_unit : IsUnit ((q.den : ℕ) : ↥A) := by
    have h1 : (u : ↥A) * ((q.den : ℕ) : ↥A) = 1 - (v : ↥A) * (p : ↥A) := by
      have := congrArg (fun z : ℤ => (z : ↥A)) huv
      push_cast at this
      linear_combination this
    have hpeq : ((p : ℕ) : ↥A) = ⟨(p : AlgebraicClosure ℚ), hpA⟩ := Subtype.ext (by push_cast; rfl)
    have hvp : (v : ↥A) * (p : ↥A) ∈ maximalIdeal ↥A := by
      rw [hpeq]; exact Ideal.mul_mem_left _ _ hpm
    have hu1 : IsUnit (1 - (v : ↥A) * (p : ↥A)) := by
      apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      rwa [← IsLocalRing.mem_maximalIdeal]
    rw [← h1] at hu1
    exact isUnit_of_mul_isUnit_right hu1
  obtain ⟨w, hw⟩ := hden_unit
  have hwc : ((w : ↥A) : AlgebraicClosure ℚ) = (q.den : AlgebraicClosure ℚ) := by
    rw [hw]; push_cast; rfl
  have hinv : ((q.den : AlgebraicClosure ℚ))⁻¹ = (((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) := by
    rw [← hwc]
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rfl

  have hr : algebraMap ℚ (AlgebraicClosure ℚ) q = (q.num : AlgebraicClosure ℚ) * ((q.den : AlgebraicClosure ℚ))⁻¹ := by
    show ((q : ℚ) : AlgebraicClosure ℚ) = _
    rw [Rat.cast_def, div_eq_mul_inv]
  rw [hr, hinv]
  exact mul_mem (intCast_mem A q.num) (SetLike.coe_mem _)

theorem exists_ringHom_ratLocalizedAt (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ ρ : R p →+* ↥A, A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ) := by
  let f : R p →+* AlgebraicClosure ℚ := (algebraMap ℚ (AlgebraicClosure ℚ)).comp (GaloisRep.ratLocalizedAt p).subtype
  have hf : ∀ r, f r ∈ A.toSubring := fun r => coe_mem_of_liesOverPrime p A hA r
  refine ⟨f.codRestrict A.toSubring hf, ?_⟩
  ext r
  rfl

section Lift

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem coe_mem_closure (f : ↥(qExpFunctionFieldC ℚ Γ)) :
    (f : LaurentSeries ℚ) ∈ Subfield.closure (Set.range ((HahnSeries.ofPowerSeries ℤ ℚ).comp
      (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype))) := by
  set T := Subfield.closure (Set.range ((HahnSeries.ofPowerSeries ℤ ℚ).comp
      (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype))) with hT

  have hint : ∀ q : PowerSeries ℤ, intSeriesC ℚ q ∈ T := by
    intro q
    apply Subfield.subset_closure
    refine ⟨q.map (Int.castRingHom _), ?_⟩
    show HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype (PowerSeries.map (Int.castRingHom _) q)) = _
    rw [← RingHom.comp_apply (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype), ← PowerSeries.map_comp,
      RingHom.ext_int ((GaloisRep.ratLocalizedAt p).subtype.comp (Int.castRingHom _)) (Int.castRingHom ℚ)]
    rfl

  have hconst : ∀ c : ℚ, algebraMap ℚ (LaurentSeries ℚ) c ∈ T := by
    intro c
    have hn : ∀ n : ℤ, algebraMap ℚ (LaurentSeries ℚ) (n : ℚ) ∈ T := by
      intro n
      have := hint (PowerSeries.C n)
      rw [intSeriesC, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C] at this
      rw [ModularCurve.algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]
      exact_mod_cast this
    have hc : algebraMap ℚ (LaurentSeries ℚ) c = algebraMap ℚ (LaurentSeries ℚ) (c.num : ℚ) / algebraMap ℚ (LaurentSeries ℚ) (c.den : ℚ) := by
      rw [← map_div₀]
      congr 1
      exact_mod_cast (Rat.num_div_den c).symm
    rw [hc]
    exact div_mem (hn c.num) (by exact_mod_cast hn c.den)

  let T' : IntermediateField ℚ (LaurentSeries ℚ) := T.toIntermediateField hconst
  have hle : qExpFunctionFieldC ℚ Γ ≤ T' := by
    rw [qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
    rintro x ⟨k, fm, gm, pf, pg, -, -, -, rfl⟩
    exact div_mem (hint pf) (hint pg)
  exact hle f.2

theorem coeff_mem_of_mem_adjoin (a : ↥(qExpFunctionFieldC ℚ Γ))
    (ha : a ∈ Algebra.adjoin (R p) ({jAt Γ hj} : Set ↥(qExpFunctionFieldC ℚ Γ))) (n : ℤ) :
    ((a : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ).coeff n ∈ GaloisRep.ratLocalizedAt p := by
  induction ha using Algebra.adjoin_induction generalizing n with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [coe_jAt, coeff_jqModC_eq_intCast]
    exact intCast_mem _ _
  | algebraMap r =>
    have : ((algebraMap (R p) ↥(qExpFunctionFieldC ℚ Γ) r : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)
        = HahnSeries.single 0 ((r : ℚ)) := by
      rw [IsScalarTower.algebraMap_apply (R p) ℚ ↥(qExpFunctionFieldC ℚ Γ) r, ← ModularCurve.algebraMap_laurentSeries_eq_single]
      simp
      rfl
    rw [this, HahnSeries.coeff_single]
    split_ifs
    · exact r.2
    · exact zero_mem _
  | add x y _ _ hx hy =>
    rw [show (((x + y : ↥(qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) + (y : LaurentSeries ℚ) from rfl,
      HahnSeries.coeff_add]
    exact add_mem (hx n) (hy n)
  | mul x y _ _ hx hy =>
    rw [show (((x * y : ↥(qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) * (y : LaurentSeries ℚ) from rfl,
      HahnSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hx _) (hy _)

theorem exists_lift (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (b : ↥(chartAlgFin p Γ hj)) :
    ∃ y : LaurentSeries ↥A,
      coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) := by
  classical
  haveI : IsPrincipalIdealRing (R p) := isPrincipalIdealRing_ratLocalizedAt p

  set B : Subalgebra (R p) ↥(qExpFunctionFieldC ℚ Γ) := Algebra.adjoin (R p) ({jAt Γ hj} : Set ↥(qExpFunctionFieldC ℚ Γ)) with hB
  let ι : ↥(qExpFunctionFieldC ℚ Γ) →+* LaurentSeries ℚ := algebraMap ↥(qExpFunctionFieldC ℚ Γ) (LaurentSeries ℚ)
  have hι : Function.Injective ι := Subtype.val_injective
  set S : Subring (LaurentSeries ℚ) := B.toSubring.map ι with hS
  have hScoef : ∀ z ∈ S, ∀ n : ℤ, z.coeff n ∈ Set.range (GaloisRep.ratLocalizedAt p).subtype := by
    rintro z ⟨a, ha, rfl⟩ n
    exact ⟨⟨_, coeff_mem_of_mem_adjoin p Γ hj a ha n⟩, rfl⟩

  have hint : IsIntegral ↥S ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) := by
    obtain ⟨P, hPm, hP⟩ := (b.2 : IsIntegral ↥B (b : ↥(qExpFunctionFieldC ℚ Γ)))
    let φ : ↥B.toSubring ≃+* ↥S := B.toSubring.equivMapOfInjective ι hι
    refine ⟨P.map φ.toRingHom, hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥S (LaurentSeries ℚ)).comp φ.toRingHom = ι.comp (algebraMap ↥B ↥(qExpFunctionFieldC ℚ Γ)) := by
      ext a; rfl
    rw [hcomp, show ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = ι (b : ↥(qExpFunctionFieldC ℚ Γ)) from rfl,
      ← Polynomial.hom_eval₂, hP, map_zero]
  obtain ⟨y₀, hy₀⟩ := LaurentSeries.exists_forall_coeff_eq_of_isIntegral_of_mem_closure_range_ofPowerSeries
    (GaloisRep.ratLocalizedAt p).subtype Subtype.val_injective _ (coe_mem_closure p Γ (b : ↥(qExpFunctionFieldC ℚ Γ))) S hScoef hint
  refine ⟨coeffMap ρ y₀, ?_⟩
  ext n
  rw [coeffMap_coeffMap, hρ, coeffMap_coeff, coeffEmb_coeff, ← hy₀ n]
  rfl

end Lift
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_qExpFunctionFieldC_residueField_le_adjoin_coeffMap_residue_of_mem_chartAlgFin.PIRAux"

theorem not_dvd_div {p M : ℕ} (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ¬ p ∣ M / p := by
  intro h
  apply hpM2
  obtain ⟨k, hk⟩ := h
  have : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
  rw [pow_two, this, hk, ← mul_assoc]
  exact dvd_mul_right _ _

end ResFieldGen
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_qExpFunctionFieldC_residueField_le_adjoin_coeffMap_residue_of_mem_chartAlgFin.PIRAux"

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ResFieldGen AlgebraicCurve.CurveModel in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] :
    (qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM) : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))) ≤
      IntermediateField.adjoin (ResidueField ↥A)
        {x : LaurentSeries (ResidueField ↥A) |
          ∃ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
            coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) ∧
            x = coeffMap (IsLocalRing.residue ↥A) y} := by
  classical
  obtain ⟨ρ, hρ⟩ := ResFieldGen.exists_ringHom_ratLocalizedAt p A hA
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  have hΓ₁ : CongruenceSubgroup.Gamma1 (M / p) ≤ ΓN p M H hpM := Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM)
  have hΓ₀ : ΓN p M H hpM ≤ CongruenceSubgroup.Gamma0 (M / p) := CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM)
  have hpN : ¬ p ∣ M / p := ResFieldGen.not_dvd_div hpM hpM2

  have hjκ : jqModC (ResidueField ↥A) ∈ qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM) :=
    x0_le_xHFunctionFieldC (K := ResidueField ↥A) (M := M / p) (H := infSubgroup p M H hpM)
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 (ResidueField ↥A) (M / p)
        (jqModC_mem_full (K := ResidueField ↥A) (N := M / p)))
  set xb : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) := ⟨jqModC (ResidueField ↥A), hjκ⟩ with hxbdef
  have hxb : (xb : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := rfl

  obtain ⟨⟨eFin, -, hread⟩, -⟩ :=
    ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
      (M / p) (ΓN p M H hpM) hΓ₁ hΓ₀ p hpN (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj) A hA ρ hρ xb hxb

  have hlift : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), ∃ y : LaurentSeries ↥A,
      coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) := by
    exact fun b => ResFieldGen.exists_lift p (ΓN p M H hpM) hj A ρ hρ b

  set X : Set (LaurentSeries (ResidueField ↥A)) := {x : LaurentSeries (ResidueField ↥A) |
          ∃ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
            coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) ∧
            x = coeffMap (IsLocalRing.residue ↥A) y} with hXdef
  set E := IntermediateField.adjoin (ResidueField ↥A) X with hEdef

  have hgen : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((eFin ((1 : ResidueField ↥A) ⊗ₜ[R p] b)).1 : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) :
        LaurentSeries (ResidueField ↥A)) ∈ E := by
    intro b
    obtain ⟨y, hy⟩ := hlift b
    exact IntermediateField.subset_adjoin _ _ ⟨b, y, hy, hread b y hy⟩

  have coe_mul' : ∀ u w : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)),
      ((u * w : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) =
        (u : LaurentSeries (ResidueField ↥A)) * (w : LaurentSeries (ResidueField ↥A)) := fun _ _ => rfl
  have coe_add' : ∀ u w : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)),
      ((u + w : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) =
        (u : LaurentSeries (ResidueField ↥A)) + (w : LaurentSeries (ResidueField ↥A)) := fun _ _ => rfl
  have coe_alg' : ∀ k : ResidueField ↥A,
      ((algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) k :
          ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) =
        algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) k := fun _ => rfl

  have hchart : ∀ c : ↥(chartRing (ResidueField ↥A) ({xb} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)))),
      ((c : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) ∈ E := by
    intro c
    obtain ⟨t, rfl⟩ := eFin.surjective c
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero]
      exact zero_mem E
    | tmul k b =>
      have htm : k ⊗ₜ[R p] b = algebraMap (ResidueField ↥A) _ k * ((1 : ResidueField ↥A) ⊗ₜ[R p] b) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp
      rw [htm, map_mul, AlgEquiv.commutes, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, coe_mul', coe_alg']
      exact mul_mem (IntermediateField.algebraMap_mem E k) (hgen b)
    | add x y hx hy =>
      rw [map_add, Subalgebra.coe_add, coe_add']
      exact add_mem hx hy

  haveI : (ΓN p M H hpM).FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁
  haveI hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (ResidueField ↥A) ({xb} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))))
      ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) :=
    (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index (ResidueField ↥A)
      (ΓN p M H hpM) (translation_mem_GammaH (M / p) (infSubgroup p M H hpM)) (ΓN p M H hpM) le_rfl
      (fun γ hγ => Or.inl hγ) xb hxb).1
  open scoped IntermediateField.algebraAdjoinAdjoin in
  haveI hfr : IsFractionRing
      ↥(chartRing (ResidueField ↥A) ({xb} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))))
      ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      (Algebra.adjoin (ResidueField ↥A) ({xb} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))))
      (IntermediateField.adjoin (ResidueField ↥A) ({xb} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))))
      ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) _

  intro f hf
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective
    (A := ↥(chartRing (ResidueField ↥A) ({xb} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)))))
    (⟨f, hf⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)))
  have hfc : f = ((c : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) /
      ((d : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) := by
    have := congrArg (fun z : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) => (z : LaurentSeries (ResidueField ↥A))) hcd
    simp only at this
    rw [← this]
    rfl
  rw [hfc]
  exact div_mem (hchart c) (hchart d)

end S_ModularCurve_XHDRLevel_qExpFunctionFieldC_residueField_le_adjoin_coeffMap_residue_of_mem_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_qExpFunctionFieldC_residueField_le_adjoin_coeffMap_residue_of_mem_chartAlgFin (solution)
