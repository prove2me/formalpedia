-- Prove2me | solution 1 for ModularCurve.FullLevel.isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/bcbd5243-f507-57f1-8bc5-d64b82d9a866

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_IgusaFunctionField
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_ModularCurve_FullLevel_isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic ModularCurve.FullLevel.SemistableCovering.instAlgebraSS ModularCurve.FullLevel.SemistableCovering.instFieldIg ModularCurve.FullLevel.SemistableCovering.instFieldSS"
p2m_attr_erase "instance" "ModularCurve.FullLevel.SemistableCovering.instAlgebraIg CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.FullLevel.SemistableCovering.mk.sizeOf_spec ModularCurve.FullLevel.SemistableCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce"
p2m_attr_erase "simp" "CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

noncomputable section

open scoped ArithmeticFunction.sigma
p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC~coeffMap_jqModC~coeffMap_jqNModC P2MW.S_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH xHFunctionFieldC intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset qExpand dedekindEtaUnit ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem IgusaCover.igusaFunctionField_eq_sup FullLevel.isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH coeffMap_qExpand"
namespace IgSepKappaAux
p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC~coeffMap_jqModC~coeffMap_jqNModC"

section CoeffMap

variable {K K' : Type*} [Field K] [Field K'] (f : K →+* K')

theorem coeffMap_injective : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  exact f.injective (by simpa only [coeffMap_coeff] using congrArg (fun z : LaurentSeries K' => z.coeff k) h)

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) : coeffMap f (intSeriesC K p) = intSeriesC K' p := by
  have hseries : ∀ u : PowerSeries K,
      (HahnSeries.ofPowerSeries ℤ K u).map f = HahnSeries.ofPowerSeries ℤ K' (u.map f) := by
    intro u
    ext k
    rw [HahnSeries.map_coeff]
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  change (intSeriesC K p).map f = intSeriesC K' p
  rw [intSeriesC, intSeriesC, hseries,
    show (p.map (Int.castRingHom K)).map f = p.map (Int.castRingHom K') from by
      rw [show PowerSeries.map f (PowerSeries.map (Int.castRingHom K) p)
            = PowerSeries.map (f.comp (Int.castRingHom K)) p from
          (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom K) f)) p).symm,
        RingHom.ext_int (f.comp (Int.castRingHom K)) (Int.castRingHom K')]]

theorem image_intFormRatiosC_eq (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    coeffMap f '' intFormRatiosC K Γ = intFormRatiosC K' Γ := by
  apply subset_antisymm
  · rintro _ ⟨x, ⟨k, F, G, pf, pg, hF, hG, hg0, rfl⟩, rfl⟩
    refine ⟨k, F, G, pf, pg, hF, hG, ?_, ?_⟩
    · rw [← coeffMap_intSeriesC f]
      exact fun h => hg0 (coeffMap_injective f (by rw [h, map_zero]))
    · rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  · rintro x ⟨k, F, G, pf, pg, hF, hG, hg0, rfl⟩
    refine ⟨intSeriesC K pf / intSeriesC K pg, ⟨k, F, G, pf, pg, hF, hG, ?_, rfl⟩, ?_⟩
    · intro h
      apply hg0
      rw [← coeffMap_intSeriesC f, h, map_zero]
    · rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

theorem coeffMap_jqModC : coeffMap f (jqModC K) = jqModC K' := by
  change (jqModC K).map f = jqModC K'
  exact map_jqModC f

theorem coeffMap_jqNModC (N : ℕ) [NeZero N] : coeffMap f (jqNModC K N) = jqNModC K' N := by
  change coeffMap f (qExpand K N (jqModC K)) = qExpand K' N (jqModC K')
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem coeffMap_algebraMap' (c : K) :
    coeffMap f (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (f c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_modularFunctionFieldC (N : ℕ) [NeZero N] {x : LaurentSeries K}
    (hx : x ∈ modularFunctionFieldC K N) : coeffMap f x ∈ modularFunctionFieldC K' N := by
  have hx' : x ∈ (IntermediateField.adjoin K ({jqModC K, jqNModC K N} : Set (LaurentSeries K))).toSubfield := hx
  rw [IntermediateField.adjoin_toSubfield] at hx'
  clear hx
  induction hx' using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [coeffMap_algebraMap']
        exact (modularFunctionFieldC K' N).algebraMap_mem _
      · rcases hy with rfl | hy
        · rw [coeffMap_jqModC]; exact jqModC_mem K' N
        · rw [Set.mem_singleton_iff] at hy
          rw [hy, coeffMap_jqNModC]; exact jqNModC_mem K' N
  | one => rw [map_one]; exact one_mem _
  | add _ _ _ _ ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | neg _ _ ihx => rw [map_neg]; exact neg_mem ihx
  | inv _ _ ihx => rw [map_inv₀]; exact inv_mem ihx
  | mul _ _ _ _ ihx ihy => rw [map_mul]; exact mul_mem ihx ihy

end CoeffMap

section Transfer

variable {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (N : ℕ) [NeZero N]

def baseHom : ↥(modularFunctionFieldC K N) →+* LaurentSeries K' :=
  (coeffMap φ).comp (algebraMap ↥(modularFunctionFieldC K N) (LaurentSeries K))

@[reducible] def baseAlgebra : Algebra ↥(modularFunctionFieldC K N) (LaurentSeries K') :=
  (baseHom φ N).toAlgebra

def liftAlgHom : letI := baseAlgebra φ N; LaurentSeries K →ₐ[↥(modularFunctionFieldC K N)] LaurentSeries K' :=
  letI := baseAlgebra φ N
  { coeffMap φ with commutes' := fun _ => rfl }

theorem liftAlgHom_apply (x : LaurentSeries K) :
    letI := baseAlgebra φ N; liftAlgHom φ N x = coeffMap φ x := rfl

theorem liftAlgHom_injective : letI := baseAlgebra φ N; Function.Injective (liftAlgHom φ N) :=
  fun _ _ h => coeffMap_injective φ h

def baseHomRes : ↥(modularFunctionFieldC K N) →+* ↥(modularFunctionFieldC K' N) :=
  (baseHom φ N).codRestrict (modularFunctionFieldC K' N)
    (fun c => coeffMap_mem_modularFunctionFieldC φ N c.2)

@[reducible] def midAlgebra : Algebra ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K' N) :=
  (baseHomRes φ N).toAlgebra

theorem isScalarTower_mid :
    letI := baseAlgebra φ N; letI := midAlgebra φ N
    IsScalarTower ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K' N) (LaurentSeries K') :=
  letI := baseAlgebra φ N; letI := midAlgebra φ N
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isSeparable_coeffMap_of_isSeparable {x : LaurentSeries K}
    (hx : IsSeparable ↥(modularFunctionFieldC K N) x) :
    IsSeparable ↥(modularFunctionFieldC K' N) (coeffMap φ x) := by
  letI := baseAlgebra φ N
  letI := midAlgebra φ N
  haveI := isScalarTower_mid φ N
  have h1 : IsSeparable ↥(modularFunctionFieldC K N) (liftAlgHom φ N x) :=
    (isSeparable_map_iff (liftAlgHom φ N) (liftAlgHom_injective φ N)).mpr hx
  exact IsSeparable.tower_top _ h1

end Transfer

section PrimeField

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem isSeparable_of_mem_intFormRatiosC_zmod
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    {x₀ : LaurentSeries (ZMod q)}
    (hx₀ : x₀ ∈ intFormRatiosC (ZMod q) (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
    IsSeparable ↥(modularFunctionFieldC (ZMod q) M') x₀ := by
  classical
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨q, Fact.out⟩

  haveI hchar : CharP (IsLocalRing.ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  let ι₁ : ZMod q →+* IsLocalRing.ResidueField ↥A := ZMod.castHom (dvd_refl q) (IsLocalRing.ResidueField ↥A)
  letI algκ : Algebra (ZMod q) (IsLocalRing.ResidueField ↥A) := ι₁.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI halgκ : Algebra.IsAlgebraic (ZMod q) (IsLocalRing.ResidueField ↥A) :=
    ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat (AlgebraicClosure ℚ) A q

  obtain ⟨hK, hE, -⟩ :=
    ModularCurve.FullLevel.isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH
      q hq M' hqM' A hA
  set g : LaurentSeries (IsLocalRing.ResidueField ↥A) := (ModularCurve.intSeriesC (IsLocalRing.ResidueField ↥A) (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
            ModularCurve.intSeriesC (IsLocalRing.ResidueField ↥A) (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)) /
          ModularCurve.intSeriesC (IsLocalRing.ResidueField ↥A) (PowerSeries.X * ModularCurve.dedekindEtaUnit)) with hg
  set E₀ : IntermediateField (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)) := modularFunctionFieldC (IsLocalRing.ResidueField ↥A) M' with hE₀

  have hn : 0 < (q - 1) / 2 := hK.pos
  have hnκ : (((q - 1) / 2 : ℕ) : IsLocalRing.ResidueField ↥A) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥A) q]
    intro h
    have := Nat.le_of_dvd hn h
    omega
  have hnE₀ : (((q - 1) / 2 : ℕ) : ↥E₀) ≠ 0 := by
    intro h
    apply hnκ
    have h1 := congrArg (algebraMap ↥E₀ (LaurentSeries (IsLocalRing.ResidueField ↥A))) h
    rw [map_natCast, map_zero, ← map_natCast (algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A))), map_eq_zero] at h1
    exact h1

  have hgsep : IsSeparable ↥E₀ g := by
    let c : ↥E₀ := ⟨g ^ ((q - 1) / 2), hK.pow_mem⟩
    have hc : c ≠ 0 := fun h => by
      have h' : g ^ ((q - 1) / 2) = 0 := congrArg Subtype.val h
      exact hK.ne_zero (pow_eq_zero_iff hn.ne' |>.mp h')
    have hP : (Polynomial.X ^ ((q - 1) / 2) - Polynomial.C c).Separable :=
      Polynomial.separable_X_pow_sub_C c hnE₀ hc
    have haeval : Polynomial.aeval g (Polynomial.X ^ ((q - 1) / 2) - Polynomial.C c) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      exact sub_self _
    exact hP.of_dvd (minpoly.dvd ↥E₀ g haeval)

  have hsepE : ∀ y ∈ xHFunctionFieldC (IsLocalRing.ResidueField ↥A) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'), IsSeparable ↥E₀ y := by
    intro y hy
    rw [← hE, IgusaCover.igusaFunctionField_eq_sup, ← IntermediateField.restrictScalars_adjoin_eq_sup,
      IntermediateField.mem_restrictScalars] at hy
    haveI : Algebra.IsSeparable ↥E₀ ↥(IntermediateField.adjoin ↥E₀ ({g} : Set (LaurentSeries (IsLocalRing.ResidueField ↥A)))) :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (F := ↥E₀) (x := g)).mpr hgsep
    have h := Algebra.IsSeparable.isSeparable ↥E₀
      (⟨y, hy⟩ : ↥(IntermediateField.adjoin ↥E₀ ({g} : Set (LaurentSeries (IsLocalRing.ResidueField ↥A)))))
    simpa only [IntermediateField.coe_val] using
      h.map (IntermediateField.adjoin ↥E₀ ({g} : Set (LaurentSeries (IsLocalRing.ResidueField ↥A)))).val (fun _ _ e => Subtype.ext e)

  letI := baseAlgebra ι₁ M'
  letI := midAlgebra ι₁ M'
  haveI := isScalarTower_mid ι₁ M'
  letI algq : Algebra (ZMod q) (LaurentSeries (IsLocalRing.ResidueField ↥A)) :=
    ((algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A))).comp ι₁).toAlgebra
  haveI hST : @IsScalarTower (ZMod q) ↥(modularFunctionFieldC (ZMod q) M') (LaurentSeries (IsLocalRing.ResidueField ↥A))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)

  have hconst : ∀ c : IsLocalRing.ResidueField ↥A,
      IsSeparable ↥(modularFunctionFieldC (ZMod q) M') (algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)) c) := by
    intro c
    have hcs : IsSeparable (ZMod q) c :=
      PerfectField.separable_of_irreducible (minpoly.irreducible (Algebra.IsIntegral.isIntegral c))
    let ψ : IsLocalRing.ResidueField ↥A →ₐ[ZMod q] LaurentSeries (IsLocalRing.ResidueField ↥A) :=
      { algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)) with commutes' := fun _ => rfl }
    have h1 : IsSeparable (ZMod q) (ψ c) :=
      (isSeparable_map_iff ψ (algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A))).injective).mpr hcs
    exact IsSeparable.tower_top _ h1

  have hT : ∀ y ∈ E₀, IsSeparable ↥(modularFunctionFieldC (ZMod q) M') y := by
    let T : IntermediateField ↥(modularFunctionFieldC (ZMod q) M') (LaurentSeries (IsLocalRing.ResidueField ↥A)) :=
      IntermediateField.adjoin _ (Set.range (algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A))))
    haveI : Algebra.IsSeparable ↥(modularFunctionFieldC (ZMod q) M') ↥T :=
      (IntermediateField.isSeparable_adjoin_iff_isSeparable (F := ↥(modularFunctionFieldC (ZMod q) M'))
        (S := Set.range (algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A))))).mpr
        (by rintro _ ⟨c, rfl⟩; exact hconst c)
    have hj : jqModC (IsLocalRing.ResidueField ↥A) ∈ T := by
      have : algebraMap ↥(modularFunctionFieldC (ZMod q) M') (LaurentSeries (IsLocalRing.ResidueField ↥A))
          ⟨jqModC (ZMod q), jqModC_mem (ZMod q) M'⟩ = jqModC (IsLocalRing.ResidueField ↥A) := coeffMap_jqModC ι₁
      rw [← this]; exact T.algebraMap_mem _
    have hjN : jqNModC (IsLocalRing.ResidueField ↥A) M' ∈ T := by
      have : algebraMap ↥(modularFunctionFieldC (ZMod q) M') (LaurentSeries (IsLocalRing.ResidueField ↥A))
          ⟨jqNModC (ZMod q) M', jqNModC_mem (ZMod q) M'⟩ = jqNModC (IsLocalRing.ResidueField ↥A) M' := coeffMap_jqNModC ι₁ M'
      rw [← this]; exact T.algebraMap_mem _
    have hle : ∀ y ∈ E₀, y ∈ T := by
      intro y hy
      have hy' : y ∈ (IntermediateField.adjoin (IsLocalRing.ResidueField ↥A)
          ({jqModC (IsLocalRing.ResidueField ↥A), jqNModC (IsLocalRing.ResidueField ↥A) M'} : Set (LaurentSeries (IsLocalRing.ResidueField ↥A)))).toSubfield := hy
      rw [IntermediateField.adjoin_toSubfield] at hy'
      refine (Subfield.closure_le (t := T.toSubfield)).mpr ?_ hy'
      rintro z (⟨c, rfl⟩ | hz)
      · exact IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩
      · rcases hz with rfl | hz
        · exact hj
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]; exact hjN
    intro y hy
    have h := Algebra.IsSeparable.isSeparable ↥(modularFunctionFieldC (ZMod q) M') (⟨y, hle y hy⟩ : ↥T)
    simpa only [IntermediateField.coe_val] using h.map T.val (fun _ _ e => Subtype.ext e)
  haveI : Algebra.IsSeparable ↥(modularFunctionFieldC (ZMod q) M') ↥E₀ :=
    ⟨fun y => (isSeparable_map_iff (x := y)
      (IsScalarTower.toAlgHom ↥(modularFunctionFieldC (ZMod q) M') ↥E₀ (LaurentSeries (IsLocalRing.ResidueField ↥A)))
      (fun _ _ h => Subtype.ext h)).mp (hT y y.2)⟩

  have hx₁ : coeffMap ι₁ x₀ ∈ xHFunctionFieldC (IsLocalRing.ResidueField ↥A) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') := by
    show coeffMap ι₁ x₀ ∈ qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    apply intFormRatiosC_subset
    rw [← image_intFormRatiosC_eq ι₁]
    exact ⟨x₀, hx₀, rfl⟩
  have h2 : IsSeparable ↥E₀ (liftAlgHom ι₁ M' x₀) := hsepE _ hx₁
  have h3 : IsSeparable ↥(modularFunctionFieldC (ZMod q) M') (liftAlgHom ι₁ M' x₀) :=
    IsSeparable.of_algebra_isSeparable_of_isSeparable ↥(modularFunctionFieldC (ZMod q) M') h2
  exact (isSeparable_map_iff (liftAlgHom ι₁ M') (liftAlgHom_injective ι₁ M')).mp h3

end PrimeField

end ModularCurve.IgSepKappaAux

p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC~coeffMap_jqModC~coeffMap_jqNModC" in open _root_.P2MW.S_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP.ModularCurve ModularCurve.IgSepKappaAux in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (κ : Type) [Field κ] [CharP κ q] :
    ∀ x ∈ ModularCurve.xHFunctionFieldC κ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'),
      IsSeparable (↥(ModularCurve.modularFunctionFieldC κ M')) x := by
  classical
  intro x hx
  let ι : ZMod q →+* κ := ZMod.castHom (dvd_refl q) κ

  have hgen : ∀ s ∈ intFormRatiosC κ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
      IsSeparable ↥(modularFunctionFieldC κ M') s := by
    intro s hs
    rw [← image_intFormRatiosC_eq ι] at hs
    obtain ⟨x₀, hx₀, rfl⟩ := hs
    exact isSeparable_coeffMap_of_isSeparable ι M' (isSeparable_of_mem_intFormRatiosC_zmod q hq M' hqM' hx₀)

  let T : IntermediateField ↥(modularFunctionFieldC κ M') (LaurentSeries κ) :=
    IntermediateField.adjoin _ (intFormRatiosC κ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
  haveI : Algebra.IsSeparable ↥(modularFunctionFieldC κ M') ↥T :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable (F := ↥(modularFunctionFieldC κ M'))
      (S := intFormRatiosC κ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))).mpr hgen
  have hxT : x ∈ T := by
    have hx' : x ∈ qExpFunctionFieldC κ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) := hx
    have hle : qExpFunctionFieldC κ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) ≤ T.restrictScalars κ :=
      IntermediateField.adjoin_le_iff.mpr fun s hs =>
        (IntermediateField.mem_restrictScalars κ).mpr (IntermediateField.subset_adjoin _ _ hs)
    exact (IntermediateField.mem_restrictScalars κ).mp (hle hx')
  have h := Algebra.IsSeparable.isSeparable ↥(modularFunctionFieldC κ M') (⟨x, hxT⟩ : ↥T)
  simpa only [IntermediateField.coe_val] using h.map T.val (fun _ _ e => Subtype.ext e)

end
end S_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP
end P2MW
export P2MW.S_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP (solution)
