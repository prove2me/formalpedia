-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_family_liftIndep_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/4bdd1d66-8ce3-578d-a2fa-910cf2103d6d

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio
import Theorems.Thm_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_FullLevel_residue_mem_qExpFunctionFieldC_gamma0_and_surj
import Theorems.Thm_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_family_liftIndep_gamma0
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.jqNModC_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_exists_family_liftIndep_gamma0.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_family_liftIndep_gamma0.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups ArithmeticFunction.sigma

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH intSeriesC qExpFunctionFieldC qExpFunctionFieldC_mono x1FunctionFieldC dedekindEtaUnit constantCoeff_dedekindEtaUnit ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single laurentBaseChange FullLevel.exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC FullLevel.residue_mem_qExpFunctionFieldC_gamma0_and_surj eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio residue_mem_qExpFunctionFieldC_gamma0_and_surj"
namespace LiftIndep
p2m_open "ModularCurve.FullLevel ModularCurve"

variable {L : Type*} [Field L] (A : ValuationSubring L)

private def intSeriesA (p : PowerSeries ℤ) : LaurentSeries A :=
  HahnSeries.ofPowerSeries ℤ A (p.map (Int.castRingHom A))

private theorem coeffMap_subtype_intSeriesA (p : PowerSeries ℤ) :
    coeffMap A.subtype (intSeriesA A p) = intSeriesC L p := by
  ext n
  simp only [intSeriesA, intSeriesC, coeffMap_coeff]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · rw [ofPowerSeries_coeff_of_neg _ (not_le.mp hn), ofPowerSeries_coeff_of_neg _ (not_le.mp hn), map_zero]

private theorem coeffMap_residue_intSeriesA (p : PowerSeries ℤ) :
    coeffMap (IsLocalRing.residue A) (intSeriesA A p) = intSeriesC (ResidueField A) p := by
  ext n
  simp only [intSeriesA, intSeriesC, coeffMap_coeff]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · rw [ofPowerSeries_coeff_of_neg _ (not_le.mp hn), ofPowerSeries_coeff_of_neg _ (not_le.mp hn), map_zero]

private theorem coeffMap_subtype_injective :
    Function.Injective (coeffMap A.subtype : LaurentSeries A → LaurentSeries L) := by
  intro x y h
  apply HahnSeries.ext
  funext k
  have := congrArg (fun s : LaurentSeries L => s.coeff k) h
  simp only [coeffMap_coeff] at this
  exact Subtype.ext this

private theorem coeffMap_subtype_C (a : A) :
    coeffMap A.subtype (HahnSeries.C a) = algebraMap L (LaurentSeries L) (a : L) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]
  rfl

private theorem coeffMap_residue_C (a : A) :
    coeffMap (IsLocalRing.residue A) (HahnSeries.C a) = HahnSeries.C (IsLocalRing.residue A a) := by
  rw [HahnSeries.C_apply, coeffMap_single, HahnSeries.C_apply]

private theorem charP_residueField (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) : CharP (ResidueField A) q := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr
  have hmem : (⟨(q : AlgebraicClosure ℚ), natCast_mem A q⟩ : A) ∈ maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA
  have : IsLocalRing.residue A ⟨(q : AlgebraicClosure ℚ), natCast_mem A q⟩ = 0 := (residue_eq_zero_iff _).mpr hmem
  rw [← map_natCast (IsLocalRing.residue A) q]
  convert this
  rfl

private theorem Gamma1_le_Gamma0_of_dvd {M' M : ℕ} (h : M' ∣ M) : Gamma1 M ≤ Gamma0 M' := by
  intro γ hγ
  rw [Gamma1_mem] at hγ
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have := hγ.2.2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  exact (Int.natCast_dvd_natCast.mpr h).trans this

end ModularCurve.FullLevel.LiftIndep

end

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_exists_family_liftIndep_gamma0.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_family_liftIndep_gamma0.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup P2MW.S_ModularCurve_FullLevel_exists_family_liftIndep_gamma0.ModularCurve.FullLevel.LiftIndep"
open scoped MatrixGroups ArithmeticFunction.sigma

@[reducible] noncomputable def instAlgResFb (A : ValuationSubring (AlgebraicClosure ℚ)) (Γ : Subgroup SL(2, ℤ)) :
    Algebra (ResidueField A) (qExpFunctionFieldC (ResidueField A) Γ) := inferInstance
@[reducible] noncomputable def instAlgLF (Γ : Subgroup SL(2, ℤ)) :
    Algebra (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := inferInstance
attribute [local instance] instAlgResFb instAlgLF

namespace ValSub
private theorem _root_.ValSub.coe_sum_mul_pow {K : Type*} [Field K] (O : ValuationSubring K) {a : ℕ} (d : Fin a → O) (u : O) :
    ((∑ i, d i * u ^ (i : ℕ) : O) : K) = ∑ i, (d i : K) * (u : K) ^ (i : ℕ) := by
  simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]

end ValSub
p2m_export "" "ValSub.coe_sum_mul_pow"
namespace IntField
private theorem _root_.IntField.coe_sum_mul_pow {K L' : Type*} [Field K] [Field L'] [Algebra K L']
    (E : IntermediateField K L')
    {a : ℕ} (e : Fin a → E) (g : E) :
    ((∑ i, e i * g ^ (i : ℕ) : E) : L') = ∑ i, (e i : L') * (g : L') ^ (i : ℕ) := by
  simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]

end IntField
p2m_export "" "IntField.coe_sum_mul_pow"
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (R : RegularProlongation A (fieldBar q M')
      (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))))
    (hq : 5 ≤ q) (hqM' : ¬ q ∣ M') (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y) :
    ∃ (a : ℕ) (u : Fin a → fieldBar q M'), (∀ i, u i ∈ R.integers) ∧ q - 1 < 4 * a ∧
      ∀ d : Fin a → fieldBar q M', (∀ i, d i ∈ R.integers ∧
        (d i : LaurentSeries (AlgebraicClosure ℚ)) ∈
          laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) →
        R.integers.valuation (∑ i, d i * u i) < 1 → ∀ i, R.integers.valuation (d i) < 1 := by
  classical
  haveI hκ : CharP (ResidueField A) q := charP_residueField q A hA

  let Fb := qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))

  obtain ⟨u, X, Y, huY, hred⟩ :=
    ModularCurve.FullLevel.exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio q hq M'
  obtain ⟨hY0, hXY⟩ := hred (ResidueField A)

  have huYA : (u : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype (intSeriesA A Y) =
      coeffMap A.subtype (intSeriesA A X) := by
    rw [coeffMap_subtype_intSeriesA, coeffMap_subtype_intSeriesA]; exact huY
  have hYA0 : coeffMap (IsLocalRing.residue A) (intSeriesA A Y) ≠ 0 := by
    rw [coeffMap_residue_intSeriesA]; exact hY0
  have huO : u ∈ R.integers := (hR u).mpr ⟨_, _, hYA0, huYA⟩

  have hΔ0 : intSeriesC (ResidueField A) (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
    intro h
    have h1 := congrArg (fun z : LaurentSeries (ResidueField A) => z.coeff 1) h
    simp only [intSeriesC, HahnSeries.coeff_zero] at h1
    have h2 : (HahnSeries.ofPowerSeries ℤ (ResidueField A)
        ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom (ResidueField A)))).coeff ((1 : ℕ) : ℤ) = 1 := by
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
    rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
    rw [h2] at h1
    exact one_ne_zero h1
  have hmk : ∀ c : ℕ → ℤ,
      intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else c n) ≠ 0 := by
    intro c h
    have h1 := congrArg (fun z : LaurentSeries (ResidueField A) => z.coeff 0) h
    simp only [intSeriesC, HahnSeries.coeff_zero] at h1
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_mk, if_pos rfl, map_one] at h1
    exact one_ne_zero h1
  have hP0 : intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
      intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)) ≠ 0 :=
    mul_ne_zero (hmk _) (hmk _)
  have hX0 : intSeriesC (ResidueField A) X ≠ 0 := by
    intro h; apply mul_ne_zero hY0 hP0; rw [← hXY, h, zero_mul]

  have hu0 : u ≠ 0 := by
    intro h
    apply hX0
    have : intSeriesC (AlgebraicClosure ℚ) X = 0 := by rw [← huY, h, ZeroMemClass.coe_zero, zero_mul]
    have hXA : intSeriesA A X = 0 :=
      coeffMap_subtype_injective A (by rw [coeffMap_subtype_intSeriesA, this, map_zero])
    rw [← coeffMap_residue_intSeriesA, hXA, map_zero]

  obtain ⟨c, x, y, hc0, hx0, hy0, hxF, hyF, hcxy⟩ :=
    ModularCurve.exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (ModularCurve.translation_mem_GammaH _ _) u hu0
  obtain ⟨hyO, hyres⟩ := hpin y hyF
  obtain ⟨hxO, hxres⟩ := hpin x hxF

  have hconst_mem : ∀ a : A, (algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ)) ∈
      R.integers := fun a => (R.algebraMap_mem_iff _).mpr a.2
  have hconst_coe : ∀ z : AlgebraicClosure ℚ,
      ((algebraMap (AlgebraicClosure ℚ) (fieldBar q M') z : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) z := fun _ => rfl

  have hcA : c ∈ A := by
    by_contra hcA
    have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    have hgt : 1 < A.valuation c := lt_of_not_ge fun h => hcA ((A.valuation_le_one_iff c).mp h)
    have hcim : (⟨c⁻¹, hci⟩ : A) ∈ maximalIdeal A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      show A.valuation c⁻¹ < 1
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hgt
    have hres0 : IsLocalRing.residue A ⟨c⁻¹, hci⟩ = 0 := (residue_eq_zero_iff _).mpr hcim

    have heq : (⟨_, hconst_mem ⟨c⁻¹, hci⟩⟩ : R.integers) * (⟨u, huO⟩ * ⟨_, hyO⟩) = ⟨_, hxO⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c⁻¹ *
        ((u : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y) = coeffMap A.subtype x
      rw [hcxy, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
    have := congrArg R.residue heq
    rw [map_mul, R.residue_algebraMap, hres0, map_zero, zero_mul] at this
    apply hx0
    rw [← hxres, ← this]
    rfl

  set cA : A := ⟨c, hcA⟩ with hcA_def
  have heq1 : (⟨u, huO⟩ : R.integers) * ⟨_, hyO⟩ = ⟨_, hconst_mem cA⟩ * ⟨_, hxO⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    show (u : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c * coeffMap A.subtype x
    exact hcxy
  have hres1 := congrArg (fun z : Fb => (z : LaurentSeries (ResidueField A))) (congrArg R.residue heq1)
  simp only [map_mul, R.residue_algebraMap] at hres1
  rw [IntermediateField.coe_mul, IntermediateField.coe_mul, hyres, hxres] at hres1
  have halg : ((algebraMap (ResidueField A) Fb (IsLocalRing.residue A cA) : Fb) : LaurentSeries (ResidueField A)) =
      HahnSeries.C (IsLocalRing.residue A cA) := by
    change algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A cA) = _
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  rw [halg] at hres1

  have hA1 : intSeriesA A X * y = HahnSeries.C cA * x * intSeriesA A Y := by
    apply coeffMap_subtype_injective A
    rw [map_mul, map_mul, map_mul, coeffMap_subtype_C, ← huYA, mul_assoc,
      mul_comm (coeffMap A.subtype _) (coeffMap A.subtype y),
      ← mul_assoc, hcxy]
  have hred1 := congrArg (coeffMap (IsLocalRing.residue A)) hA1
  rw [map_mul, map_mul, map_mul, coeffMap_residue_intSeriesA, coeffMap_residue_intSeriesA, coeffMap_residue_C]
    at hred1

  have hresY : ((R.residue ⟨u, huO⟩ : Fb) : LaurentSeries (ResidueField A)) * intSeriesC (ResidueField A) Y =
      intSeriesC (ResidueField A) X := by
    apply mul_right_cancel₀ hy0
    calc ((R.residue ⟨u, huO⟩ : Fb) : LaurentSeries (ResidueField A)) * intSeriesC (ResidueField A) Y *
          coeffMap (IsLocalRing.residue A) y
        = ((R.residue ⟨u, huO⟩ : Fb) : LaurentSeries (ResidueField A)) * coeffMap (IsLocalRing.residue A) y *
          intSeriesC (ResidueField A) Y := by ring
      _ = HahnSeries.C (IsLocalRing.residue A cA) * coeffMap (IsLocalRing.residue A) x *
          intSeriesC (ResidueField A) Y := by rw [hres1]
      _ = intSeriesC (ResidueField A) X * coeffMap (IsLocalRing.residue A) y := hred1.symm

  have hresu : ((R.residue ⟨u, huO⟩ : Fb) : LaurentSeries (ResidueField A)) =
      intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
          intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)) /
        intSeriesC (ResidueField A) (PowerSeries.X * dedekindEtaUnit) := by
    rw [eq_div_iff hΔ0]
    apply mul_left_cancel₀ hY0
    calc intSeriesC (ResidueField A) Y * (((R.residue ⟨u, huO⟩ : Fb) : LaurentSeries (ResidueField A)) *
          intSeriesC (ResidueField A) (PowerSeries.X * dedekindEtaUnit))
        = ((R.residue ⟨u, huO⟩ : Fb) : LaurentSeries (ResidueField A)) * intSeriesC (ResidueField A) Y *
            intSeriesC (ResidueField A) (PowerSeries.X * dedekindEtaUnit) := by ring
      _ = intSeriesC (ResidueField A) X * intSeriesC (ResidueField A) (PowerSeries.X * dedekindEtaUnit) := by
          rw [hresY]
      _ = _ := hXY

  have hodd : q % 2 = 1 := (Fact.out : q.Prime).eq_two_or_odd.resolve_left (by omega)
  refine ⟨(q - 1) / 2, fun i => u ^ (i : ℕ), fun i => pow_mem huO _, by omega, ?_⟩
  intro d hd hlt i

  let M : ℕ := if q = 5 then 7 * M' else 5 * M'
  have hM0 : 0 < M' := Nat.pos_of_ne_zero (NeZero.ne M')
  haveI : NeZero M := ⟨by simp only [M]; split_ifs <;> omega⟩
  have hM5 : 5 ≤ M := by simp only [M]; split_ifs <;> omega
  have hdvdM : M' ∣ M := by simp only [M]; split_ifs <;> exact Dvd.intro_left _ rfl
  have hqM : ¬ q ∣ M := by
    simp only [M]
    have hp : q.Prime := Fact.out
    split_ifs with h5
    · subst h5
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h7 | hM'
      · norm_num at h7
      · exact hqM' hM'
    · intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h7 | hM'
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7
        exact h5 this
      · exact hqM' hM'

  let dO : Fin ((q - 1) / 2) → R.integers := fun i => ⟨d i, (hd i).1⟩
  let uO : R.integers := ⟨u, huO⟩
  have hsum : (∑ i, d i * u ^ (i : ℕ) : fieldBar q M') = ((∑ i, dO i * uO ^ (i : ℕ) : R.integers) : fieldBar q M') :=
    (ValSub.coe_sum_mul_pow R.integers dO uO).symm
  have hmax : (∑ i, dO i * uO ^ (i : ℕ) : R.integers) ∈ maximalIdeal R.integers := by
    rw [ValuationSubring.valuation_lt_one_iff]
    rw [hsum] at hlt
    exact hlt
  have hres0 : R.residue (∑ i, dO i * uO ^ (i : ℕ)) = 0 := by
    have : (∑ i, dO i * uO ^ (i : ℕ) : R.integers) ∈ RingHom.ker R.residue := by rw [R.ker_residue]; exact hmax
    exact this
  rw [map_sum] at hres0
  simp only [map_mul, map_pow] at hres0
  let e : Fin ((q - 1) / 2) → LaurentSeries (ResidueField A) :=
    fun j => ((R.residue (dO j) : Fb) : LaurentSeries (ResidueField A))
  have he : ∀ j, e j ∈ x1FunctionFieldC (ResidueField A) M := by
    intro j
    have hE0 := (ModularCurve.FullLevel.residue_mem_qExpFunctionFieldC_gamma0_and_surj q M' A R hA hR hpin).1
      (d j) (hd j).1 (hd j).2
    exact qExpFunctionFieldC_mono (ResidueField A) (Gamma1_le_Gamma0_of_dvd hdvdM) hE0
  have hcomb : ∑ j, e j *
      (intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
          intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)) /
        intSeriesC (ResidueField A) (PowerSeries.X * dedekindEtaUnit)) ^ (j : ℕ) = 0 := by
    have h := congrArg (fun z : Fb => (z : LaurentSeries (ResidueField A))) hres0
    rw [IntField.coe_sum_mul_pow, ZeroMemClass.coe_zero] at h
    rw [← hresu]
    exact h
  have hej : e i = 0 :=
    ModularCurve.eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC q hq (ResidueField A)
      M hM5 hqM e he hcomb i

  have hdi : R.residue (dO i) = 0 := by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact hej
  have hker : dO i ∈ maximalIdeal R.integers := by
    rw [← R.ker_residue]; exact hdi
  exact (ValuationSubring.valuation_lt_one_iff R.integers (dO i)).mp hker

end S_ModularCurve_FullLevel_exists_family_liftIndep_gamma0
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_family_liftIndep_gamma0 (solution)
