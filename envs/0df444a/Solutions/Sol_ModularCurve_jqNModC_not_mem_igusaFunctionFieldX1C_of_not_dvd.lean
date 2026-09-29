-- Prove2me | solution 1 for ModularCurve.jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/745ec06b-0a31-5210-81ea-6023dea43010

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_IgusaFunctionField
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_lift_fixedField_range_act_eq_x1FunctionFieldC_and_isGalois_igusaFunctionFieldX1C
import Theorems.Thm_ModularCurve_nonempty_igusaDiamondDataX1C
import Theorems.Thm_ModularCurve_exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C
import Theorems.Thm_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace W1Assembly

open ModularCurve Polynomial

theorem coeff_neg_one_eq_zero_of_mem_range_qExpand {K : Type*} [Field K] (ℓ : ℕ) [NeZero ℓ] (hℓ : 2 ≤ ℓ)
    {z : LaurentSeries K} (hz : z ∈ Set.range (qExpand K ℓ)) : z.coeff (-1) = 0 := by
  obtain ⟨x, rfl⟩ := hz
  refine qExpand_coeff_of_not_dvd ℓ x ?_
  intro h
  have h1 : ((ℓ : ℕ) : ℤ) ∣ 1 := (Int.dvd_neg).mp h
  have h2 : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
  omega

theorem coeff_neg_one_jqModC (K : Type*) [Field K] : (jqModC K).coeff (-1) = 1 := by
  rw [jqModC, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]

theorem coeff_neg_one_qTwist_jqModC_ne_zero {K : Type*} [Field K] (u : Kˣ) :
    (qTwist u (jqModC K)).coeff (-1) ≠ 0 := by
  rw [qTwist_coeff, coeff_neg_one_jqModC, mul_one]
  exact Units.ne_zero _

theorem exists_mem_of_roots_le {R : Type*} [CommRing R] [IsDomain R] (m : R[X]) (S : Set R)
    (hS : ∀ r ∈ m.roots, r ∈ S) (hcard : 2 ≤ m.roots.card)
    (ℓ : ℕ) (t : ℕ → R) (yt : R) (hle : m.roots ≤ (Finset.range ℓ).val.map t + {yt}) :
    ∃ k, k < ℓ ∧ t k ∈ S := by
  classical
  by_contra hno
  push Not at hno

  have hall : ∀ r ∈ m.roots, r = yt := by
    intro r hr
    have hr' : r ∈ (Finset.range ℓ).val.map t + {yt} := Multiset.mem_of_le hle hr
    rw [Multiset.mem_add, Multiset.mem_map, Multiset.mem_singleton] at hr'
    rcases hr' with ⟨k, hk, rfl⟩ | h
    · exact absurd (hS _ hr) (hno k (by simpa using hk))
    · exact h

  have h1 : m.roots = Multiset.replicate m.roots.card yt := Multiset.eq_replicate_card.mpr hall
  have hcnt : Multiset.count yt m.roots = m.roots.card := by
    conv_lhs => rw [h1]
    rw [Multiset.count_replicate_self]
  have h2 : 2 ≤ Multiset.count yt ((Finset.range ℓ).val.map t + {yt}) := by
    calc 2 ≤ m.roots.card := hcard
      _ = Multiset.count yt m.roots := hcnt.symm
      _ ≤ _ := Multiset.count_le_of_le _ hle
  rw [Multiset.count_add, Multiset.count_singleton_self] at h2
  have h3 : 0 < Multiset.count yt ((Finset.range ℓ).val.map t) := by omega
  rw [Multiset.count_pos, Multiset.mem_map] at h3
  obtain ⟨k, hk, hkt⟩ := h3
  refine absurd ?_ (hno k (by simpa using hk))
  rw [hkt]

  have : yt ∈ m.roots := by
    have hne : m.roots ≠ 0 := by intro h; rw [h] at hcard; simp at hcard
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hne
    rwa [hall r hr] at hr
  exact hS _ this

end W1Assembly

open W1Assembly in

theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hℓM : ¬ ℓ ∣ M) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ModularCurve.jqNModC κ ℓ ∉ ModularCurve.igusaFunctionFieldX1C κ M w := by
  classical
  intro hy
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out

  let K := AlgebraicClosure κ
  haveI : CharP K p := (Algebra.charP_iff κ K p).mp inferInstance
  have hℓK : ((ℓ : ℕ) : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K p ℓ).mp h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp this).symm
  have hMK : ((M : ℕ) : K) ≠ 0 := by
    intro h
    exact hpM ((CharP.cast_eq_zero_iff K p M).mp h)
  obtain ⟨w'⟩ := ModularCurve.nonempty_integralWeightOneForm K M (by omega)
  have hyK : ModularCurve.jqNModC K ℓ ∈ ModularCurve.igusaFunctionFieldX1C K M w' := by
    have h1 : ModularCurve.coeffMap (algebraMap κ K) (ModularCurve.jqNModC κ ℓ) ∈
        IntermediateField.adjoin K (⇑(ModularCurve.coeffMap (algebraMap κ K)) '' (ModularCurve.igusaFunctionFieldX1C κ M w : Set (LaurentSeries κ))) :=
      IntermediateField.subset_adjoin K _ ⟨_, hy, rfl⟩
    rwa [ModularCurve.adjoin_image_coeffMap_igusaFunctionFieldX1C_eq κ K M w w', ModularCurve.coeffMap_jqNModC] at h1

  set E : IntermediateField K (LaurentSeries K) := ModularCurve.x1FunctionFieldC K M with hE
  set Ig : IntermediateField K (LaurentSeries K) := ModularCurve.igusaFunctionFieldX1C K M w' with hIg
  have hEIg : E ≤ Ig := ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C K M w'
  obtain ⟨δ⟩ := ModularCurve.nonempty_igusaDiamondDataX1C p M hM hpM K w'
  letI : Algebra ↥E ↥Ig := (IntermediateField.inclusion hEIg).toRingHom.toAlgebra
  have hgal : IsGalois ↥E ↥Ig :=
    (ModularCurve.lift_fixedField_range_act_eq_x1FunctionFieldC_and_isGalois_igusaFunctionFieldX1C p M hM hpM K w' δ).2

  have hyE : ModularCurve.jqNModC K ℓ ∉ E := by
    have := ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd K M (⊥ : Subgroup (ZMod M)ˣ) hMK ℓ hℓM hℓK
    rwa [ModularCurve.GammaH_bot] at this

  haveI : Normal ↥E ↥Ig := hgal.to_normal
  let yI : ↥Ig := ⟨ModularCurve.jqNModC K ℓ, hyK⟩
  let incl : ↥Ig →ₐ[↥E] LaurentSeries K :=
    { (algebraMap ↥Ig (LaurentSeries K)) with commutes' := fun e => rfl }
  have hinclInj : Function.Injective incl := Subtype.val_injective
  have hint : IsIntegral ↥E yI := Normal.isIntegral inferInstance yI
  have hmI : ((minpoly ↥E yI).map (algebraMap ↥E ↥Ig)).Splits := Normal.splits inferInstance yI
  have hmy : minpoly ↥E (ModularCurve.jqNModC K ℓ) = minpoly ↥E yI := by
    rw [← minpoly.algHom_eq incl hinclInj yI]; rfl
  have hmmonic : (minpoly ↥E (ModularCurve.jqNModC K ℓ)).Monic := by rw [hmy]; exact minpoly.monic hint
  have e1 : (minpoly ↥E (ModularCurve.jqNModC K ℓ)).map (algebraMap ↥E (LaurentSeries K)) =
      ((minpoly ↥E yI).map (algebraMap ↥E ↥Ig)).map (algebraMap ↥Ig (LaurentSeries K)) := by
    rw [Polynomial.map_map, hmy]; rfl
  have hsplit1 : ((minpoly ↥E (ModularCurve.jqNModC K ℓ)).map (algebraMap ↥E (LaurentSeries K))).Splits := by
    rw [e1]; exact hmI.map _

  have hroots1 : ∀ r ∈ ((minpoly ↥E (ModularCurve.jqNModC K ℓ)).map (algebraMap ↥E (LaurentSeries K))).roots,
      r ∈ (Ig : Set (LaurentSeries K)) := by
    intro r hr
    rw [e1, hmI.roots_map, Multiset.mem_map] at hr
    obtain ⟨s, -, rfl⟩ := hr
    exact s.2

  have hdeg : 2 ≤ (minpoly ↥E (ModularCurve.jqNModC K ℓ)).natDegree := by
    rw [hmy, minpoly.two_le_natDegree_iff hint]
    rintro ⟨e, he⟩
    apply hyE
    have : ((algebraMap ↥E ↥Ig e : ↥Ig) : LaurentSeries K) = ModularCurve.jqNModC K ℓ := by rw [he]
    rw [← this]; exact e.2

  let φ : LaurentSeries K →ₐ[K] LaurentSeries K := ModularCurve.qExpandAlgHomC K ℓ
  have hφ : ∀ z, φ z = ModularCurve.qExpand K ℓ z := fun z => rfl
  have hφinj : Function.Injective φ := ModularCurve.qExpand_injective (R := K) (N := ℓ)
  haveI : NeZero ((ℓ : ℕ) : κ) := ⟨fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp ((CharP.cast_eq_zero_iff κ p ℓ).mp h)).symm⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ℓ
  let ζ : Kˣ := (hζ₀.isUnit hℓ.ne_zero).unit
  have hζ : IsPrimitiveRoot (ζ : K) ℓ := by simpa [ζ] using hζ₀
  let F : IntermediateField K (LaurentSeries K) := E.map φ
  have hjE : ModularCurve.jqModC K ∈ E := by
    have h1 : ModularCurve.jqModC K ∈ ModularCurve.modularFunctionFieldFullC K M := ModularCurve.jqModC_mem_full K M
    have h2 := ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 K M h1
    exact ModularCurve.qExpFunctionFieldC_mono K (CongruenceSubgroup.Gamma1_in_Gamma0 M) h2
  haveI : NeZero (ℓ * 1) := ⟨by simpa using hℓ.ne_zero⟩
  haveI : NeZero (ℓ * (ℓ * 1)) := ⟨by simpa using hℓ.ne_zero⟩
  have hmem : ModularCurve.qExpand K (ℓ * 1) (ModularCurve.jqModC K) ∈ F := by
    rw [ModularCurve.qExpand_congr (mul_one ℓ)]
    exact ⟨_, hjE, rfl⟩
  obtain ⟨P, hPmonic, hPdeg, hPmap⟩ :=
    ModularCurve.exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C K ℓ ζ hζ 1 (by
      intro h; exact hℓ.one_lt.ne' (Nat.dvd_one.mp h)) F hmem

  let ψ : ↥E ≃ₐ[K] ↥F := IntermediateField.equivMap E φ
  have hψ : ∀ x : ↥F, φ (((ψ.symm x : ↥E)) : LaurentSeries K) = (x : LaurentSeries K) := fun x => by
    conv_rhs => rw [← ψ.apply_symm_apply x]
    rfl
  have hcomp : (φ.toRingHom.comp (algebraMap ↥E (LaurentSeries K))).comp (ψ.symm : ↥F →+* ↥E) = algebraMap ↥F (LaurentSeries K) :=
    RingHom.ext fun x => hψ x
  have hP₀map : ((P.map (ψ.symm : ↥F →+* ↥E)).map (algebraMap ↥E (LaurentSeries K))).map φ.toRingHom =
      P.map (algebraMap ↥F (LaurentSeries K)) := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomp]
  have hyt : φ (ModularCurve.jqNModC K ℓ) = ModularCurve.qExpand K (ℓ * (ℓ * 1)) (ModularCurve.jqModC K) := by
    rw [hφ, ModularCurve.jqNModC, ModularCurve.qExpand_qExpand, ModularCurve.qExpand_congr (by ring : ℓ * ℓ = ℓ * (ℓ * 1))]
  have hP₀y : Polynomial.aeval (ModularCurve.jqNModC K ℓ) (P.map (ψ.symm : ↥F →+* ↥E)) = 0 := by
    apply hφinj
    have := Polynomial.hom_eval₂ (P.map (ψ.symm : ↥F →+* ↥E)) (algebraMap ↥E (LaurentSeries K)) φ.toRingHom (ModularCurve.jqNModC K ℓ)
    rw [Polynomial.aeval_def, show (φ : LaurentSeries K → LaurentSeries K) = φ.toRingHom from rfl, this, map_zero,
      ← Polynomial.eval_map, ← Polynomial.map_map, hP₀map, hPmap, show φ.toRingHom (ModularCurve.jqNModC K ℓ) = φ _ from rfl, hyt,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, mul_zero]
  have hmP₀ : minpoly ↥E (ModularCurve.jqNModC K ℓ) ∣ P.map (ψ.symm : ↥F →+* ↥E) := minpoly.dvd ↥E _ hP₀y

  have hm₂split : (((minpoly ↥E (ModularCurve.jqNModC K ℓ)).map (algebraMap ↥E (LaurentSeries K))).map φ.toRingHom).Splits :=
    hsplit1.map _
  have hm₂roots : ∀ r ∈ (((minpoly ↥E (ModularCurve.jqNModC K ℓ)).map (algebraMap ↥E (LaurentSeries K))).map φ.toRingHom).roots,
      r ∈ Set.range (ModularCurve.qExpand K ℓ) := by
    intro r hr
    rw [hsplit1.roots_map, Multiset.mem_map] at hr
    obtain ⟨s, -, rfl⟩ := hr
    exact ⟨s, rfl⟩
  have hm₂card : 2 ≤ (((minpoly ↥E (ModularCurve.jqNModC K ℓ)).map (algebraMap ↥E (LaurentSeries K))).map φ.toRingHom).roots.card := by
    rw [(Polynomial.splits_iff_card_roots.mp hm₂split), Polynomial.natDegree_map, Polynomial.natDegree_map]
    exact hdeg
  have hQ0 : P.map (algebraMap ↥F (LaurentSeries K)) ≠ 0 := (hPmonic.map _).ne_zero
  have hle : (((minpoly ↥E (ModularCurve.jqNModC K ℓ)).map (algebraMap ↥E (LaurentSeries K))).map φ.toRingHom).roots ≤
      (P.map (algebraMap ↥F (LaurentSeries K))).roots :=
    Polynomial.roots.le_of_dvd hQ0 (by rw [← hP₀map]; exact Polynomial.map_dvd _ (Polynomial.map_dvd _ hmP₀))
  have hroots_rhs : (P.map (algebraMap ↥F (LaurentSeries K))).roots =
      (Finset.range ℓ).val.map (fun k => ModularCurve.qTwist (ζ ^ k) (ModularCurve.qExpand K 1 (ModularCurve.jqModC K))) +
        {ModularCurve.qExpand K (ℓ * (ℓ * 1)) (ModularCurve.jqModC K)} := by
    rw [hPmap, Polynomial.roots_mul (by rw [← hPmap]; exact hQ0), Polynomial.roots_X_sub_C,
      Polynomial.roots_prod _ _ (by rw [Finset.prod_ne_zero_iff]; exact fun k _ => Polynomial.X_sub_C_ne_zero _)]
    congr 1
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  rw [hroots_rhs] at hle
  obtain ⟨k, hk, hkS⟩ := exists_mem_of_roots_le _ _ hm₂roots hm₂card ℓ
    (fun k => ModularCurve.qTwist (ζ ^ k) (ModularCurve.qExpand K 1 (ModularCurve.jqModC K))) _ hle

  rw [ModularCurve.qExpand_one_apply] at hkS
  exact coeff_neg_one_qTwist_jqModC_ne_zero (ζ ^ k) (coeff_neg_one_eq_zero_of_mem_range_qExpand ℓ hℓ.two_le hkS)

end S_ModularCurve_jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd (solution)
