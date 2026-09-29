-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/85192af7-5916-568f-a649-bb0699fe3917

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div
import Theorems.Thm_ModularCurve_FullLevel_algebraMap_mem_gauss_iff_of_levelH
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.FullLevel.SemistableCovering.instAlgebraSS ModularCurve.FullLevel.SemistableCovering.instFieldIg ModularCurve.FullLevel.SemistableCovering.instFieldSS ModularCurve.FullLevel.SemistableCovering.instAlgebraIg"
p2m_attr_erase "instance" "CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta"
p2m_attr_erase "simp" "ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.FullLevel.SemistableCovering.mk.sizeOf_spec ModularCurve.FullLevel.SemistableCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

open scoped MatrixGroups

namespace IgSepAux

open ModularCurve HahnSeries

section Aprime

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {L : Type} [Field L] [Algebra A L]
  [IsFractionRing A L]

noncomputable def Ap (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (L : Type) [Field L] [Algebra A L]
    [IsFractionRing A L] : ValuationSubring L where
  toSubring := (algebraMap A L).range
  mem_or_inv_mem' := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨a, ha⟩

theorem mem_Ap_iff (x : L) : x ∈ Ap A L ↔ ∃ a : A, algebraMap A L a = x := Iff.rfl

noncomputable def eAp : A ≃+* ↥(Ap A L) :=
  RingEquiv.ofBijective ((algebraMap A L).rangeRestrict) ⟨by
      intro a b h
      exact IsFractionRing.injective A L (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩

@[scoped simp] theorem coe_eAp (a : A) : ((eAp (L := L) a : ↥(Ap A L)) : L) = algebraMap A L a := rfl

theorem subtype_comp_eAp : (Ap A L).subtype.comp (eAp (A := A) (L := L)).toRingHom = algebraMap A L := by
  ext a; rfl

theorem residue_eAp_eq_zero_iff (a : A) :
    IsLocalRing.residue ↥(Ap A L) (eAp (L := L) a) = 0 ↔ IsLocalRing.residue A a = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
  exact not_congr (MulEquiv.isUnit_map (eAp (A := A) (L := L)))

theorem charP_residueField_Ap (q : ℕ) [Fact q.Prime] (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) :
    CharP (IsLocalRing.ResidueField ↥(Ap A L)) q := by
  rw [CharP.charP_iff_prime_eq_zero Fact.out]
  have h : IsLocalRing.residue A (q : A) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hAq
  have h2 : IsLocalRing.residue ↥(Ap A L) (eAp (L := L) (q : A)) = 0 := (residue_eAp_eq_zero_iff _).mpr h
  simpa using h2

end Aprime

section Bridge

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {L : Type} [Field L] [Algebra A L]
  [IsFractionRing A L]

def GaussP (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {L : Type} [Field L] [Algebra A L]
    [IsFractionRing A L] (s : LaurentSeries L) : Prop :=
  ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
    s * ofPowerSeries ℤ L (y.map (algebraMap A L)) = ofPowerSeries ℤ L (x.map (algebraMap A L))

def GaussL (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (L : Type) [Field L] [Algebra A L]
    [IsFractionRing A L] (s : LaurentSeries L) : Prop :=
  ∃ x y : LaurentSeries ↥(Ap A L), coeffMap (IsLocalRing.residue ↥(Ap A L)) y ≠ 0 ∧
    s * coeffMap (Ap A L).subtype y = coeffMap (Ap A L).subtype x

private noncomputable def _root_.IgSepAux.lift (x : PowerSeries A) : LaurentSeries ↥(Ap A L) :=
  coeffMap (eAp (A := A) (L := L)).toRingHom (ofPowerSeries ℤ A x)

p2m_export "IgSepAux" "lift"
theorem coeffMap_subtype_lift (x : PowerSeries A) :
    coeffMap (Ap A L).subtype (lift (L := L) x) = ofPowerSeries ℤ L (x.map (algebraMap A L)) := by
  rw [lift, coeffMap_coeffMap, subtype_comp_eAp, coeffMap_ofPowerSeries]

theorem powerSeries_map_ne_zero_iff {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (y : PowerSeries R) :
    y.map f ≠ 0 ↔ ∃ n, f (PowerSeries.coeff n y) ≠ 0 := by
  rw [Ne, PowerSeries.ext_iff, not_forall]
  simp [PowerSeries.coeff_map]

theorem coeffMap_residue_lift_ne_zero_iff (y : PowerSeries A) :
    coeffMap (IsLocalRing.residue ↥(Ap A L)) (lift (L := L) y) ≠ 0 ↔ y.map (IsLocalRing.residue A) ≠ 0 := by
  rw [lift, coeffMap_coeffMap, coeffMap_ofPowerSeries, Ne, HahnSeries.ofPowerSeries_injective.eq_iff' (map_zero _),
    ← Ne, powerSeries_map_ne_zero_iff, powerSeries_map_ne_zero_iff]
  refine exists_congr fun n => not_congr ?_
  exact residue_eAp_eq_zero_iff _

theorem GaussL_of_GaussP {s : LaurentSeries L} (h : GaussP A s) : GaussL A L s := by
  obtain ⟨x, y, hy, hxy⟩ := h
  exact ⟨lift x, lift y, (coeffMap_residue_lift_ne_zero_iff y).mpr hy,
    by rw [coeffMap_subtype_lift, coeffMap_subtype_lift]; exact hxy⟩

noncomputable def desc (X : PowerSeries ↥(Ap A L)) : PowerSeries A := X.map (eAp (A := A) (L := L)).symm.toRingHom

theorem lift_desc (X : PowerSeries ↥(Ap A L)) : lift (L := L) (desc X) = ofPowerSeries ℤ _ X := by
  rw [lift, coeffMap_ofPowerSeries, desc]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem coeffMap_residue_single_mul_ofPowerSeries_ne_zero {k : ℤ} {Y : PowerSeries ↥(Ap A L)}
    (h : coeffMap (IsLocalRing.residue ↥(Ap A L)) (single k 1 * ofPowerSeries ℤ _ Y) ≠ 0) :
    Y.map (IsLocalRing.residue ↥(Ap A L)) ≠ 0 := by
  intro h0
  apply h
  rw [map_mul, coeffMap_ofPowerSeries, h0, map_zero, mul_zero]

theorem GaussP_of_GaussL {s : LaurentSeries L} (h : GaussL A L s) : GaussP A s := by
  obtain ⟨x, y, hy, hxy⟩ := h

  set X := x.powerSeriesPart with hX
  set Y := y.powerSeriesPart with hY
  have hx' : ofPowerSeries ℤ _ X = single (-x.order) 1 * x := LaurentSeries.ofPowerSeries_powerSeriesPart x
  have hy' : ofPowerSeries ℤ _ Y = single (-y.order) 1 * y := LaurentSeries.ofPowerSeries_powerSeriesPart y
  have hxe : x = single x.order 1 * ofPowerSeries ℤ _ X := by
    rw [hx', ← mul_assoc, single_mul_single, add_neg_cancel, one_mul]
    exact (one_mul x).symm.trans (by rfl)
  have hye : y = single y.order 1 * ofPowerSeries ℤ _ Y := by
    rw [hy', ← mul_assoc, single_mul_single, add_neg_cancel, one_mul]
    exact (one_mul y).symm.trans (by rfl)
  have hYne : Y.map (IsLocalRing.residue ↥(Ap A L)) ≠ 0 :=
    coeffMap_residue_single_mul_ofPowerSeries_ne_zero (by rw [← hye]; exact hy)

  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, (a : ℤ) - b = x.order - y.order := ⟨_, _, Int.toNat_sub_toNat_neg _⟩
  have hexp : (b : ℤ) - y.order + x.order = a := by omega

  set P : PowerSeries ↥(Ap A L) := PowerSeries.X ^ a * X
  set Q : PowerSeries ↥(Ap A L) := PowerSeries.X ^ b * Y
  have hQ : Q.map (IsLocalRing.residue ↥(Ap A L)) ≠ 0 := by
    intro h0
    apply hYne
    have : (PowerSeries.X ^ b * Y.map (IsLocalRing.residue ↥(Ap A L))) = PowerSeries.X ^ b * 0 := by
      rw [mul_zero, ← h0, map_mul, map_pow, PowerSeries.map_X]
    exact PowerSeries.X_pow_mul_injective this
  have key : s * coeffMap (Ap A L).subtype (ofPowerSeries ℤ _ Q) = coeffMap (Ap A L).subtype (ofPowerSeries ℤ _ P) := by

    have h1 := congrArg (fun z => z * coeffMap (Ap A L).subtype (single ((b : ℤ) - y.order) 1)) hxy
    rw [mul_assoc, ← map_mul, ← map_mul] at h1
    have e1 : y * single ((b : ℤ) - y.order) 1 = ofPowerSeries ℤ _ Q := by
      rw [show Q = PowerSeries.X ^ b * Y from rfl, map_mul, ofPowerSeries_X_pow]
      calc y * single ((b : ℤ) - y.order) 1
          = (single y.order 1 * ofPowerSeries ℤ _ Y) * single ((b : ℤ) - y.order) 1 := by rw [← hye]
        _ = single (b : ℤ) 1 * ofPowerSeries ℤ _ Y := by
          rw [mul_comm, ← mul_assoc, single_mul_single, mul_one, sub_add_cancel]
    have e2 : x * single ((b : ℤ) - y.order) 1 = ofPowerSeries ℤ _ P := by
      rw [show P = PowerSeries.X ^ a * X from rfl, map_mul, ofPowerSeries_X_pow]
      calc x * single ((b : ℤ) - y.order) 1
          = (single x.order 1 * ofPowerSeries ℤ _ X) * single ((b : ℤ) - y.order) 1 := by rw [← hxe]
        _ = single (a : ℤ) 1 * ofPowerSeries ℤ _ X := by
          rw [mul_comm, ← mul_assoc, single_mul_single, mul_one, hexp]
    rw [e1, e2] at h1
    exact h1
  refine ⟨desc P, desc Q, ?_, ?_⟩
  · have := (coeffMap_residue_lift_ne_zero_iff (L := L) (desc Q)).mp
    rw [lift_desc] at this
    exact this (by rw [coeffMap_ofPowerSeries]; exact fun h0 => hQ (HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)))
  · rw [← coeffMap_subtype_lift, ← coeffMap_subtype_lift, lift_desc, lift_desc]
    exact key

theorem GaussP_iff_GaussL (s : LaurentSeries L) : GaussP A s ↔ GaussL A L s := ⟨GaussL_of_GaussP, GaussP_of_GaussL⟩

end Bridge

theorem valuationSubring_isUnit_iff_inv_mem {F : Type} [Field F] (V : ValuationSubring F) (x : ↥V) (hx : (x : F) ≠ 0) :
    IsUnit x ↔ (x : F)⁻¹ ∈ V := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : ((u : ↥V) : F) * (((u⁻¹ : (↥V)ˣ) : ↥V) : F) = ((1 : ↥V) : F) := congrArg Subtype.val u.mul_inv
    rw [← eq_inv_of_mul_eq_one_right h]
    exact ((u⁻¹ : (↥V)ˣ) : ↥V).2
  · intro h
    exact ⟨⟨x, ⟨(x : F)⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ hx), Subtype.ext (inv_mul_cancel₀ hx)⟩, rfl⟩

end IgSepAux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH.IgSepAux"

theorem IgSepAux.coeffMap_qExpand {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : ModularCurve.coeffMap f (ModularCurve.qExpand R n x) = ModularCurve.qExpand S n (ModularCurve.coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, ModularCurve.coeffMap_coeff]
  · rw [ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_of_not_dvd _ _ hk,
      ModularCurve.qExpand_coeff_of_not_dvd _ _ hk, map_zero]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle : K₀ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (O₀ : ValuationSubring ↥K₀)
    (hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    ∀ (τ : ↥K ≃ₐ[L] ↥K) (hτ : ∀ x : ↥K₀, τ (algebraMap ↥K₀ ↥K x) = algebraMap ↥K₀ ↥K x),
      ∃ hB : ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ W₀.comap τ.toAlgHom.toRingHom ↔ x ∈ O₀,
        letI : Algebra ↥O₀ ↥(W₀.comap τ.toAlgHom.toRingHom) :=
          (((algebraMap ↥K₀ ↥K).comp O₀.subtype).codRestrict (W₀.comap τ.toAlgHom.toRingHom).toSubring
            fun a => (hB a).mpr a.2).toAlgebra
        ∃ _ : IsLocalHom (algebraMap ↥O₀ ↥(W₀.comap τ.toAlgHom.toRingHom)),
          Algebra.IsSeparable (IsLocalRing.ResidueField ↥O₀) (IsLocalRing.ResidueField ↥(W₀.comap τ.toAlgHom.toRingHom)) := by
  intro τ hτ
  letI algK : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have algK_apply : ∀ x : ↥K₀, ((algebraMap ↥K₀ ↥K x : ↥K) : LaurentSeries L) = (x : LaurentSeries L) := fun _ => rfl

  have hW0 : ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ W₀ ↔ x ∈ O₀ :=
    ModularCurve.FullLevel.algebraMap_mem_gauss_iff_of_levelH q hq M' hqM' L ζ hζ K hK K₀ hK₀ hle A hAq hζA W₀ hW₀ O₀ hO₀
  have memB : ∀ f : ↥K, f ∈ W₀.comap τ.toAlgHom.toRingHom ↔ τ f ∈ W₀ := fun f => ValuationSubring.mem_comap
  have hB : ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ W₀.comap τ.toAlgHom.toRingHom ↔ x ∈ O₀ := by
    intro x
    rw [memB, hτ x]
    exact hW0 x
  refine ⟨hB, ?_⟩
  set B : ValuationSubring ↥K := W₀.comap τ.toAlgHom.toRingHom with hBdef
  letI algOB : Algebra ↥O₀ ↥B :=
    (((algebraMap ↥K₀ ↥K).comp O₀.subtype).codRestrict B.toSubring fun a => (hB a).mpr a.2).toAlgebra
  have algOB_apply : ∀ a : ↥O₀, ((algebraMap ↥O₀ ↥B a : ↥B) : ↥K) = algebraMap ↥K₀ ↥K (a : ↥K₀) := fun _ => rfl
  have hinjK : Function.Injective (algebraMap ↥K₀ ↥K) := (algebraMap ↥K₀ ↥K).injective

  have hloc : IsLocalHom (algebraMap ↥O₀ ↥B) := by
    refine ⟨fun a ha => ?_⟩
    have ha0 : (a : ↥K₀) ≠ 0 := by
      intro h0
      have : algebraMap ↥O₀ ↥B a = 0 := Subtype.ext (by rw [algOB_apply, h0, map_zero]; rfl)
      rw [this] at ha
      exact not_isUnit_zero ha
    have hK0 : algebraMap ↥K₀ ↥K (a : ↥K₀) ≠ 0 := (map_ne_zero_iff _ hinjK).mpr ha0
    have h1 : ((algebraMap ↥O₀ ↥B a : ↥B) : ↥K)⁻¹ ∈ B :=
      (IgSepAux.valuationSubring_isUnit_iff_inv_mem B _ (by rw [algOB_apply]; exact hK0)).mp ha
    rw [algOB_apply, ← map_inv₀, hB] at h1
    exact (IgSepAux.valuationSubring_isUnit_iff_inv_mem O₀ a ha0).mpr h1
  refine ⟨hloc, ?_⟩
  haveI := hloc

  haveI hchar : CharP (ResidueField ↥(IgSepAux.Ap A L)) q := IgSepAux.charP_residueField_Ap q hAq
  obtain ⟨R, hRmem, hRres, hRq⟩ : ∃ R : AlgebraicCurve.RegularProlongation (IgSepAux.Ap A L) ↥K
      ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
      (∀ f : ↥K, f ∈ R.integers ↔ ∃ x y : LaurentSeries ↥(IgSepAux.Ap A L), ModularCurve.coeffMap (residue ↥(IgSepAux.Ap A L)) y ≠ 0 ∧
        (f : LaurentSeries L) * ModularCurve.coeffMap (IgSepAux.Ap A L).subtype y = ModularCurve.coeffMap (IgSepAux.Ap A L).subtype x) ∧
      (∀ (f : ↥R.integers) (x y : LaurentSeries ↥(IgSepAux.Ap A L)), ModularCurve.coeffMap (residue ↥(IgSepAux.Ap A L)) y ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * ModularCurve.coeffMap (IgSepAux.Ap A L).subtype y = ModularCurve.coeffMap (IgSepAux.Ap A L).subtype x →
        ((R.residue f : ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
          LaurentSeries (ResidueField ↥(IgSepAux.Ap A L))) * ModularCurve.coeffMap (residue ↥(IgSepAux.Ap A L)) y = ModularCurve.coeffMap (residue ↥(IgSepAux.Ap A L)) x) ∧
      ∀ (y : LaurentSeries ↥(IgSepAux.Ap A L)) (hy : ModularCurve.coeffMap (IgSepAux.Ap A L).subtype y ∈ K),
        ∃ hO : (⟨ModularCurve.coeffMap (IgSepAux.Ap A L).subtype y, hy⟩ : ↥K) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
            LaurentSeries (ResidueField ↥(IgSepAux.Ap A L))) = ModularCurve.coeffMap (residue ↥(IgSepAux.Ap A L)) y := by
    subst hK
    exact ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div L (IgSepAux.Ap A L)
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) (ModularCurve.translation_mem_GammaH _ _)

  have hWR : ∀ f : ↥K, f ∈ W₀ ↔ f ∈ R.integers := by
    intro f
    rw [hW₀, hRmem]
    exact IgSepAux.GaussP_iff_GaussL (A := A) (L := L) (f : LaurentSeries L)

  have hτB : ∀ b : ↥B, (τ.toAlgHom.toRingHom.comp B.subtype) b ∈ R.integers :=
    fun b => (hWR _).mp ((memB b).mp b.2)
  let ρ : ↥B →+* ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) := R.residue.comp ((τ.toAlgHom.toRingHom.comp B.subtype).codRestrict R.integers hτB)
  have ρ_apply : ∀ b : ↥B, ρ b = R.residue ⟨τ (b : ↥K), hτB b⟩ := fun _ => rfl
  haveI hρloc : IsLocalHom ρ := by
    refine ⟨fun b hb => ?_⟩
    have hne : ρ b ≠ 0 := hb.ne_zero
    have hb0 : ((b : ↥B) : ↥K) ≠ 0 := by
      intro h0
      apply hne
      have : b = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hu : IsUnit (⟨τ (b : ↥K), hτB b⟩ : ↥R.integers) := by
      rw [ρ_apply] at hne
      exact R.isUnit_of_residue_ne_zero hne
    have h1 : (τ (b : ↥K))⁻¹ ∈ R.integers :=
      (IgSepAux.valuationSubring_isUnit_iff_inv_mem R.integers ⟨τ (b : ↥K), hτB b⟩
        ((map_ne_zero_iff _ τ.injective).mpr hb0)).mp hu
    rw [← map_inv₀, ← hWR, ← memB] at h1
    exact (IgSepAux.valuationSubring_isUnit_iff_inv_mem B b hb0).mpr h1
  let θ : ResidueField ↥B →+* ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) := ResidueField.lift ρ
  have hθ : ∀ b : ↥B, θ (residue ↥B b) = ρ b := ResidueField.lift_residue_apply ρ

  let Ψ : ResidueField ↥B →+* LaurentSeries (ResidueField ↥(IgSepAux.Ap A L)) := (algebraMap ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) (LaurentSeries (ResidueField ↥(IgSepAux.Ap A L)))).comp θ
  let ψ : ResidueField ↥O₀ →+* LaurentSeries (ResidueField ↥(IgSepAux.Ap A L)) := Ψ.comp (algebraMap (ResidueField ↥O₀) (ResidueField ↥B))
  have hψ : ∀ (a : ↥O₀) (h : algebraMap ↥K₀ ↥K (a : ↥K₀) ∈ R.integers),
      ψ (residue ↥O₀ a) = ((R.residue ⟨algebraMap ↥K₀ ↥K (a : ↥K₀), h⟩ : ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) : LaurentSeries (ResidueField ↥(IgSepAux.Ap A L))) := by
    intro a h
    show (θ (algebraMap (ResidueField ↥O₀) (ResidueField ↥B) (residue ↥O₀ a)) : LaurentSeries (ResidueField ↥(IgSepAux.Ap A L))) = _
    rw [ResidueField.algebraMap_residue, hθ, ρ_apply]
    congr 2
    apply Subtype.ext
    show τ ((algebraMap ↥O₀ ↥B a : ↥B) : ↥K) = algebraMap ↥K₀ ↥K (a : ↥K₀)
    rw [algOB_apply, hτ]

  have hKK₀ : ∀ x : L, algebraMap ↥K₀ ↥K (algebraMap L ↥K₀ x) = algebraMap L ↥K x := fun x => Subtype.ext rfl

  have hconst : ∀ c : ResidueField ↥(IgSepAux.Ap A L), ∃ o : ↥O₀,
      ψ (residue ↥O₀ o) = algebraMap (ResidueField ↥(IgSepAux.Ap A L)) (LaurentSeries (ResidueField ↥(IgSepAux.Ap A L))) c := by
    intro c
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hmemR : algebraMap L ↥K (a' : L) ∈ R.integers := (R.algebraMap_mem_iff (a' : L)).mpr a'.2
    have hmemW : algebraMap ↥K₀ ↥K (algebraMap L ↥K₀ (a' : L)) ∈ R.integers := by rw [hKK₀]; exact hmemR
    refine ⟨⟨algebraMap L ↥K₀ (a' : L), (hW0 _).mp ((hWR _).mpr hmemW)⟩, ?_⟩
    rw [hψ _ hmemW]
    have : (⟨algebraMap ↥K₀ ↥K (algebraMap L ↥K₀ (a' : L)), hmemW⟩ : ↥R.integers)
        = ⟨algebraMap L ↥K (a' : L), hmemR⟩ := Subtype.ext (hKK₀ _)
    rw [this, R.residue_algebraMap a']
    rfl

  have hjq : ModularCurve.jqModC L = ModularCurve.coeffMap (IgSepAux.Ap A L).subtype (ModularCurve.jqModC ↥(IgSepAux.Ap A L)) :=
    (ModularCurve.map_jqModC (IgSepAux.Ap A L).subtype).symm
  have hjqQ : ModularCurve.coeffEmb L ModularCurve.jq = ModularCurve.jqModC L := ModularCurve.map_jqModC (algebraMap ℚ L)
  have hjK₀ : ModularCurve.jqModC L ∈ K₀ := by
    rw [hK₀, ← hjqQ]
    exact ModularCurve.coeffEmb_mem_laurentBaseChange L
      (ModularCurve.intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 M')))
  have hjK : ModularCurve.coeffMap (IgSepAux.Ap A L).subtype (ModularCurve.jqModC ↥(IgSepAux.Ap A L)) ∈ K := by
    rw [← hjq]; exact hle hjK₀
  obtain ⟨hjO, hjres⟩ := hRq (ModularCurve.jqModC ↥(IgSepAux.Ap A L)) hjK
  have hj : ∃ o : ↥O₀, ψ (residue ↥O₀ o) = ModularCurve.jqModC (ResidueField ↥(IgSepAux.Ap A L)) := by
    have e1 : algebraMap ↥K₀ ↥K ⟨ModularCurve.jqModC L, hjK₀⟩
        = ⟨ModularCurve.coeffMap (IgSepAux.Ap A L).subtype (ModularCurve.jqModC ↥(IgSepAux.Ap A L)), hjK⟩ := Subtype.ext hjq
    have hmemW : algebraMap ↥K₀ ↥K ⟨ModularCurve.jqModC L, hjK₀⟩ ∈ R.integers := by rw [e1]; exact hjO
    refine ⟨⟨⟨ModularCurve.jqModC L, hjK₀⟩, (hW0 _).mp ((hWR _).mpr hmemW)⟩, ?_⟩
    rw [hψ _ hmemW]
    have : (⟨algebraMap ↥K₀ ↥K ⟨ModularCurve.jqModC L, hjK₀⟩, hmemW⟩ : ↥R.integers) = ⟨_, hjO⟩ := Subtype.ext e1
    rw [this, hjres]
    exact ModularCurve.map_jqModC _

  have hjNq : ModularCurve.qExpand L M' (ModularCurve.jqModC L)
      = ModularCurve.coeffMap (IgSepAux.Ap A L).subtype (ModularCurve.qExpand ↥(IgSepAux.Ap A L) M' (ModularCurve.jqModC ↥(IgSepAux.Ap A L))) := by
    rw [IgSepAux.coeffMap_qExpand, ← hjq]
  have hjNqQ : ModularCurve.coeffEmb L (ModularCurve.jqNModC ℚ M') = ModularCurve.qExpand L M' (ModularCurve.jqModC L) := by
    show ModularCurve.coeffMap (algebraMap ℚ L) (ModularCurve.qExpand ℚ M' (ModularCurve.jqModC ℚ)) = _
    rw [IgSepAux.coeffMap_qExpand]
    exact congrArg _ (ModularCurve.map_jqModC (algebraMap ℚ L))
  have hjNK₀ : ModularCurve.qExpand L M' (ModularCurve.jqModC L) ∈ K₀ := by
    rw [hK₀, ← hjNqQ]
    exact ModularCurve.coeffEmb_mem_laurentBaseChange L
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M' (ModularCurve.jqModCd_mem_full ℚ M' (dvd_refl M')))
  have hjNK : ModularCurve.coeffMap (IgSepAux.Ap A L).subtype
      (ModularCurve.qExpand ↥(IgSepAux.Ap A L) M' (ModularCurve.jqModC ↥(IgSepAux.Ap A L))) ∈ K := by
    rw [← hjNq]; exact hle hjNK₀
  obtain ⟨hjNO, hjNres⟩ := hRq _ hjNK
  have hjN : ∃ o : ↥O₀, ψ (residue ↥O₀ o) = ModularCurve.jqNModC (ResidueField ↥(IgSepAux.Ap A L)) M' := by
    have e1 : algebraMap ↥K₀ ↥K ⟨_, hjNK₀⟩ = ⟨_, hjNK⟩ := Subtype.ext hjNq
    have hmemW : algebraMap ↥K₀ ↥K ⟨_, hjNK₀⟩ ∈ R.integers := by rw [e1]; exact hjNO
    refine ⟨⟨⟨_, hjNK₀⟩, (hW0 _).mp ((hWR _).mpr hmemW)⟩, ?_⟩
    rw [hψ _ hmemW]
    have : (⟨algebraMap ↥K₀ ↥K ⟨_, hjNK₀⟩, hmemW⟩ : ↥R.integers) = ⟨_, hjNO⟩ := Subtype.ext e1
    rw [this, hjNres, IgSepAux.coeffMap_qExpand]
    exact congrArg _ (ModularCurve.map_jqModC _)

  have hsub : ∀ x ∈ ModularCurve.modularFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) M', x ∈ ψ.fieldRange := by
    let T : IntermediateField (ResidueField ↥(IgSepAux.Ap A L)) (LaurentSeries (ResidueField ↥(IgSepAux.Ap A L))) :=
      ψ.fieldRange.toIntermediateField (fun c => by obtain ⟨o, ho⟩ := hconst c; exact ⟨_, ho⟩)
    have hle' : ModularCurve.modularFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) M' ≤ T := by
      rw [ModularCurve.modularFunctionFieldC]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x hx
      rcases hx with rfl | rfl
      · obtain ⟨o, ho⟩ := hj; exact ⟨_, ho⟩
      · obtain ⟨o, ho⟩ := hjN
        exact ⟨_, ho⟩
    intro x hx
    exact hle' hx
  let ι0 : ↥(ModularCurve.modularFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) M') →+* ↥ψ.fieldRange :=
    (algebraMap ↥(ModularCurve.modularFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) M')
      (LaurentSeries (ResidueField ↥(IgSepAux.Ap A L)))).codRestrict ψ.fieldRange (fun e => hsub e e.2)
  let χ : ↥(ModularCurve.modularFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) M') →+* ResidueField ↥O₀ :=
    ψ.rangeRestrictFieldEquiv.symm.toRingHom.comp ι0
  have hχ : ∀ e, ψ (χ e) = (e : LaurentSeries (ResidueField ↥(IgSepAux.Ap A L))) := by
    intro e
    change Subtype.val (ψ.rangeRestrictFieldEquiv (ψ.rangeRestrictFieldEquiv.symm (ι0 e))) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  have hcomp : ψ.comp χ = algebraMap ↥(ModularCurve.modularFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) M')
      (LaurentSeries (ResidueField ↥(IgSepAux.Ap A L))) := RingHom.ext hχ

  refine ⟨fun z => ?_⟩
  have hwE : ((θ z : ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) : LaurentSeries (ResidueField ↥(IgSepAux.Ap A L))) ∈ (ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) := (θ z).2
  have hsep := ModularCurve.FullLevel.isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP
    q hq M' hqM' (ResidueField ↥(IgSepAux.Ap A L)) _ hwE
  unfold IsSeparable at hsep ⊢
  have hPw := minpoly.aeval ↥(ModularCurve.modularFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) M')
    ((θ z : ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) : LaurentSeries (ResidueField ↥(IgSepAux.Ap A L)))
  have hQ : Polynomial.aeval z ((minpoly ↥(ModularCurve.modularFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) M')
      ((θ z : ↥(ModularCurve.xHFunctionFieldC (ResidueField ↥(IgSepAux.Ap A L)) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) : LaurentSeries (ResidueField ↥(IgSepAux.Ap A L)))).map χ) = 0 := by
    apply Ψ.injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map,
      show (Ψ.comp (algebraMap (ResidueField ↥O₀) (ResidueField ↥B))).comp χ = ψ.comp χ from rfl, hcomp,
      ← Polynomial.aeval_def]
    exact hPw
  exact (hsep.map).of_dvd (minpoly.dvd _ z hQ)

end S_ModularCurve_FullLevel_exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH (solution)
