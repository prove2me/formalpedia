-- Prove2me | solution 1 for ModularCurve.FullLevel.qExpand_coeffEmb_mem_maximalIdeal_iff_residue_eq_zero_of_forall_aeval_jqNModC_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c5590103-6c1a-5e1a-bd2d-ff735d3d4277

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd
import Theorems.Thm_ModularCurve_forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
import Theorems.Thm_ModularCurve_FullLevel_aeval_jq_mem_integers_and_inv_mem_of_map_residue_ne_zero
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_qExpand_coeffEmb_mem_maximalIdeal_iff_residue_eq_zero_of_forall_aeval_jqNModC_mem
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace GaussRead

theorem isUnit_mk_iff {K : Type} [Field K] (W : ValuationSubring K) (x : K) (hx : x ∈ W) :
    IsUnit (⟨x, hx⟩ : ↥W) ↔ x ≠ 0 ∧ x⁻¹ ∈ W := by
  constructor
  · rintro ⟨u, hu⟩
    have e : (((u⁻¹ : (↥W)ˣ) : ↥W) : K) * x = 1 := by
      have := congrArg (fun z : ↥W => (z : K)) u.inv_mul; rw [hu] at this; exact this
    have hx0 : x ≠ 0 := fun h0 => by rw [h0, mul_zero] at e; exact zero_ne_one e
    refine ⟨hx0, ?_⟩
    rw [← eq_inv_of_mul_eq_one_left e]; exact ((u⁻¹ : (↥W)ˣ) : ↥W).2
  · rintro ⟨hx0, hinv⟩
    exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem mem_nonunits_iff_not {K : Type} [Field K] (W : ValuationSubring K) (x : K) (hx : x ∈ W) :
    x ∈ W.nonunits ↔ ¬ (x ≠ 0 ∧ x⁻¹ ∈ W) := by
  rw [← isUnit_mk_iff W x hx]
  have := (ValuationSubring.coe_mem_nonunits_iff (A := W) (a := ⟨x, hx⟩))
  rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem mem_nonunits_comap_iff {K L : Type} [Field K] [Field L] (f : K →+* L)
    (W : ValuationSubring L) (x : K) (hx : f x ∈ W) :
    x ∈ (W.comap f).nonunits ↔ f x ∈ W.nonunits := by
  rw [mem_nonunits_iff_not (W.comap f) x hx, mem_nonunits_iff_not W (f x) hx, map_ne_zero_iff f f.injective]
  have : x⁻¹ ∈ W.comap f ↔ (f x)⁻¹ ∈ W := by show f x⁻¹ ∈ W ↔ (f x)⁻¹ ∈ W; rw [map_inv₀]
  rw [this]

theorem inv_mem_comap_iff {K L : Type} [Field K] [Field L] (f : K →+* L)
    (W : ValuationSubring L) (x : K) : x⁻¹ ∈ W.comap f ↔ (f x)⁻¹ ∈ W := by
  show f x⁻¹ ∈ W ↔ (f x)⁻¹ ∈ W
  rw [map_inv₀]

theorem aeval_mem {k K : Type} [Field k] [Field K] [Algebra k K] (W : ValuationSubring K)
    (p : Polynomial k) (hp : ∀ i, algebraMap k K (p.coeff i) ∈ W) (x : K) (hx : x ∈ W) :
    Polynomial.aeval x p ∈ W := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem W.toSubring (fun i _ => ?_)
  rw [Algebra.smul_def]
  exact W.toSubring.mul_mem (hp i) (W.toSubring.pow_mem hx i)

end GaussRead

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (ℓ' : ℕ) [Fact ℓ'.Prime]
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)]

    (hjK : ModularCurve.jqNModC ↥k₀ (q * ℓ') ∈ Kℓ)

    (V : ValuationSubring ↥Kℓ)
    (hVA : ∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x)
    (hVC : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ V)
    (hVj : ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
      (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
        ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))

    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M')))
    (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ) :
    ∃ hV : (⟨_, hgK⟩ : ↥Kℓ) ∈ V,
      ((⟨_, hV⟩ : ↥V) ∈ maximalIdeal ↥V ↔ (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) := by
  classical
  haveI hℓne : NeZero ℓ' := ⟨(Fact.out : ℓ'.Prime).ne_zero⟩
  haveI hqne : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI hqℓne : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩
  haveI := hdvr

  let ψ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ↥A :=
    { toFun := fun a => ⟨algebraMap ↥k₀ (AlgebraicClosure ℚ) (a : ↥k₀), a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hψ : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ((ψ a : ↥A) : AlgebraicClosure ℚ) = ((a : ↥k₀) : AlgebraicClosure ℚ) := fun _ => rfl

  have hunitA : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsUnit (ψ a) → IsUnit a := by
    intro a hu
    obtain ⟨ha0, hinv⟩ := (GaussRead.isUnit_mk_iff A _ (ψ a).2).mp (by simpa using hu)
    have ha0' : (a : ↥k₀) ≠ 0 := fun h0 => ha0 (by rw [hψ, h0]; rfl)
    have hinv' : ((a : ↥k₀))⁻¹ ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) := by
      show algebraMap ↥k₀ (AlgebraicClosure ℚ) ((a : ↥k₀))⁻¹ ∈ A
      rw [map_inv₀]; exact hinv
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv'⟩, Subtype.ext (mul_inv_cancel₀ ha0')⟩
  have hmaxA : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → ψ a ∈ maximalIdeal ↥A := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    exact fun hu => ha (hunitA a hu)

  have hqA : ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (ψ (q : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) := hu.map ψ
    rw [map_natCast] at h1
    exact (IsLocalRing.mem_maximalIdeal _).mp (ValuationSubring.natCast_mem_maximalIdeal_of_liesOverPrime hA) h1

  have hAV : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥k₀ ↥Kℓ (a : ↥k₀) ∈ V := fun a => (hVA _).mpr ⟨a, rfl⟩
  have hmV : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → algebraMap ↥k₀ ↥Kℓ (a : ↥k₀) ∈ V.nonunits := by
    intro a ha
    rw [GaussRead.mem_nonunits_iff_not V _ (hAV a)]
    rintro ⟨h0, hinv⟩
    rw [← map_inv₀] at hinv
    obtain ⟨b, hb⟩ := (hVA _).mp hinv
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
    apply ha
    have ha0 : (a : ↥k₀) ≠ 0 := fun h => h0 (by rw [h, map_zero])
    refine isUnit_iff_exists_inv.mpr ⟨b, ?_⟩
    apply Subtype.ext
    show (a : ↥k₀) * (b : ↥k₀) = 1
    rw [show (b : ↥k₀) = ((a : ↥k₀))⁻¹ from hb, mul_inv_cancel₀ ha0]

  let E : LaurentSeries ↥k₀ →ₐ[↥k₀] LaurentSeries ↥k₀ :=
    { toRingHom := ModularCurve.qExpand ↥k₀ ℓ'
      commutes' := fun r => by
        show ModularCurve.qExpand ↥k₀ ℓ' (algebraMap ↥k₀ (LaurentSeries ↥k₀) r) = algebraMap ↥k₀ (LaurentSeries ↥k₀) r
        rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.qExpand_single, mul_zero] }
  have hE : ∀ x, E x = ModularCurve.qExpand ↥k₀ ℓ' x := fun _ => rfl

  let P : IntermediateField ↥k₀ (LaurentSeries ↥k₀) :=
    (Kℓ.toSubalgebra.comap E).toIntermediateField (fun x hx => by
      rw [Subalgebra.mem_comap] at hx ⊢
      rw [map_inv₀]; exact Kℓ.inv_mem hx)
  have memP : ∀ x : LaurentSeries ↥k₀, x ∈ P ↔ ModularCurve.qExpand ↥k₀ ℓ' x ∈ Kℓ := fun x => Iff.rfl

  set F₀ : IntermediateField ↥k₀ (LaurentSeries ↥k₀) :=
    ModularCurve.laurentBaseChange ↥k₀ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) with hF₀
  have hF₀' : F₀ = ModularCurve.laurentBaseChange ↥k₀ (modularFunctionFieldFull M') := by
    rw [hF₀, ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
  have hFP : F₀ ≤ P := by
    rw [hF₀']
    show IntermediateField.adjoin ↥k₀ _ ≤ P
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    show ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ x) ∈ Kℓ
    rw [hKℓ]
    exact ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull ↥k₀ M' ℓ'
      ((q * ℓ') ^ 2 * M') ⟨q ^ 2 * ℓ', by ring⟩ (ModularCurve.FullLevel.levelH (q * ℓ') M') x hx

  let φP : ↥P →ₐ[↥k₀] ↥Kℓ :=
    { toFun := fun x => ⟨ModularCurve.qExpand ↥k₀ ℓ' (x : LaurentSeries ↥k₀), (memP x).mp x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _)
      commutes' := fun r => Subtype.ext (E.commutes r) }
  have hφP : ∀ x : ↥P, ((φP x : ↥Kℓ) : LaurentSeries ↥k₀) = ModularCurve.qExpand ↥k₀ ℓ' x := fun _ => rfl
  let φ₁ : ↥F₀ →ₐ[↥k₀] ↥Kℓ := φP.comp (IntermediateField.inclusion hFP)
  have hφ₁ : ∀ x : ↥F₀, ((φ₁ x : ↥Kℓ) : LaurentSeries ↥k₀) = ModularCurve.qExpand ↥k₀ ℓ' x := fun _ => rfl
  have hφ₁' : ∀ x : ↥F₀, φ₁ x = φP (IntermediateField.inclusion hFP x) := fun _ => rfl
  let VP : ValuationSubring ↥P := V.comap φP.toRingHom
  let V₁ : ValuationSubring ↥F₀ := V.comap φ₁.toRingHom
  have memVP : ∀ x : ↥P, x ∈ VP ↔ φP x ∈ V := fun _ => Iff.rfl
  have memV₁ : ∀ x : ↥F₀, x ∈ V₁ ↔ φ₁ x ∈ V := fun _ => Iff.rfl

  let C2 : LaurentSeries ↥k₀ →+* LaurentSeries (AlgebraicClosure ℚ) := coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ))
  have hC2c : ∀ x : ↥k₀, C2 (algebraMap ↥k₀ (LaurentSeries ↥k₀) x) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) := by
    intro x
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single]
    exact ModularCurve.coeffMap_single _ _ _
  have hC2e : ∀ x : LaurentSeries ℚ, C2 (coeffEmb ↥k₀ x) = coeffEmb (AlgebraicClosure ℚ) x := by
    intro x
    ext k
    show algebraMap ↥k₀ (AlgebraicClosure ℚ) (algebraMap ℚ ↥k₀ (x.coeff k)) = algebraMap ℚ (AlgebraicClosure ℚ) (x.coeff k)
    exact (IsScalarTower.algebraMap_apply ℚ ↥k₀ (AlgebraicClosure ℚ) _).symm
  have hC2F : ∀ x : LaurentSeries ↥k₀, x ∈ F₀ → C2 x ∈ modularFunctionFieldBar M' := by
    intro x hx
    rw [hF₀', ModularCurve.mem_laurentBaseChange_iff] at hx
    have hle : Subfield.closure (Set.range (algebraMap ↥k₀ (LaurentSeries ↥k₀)) ∪ (⇑(coeffEmb ↥k₀) '' (modularFunctionFieldFull M' : Set (LaurentSeries ℚ))))
        ≤ (modularFunctionFieldBar M').toSubfield.comap C2 := by
      rw [Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | ⟨z, hz, rfl⟩)
      · show C2 (algebraMap ↥k₀ (LaurentSeries ↥k₀) c) ∈ modularFunctionFieldBar M'
        rw [hC2c]; exact (modularFunctionFieldBar M').algebraMap_mem _
      · show C2 (coeffEmb ↥k₀ z) ∈ modularFunctionFieldBar M'
        rw [hC2e]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hz
    exact hle hx
  let φ₂ : ↥F₀ →+* ↥(modularFunctionFieldBar M') :=
    { toFun := fun x => ⟨C2 x, hC2F x x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  have hφ₂ : ∀ x : ↥F₀, ((φ₂ x : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) = C2 x := fun _ => rfl
  let V₂ : ValuationSubring ↥F₀ := R₀.integers.comap φ₂
  have memV₂ : ∀ x : ↥F₀, x ∈ V₂ ↔ φ₂ x ∈ R₀.integers := fun _ => Iff.rfl
  have hφ₂c : ∀ x : ↥k₀, φ₂ (algebraMap ↥k₀ ↥F₀ x) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (x : AlgebraicClosure ℚ) :=
    fun x => Subtype.ext (hC2c x)

  have hjF₀ : coeffEmb ↥k₀ jq ∈ F₀ := by
    rw [hF₀']; exact coeffEmb_mem_laurentBaseChange ↥k₀ (modularFunctionField_le_full M' (jq_mem M'))
  set j₀ : ↥F₀ := ⟨_, hjF₀⟩ with hj₀
  have hφ₂j : φ₂ j₀ = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :=
    Subtype.ext (hC2e jq)
  have hjq0 : ModularCurve.jqModC ↥k₀ = coeffEmb ↥k₀ jq := (ModularCurve.map_jqModC (algebraMap ℚ ↥k₀)).symm
  have heq : ModularCurve.jqNModC ↥k₀ (q * ℓ') = ModularCurve.qExpand ↥k₀ ℓ' (ModularCurve.qExpand ↥k₀ q (coeffEmb ↥k₀ jq)) := by
    rw [ModularCurve.qExpand_qExpand, ModularCurve.jqNModC, hjq0]
    exact ModularCurve.qExpand_congr (Nat.mul_comm q ℓ') _
  have hjP' : ModularCurve.qExpand ↥k₀ q (coeffEmb ↥k₀ jq) ∈ P := by
    rw [memP, ← heq]; exact hjK
  set jP : ↥P := IntermediateField.inclusion hFP j₀ with hjP
  set jP' : ↥P := ⟨_, hjP'⟩ with hjP'def
  have hφPj' : φP jP' = ⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ := Subtype.ext heq.symm

  have hjOf0 : (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) ≠ 0 := by
    intro h0
    have h1 : ModularCurve.jqNModC ↥k₀ (q * ℓ') = 0 := congrArg Subtype.val h0
    rw [ModularCurve.jqNModC, hjq0, ← hjℓ] at h1
    have h2 : (jℓ : LaurentSeries ↥k₀) = 0 := by
      apply ModularCurve.qExpand_injective (R := ↥k₀) (N := q * ℓ')
      rw [h1, map_zero]
    exact (Fact.out : jℓ ≠ 0) (Subtype.ext h2)
  haveI : Fact ((⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) ≠ 0) := ⟨hjOf0⟩
  have hjOfC : (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ := by
    have hcoe : (((⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ)) : LaurentSeries ↥k₀) =
        coeffEmb ↥k₀ (ModularCurve.qExpand ℚ (q * ℓ') jq) := by
      rw [ModularCurve.coeffEmb_qExpand]
      show ModularCurve.jqNModC ↥k₀ (q * ℓ') = _
      rw [ModularCurve.jqNModC, hjq0]
    exact (ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt (q * ℓ')
      (by nlinarith [(Fact.out : q.Prime).two_le, (Fact.out : ℓ'.Prime).two_le]) ↥k₀ Kℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) jℓ hjℓ _ hcoe).1
  have hjOfV : (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) ∈ V := hVC ⟨_, hjOfC⟩
  have hOverOf : ∀ Pp : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), Pp.map (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ≠ 0 →
      Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ V ∧
      (Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)))⁻¹ ∈ V := by
    intro Pp hPp
    have hmem : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ V :=
      GaussRead.aeval_mem V _ (fun i => by rw [Polynomial.coeff_map]; exact hAV _) _ hjOfV
    refine ⟨hmem, ?_⟩
    by_contra hinv
    apply hPp
    have hnu : (⟨_, hmem⟩ : ↥V) ∈ maximalIdeal ↥V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, GaussRead.isUnit_mk_iff]
      rintro ⟨-, h⟩; exact hinv h
    have hall := hVj Pp ⟨hmem, hnu⟩
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
    exact hall i

  have hAP : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥k₀ ↥P (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a) ∈ VP := by
    intro a; rw [memVP, AlgHom.commutes]; exact hAV a
  have hmP : ∀ a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥k₀ ↥P (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a) ∈ VP.nonunits := by
    intro a ha
    have h := hmV a ha
    rw [GaussRead.mem_nonunits_comap_iff φP.toRingHom V _ (by show φP _ ∈ V; rw [AlgHom.commutes]; exact hAV a)]
    show φP (algebraMap ↥k₀ ↥P (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a)) ∈ V.nonunits
    rw [AlgHom.commutes]; exact h
  have hJQ := (ModularCurve.forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring q ↥k₀ P ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) hqA
    jP rfl jP' rfl VP hAP hmP).mpr (by
      intro Pp hPp
      obtain ⟨h1, h2⟩ := hOverOf Pp hPp
      have hev : φP (Polynomial.aeval jP' (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀))) =
          Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) := by
        rw [← Polynomial.aeval_algHom_apply, hφPj']
      refine ⟨?_, ?_⟩
      · rw [memVP, hev]; exact h1
      · show φP.toRingHom _ ∈ V
        rw [map_inv₀]; show (φP _)⁻¹ ∈ V; rw [hev]; exact h2)

  have hV₁ : (∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥k₀ ↥F₀ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a) ∈ V₁) ∧
      (∀ a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥k₀ ↥F₀ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a) ∈ V₁.nonunits) ∧
      (∀ Pp : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), Pp.map (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ≠ 0 →
        Polynomial.aeval j₀ (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ V₁ ∧
          (Polynomial.aeval j₀ (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)))⁻¹ ∈ V₁) := by
    refine ⟨fun a => ?_, fun a ha => ?_, fun Pp hPp => ?_⟩
    · rw [memV₁, AlgHom.commutes]; exact hAV a
    · rw [GaussRead.mem_nonunits_comap_iff φ₁.toRingHom V _ (by show φ₁ _ ∈ V; rw [AlgHom.commutes]; exact hAV a)]
      show φ₁ (algebraMap ↥k₀ ↥F₀ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a)) ∈ V.nonunits
      rw [AlgHom.commutes]; exact hmV a ha
    · obtain ⟨h1, h2⟩ := hJQ Pp hPp
      have hev : IntermediateField.inclusion hFP (Polynomial.aeval j₀ (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀))) =
          Polynomial.aeval jP (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) := by
        rw [← Polynomial.aeval_algHom_apply]
      refine ⟨?_, ?_⟩
      · rw [memV₁, hφ₁', hev]; exact h1
      · show φ₁.toRingHom _ ∈ V
        rw [map_inv₀]
        have : (φP (Polynomial.aeval jP (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀))))⁻¹ ∈ V := by
          have h2' : φP.toRingHom (Polynomial.aeval jP (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)))⁻¹ ∈ V := h2
          rwa [map_inv₀] at h2'
        show (φ₁ _)⁻¹ ∈ V
        rw [hφ₁', hev]; exact this

  have hV₂ : (∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥k₀ ↥F₀ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a) ∈ V₂) ∧
      (∀ a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥k₀ ↥F₀ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a) ∈ V₂.nonunits) ∧
      (∀ Pp : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), Pp.map (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ≠ 0 →
        Polynomial.aeval j₀ (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ V₂ ∧
          (Polynomial.aeval j₀ (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)))⁻¹ ∈ V₂) := by
    have hcA : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), φ₂ (algebraMap ↥k₀ ↥F₀ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a)) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((ψ a : ↥A) : AlgebraicClosure ℚ) := by
      intro a; exact hφ₂c _
    have hmemA : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), φ₂ (algebraMap ↥k₀ ↥F₀ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a)) ∈ R₀.integers := by
      intro a; rw [hcA]; exact (R₀.algebraMap_mem_iff _).mpr (ψ a).2
    refine ⟨fun a => hmemA a, fun a ha => ?_, fun Pp hPp => ?_⟩
    · rw [GaussRead.mem_nonunits_comap_iff φ₂ R₀.integers _ (hmemA a)]
      have hres : R₀.residue ⟨_, hmemA a⟩ = 0 := by
        have e1 : (⟨_, hmemA a⟩ : ↥R₀.integers) = ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (ψ a),
            (R₀.algebraMap_mem_iff _).mpr (ψ a).2⟩ := Subtype.ext (hcA a)
        rw [e1, R₀.residue_algebraMap, (IsLocalRing.residue_eq_zero_iff _).mpr (hmaxA a ha), map_zero]
      have hker : (⟨_, hmemA a⟩ : ↥R₀.integers) ∈ maximalIdeal ↥R₀.integers := by
        rw [← R₀.ker_residue, RingHom.mem_ker]; exact hres
      exact (ValuationSubring.coe_mem_nonunits_iff).mpr hker
    ·
      set PA : Polynomial ↥A := Pp.map ψ with hPA
      have hPA0 : PA.map (IsLocalRing.residue ↥A) ≠ 0 := by
        intro h0
        apply hPp
        ext i
        have hi : (PA.map (IsLocalRing.residue ↥A)).coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
        rw [Polynomial.coeff_map, hPA, Polynomial.coeff_map, IsLocalRing.residue_eq_zero_iff] at hi
        rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff,
          IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact (IsLocalRing.mem_maximalIdeal _).mp hi (hu.map ψ)
      obtain ⟨h1, h2⟩ := ModularCurve.FullLevel.aeval_jq_mem_integers_and_inv_mem_of_map_residue_ne_zero q hq M' hqM' A hA R₀ hR₀ PA hPA0
      have hev : φ₂ (Polynomial.aeval j₀ (Pp.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀))) =
          Polynomial.aeval ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M'))) PA := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, hPA, Polynomial.eval₂_map,
          Polynomial.hom_eval₂, hφ₂j]
        congr 1
        refine RingHom.ext (fun a => ?_)
        show φ₂ (algebraMap ↥k₀ ↥F₀ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a)) = algebraMap ↥A ↥(modularFunctionFieldBar M') (ψ a)
        rw [IsScalarTower.algebraMap_apply ↥A (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (ψ a)]
        exact hcA a
      refine ⟨?_, ?_⟩
      · rw [memV₂, hev]; exact h1
      · rw [GaussRead.inv_mem_comap_iff, hev]; exact h2
  have hVV : V₁ = V₂ :=
    ModularCurve.valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd q M' hqM' ↥k₀ F₀ hF₀ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) hqA
      j₀ rfl V₁ V₂ hV₁ hV₂

  have hgF₀ : coeffEmb ↥k₀ g ∈ F₀ := by rw [hF₀']; exact coeffEmb_mem_laurentBaseChange ↥k₀ hg
  have hφ₁g : φ₁ ⟨_, hgF₀⟩ = ⟨_, hgK⟩ := Subtype.ext rfl
  have hφ₂g : φ₂ ⟨_, hgF₀⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :=
    Subtype.ext (hC2e g)
  have hg2 : (⟨_, hgF₀⟩ : ↥F₀) ∈ V₂ := by rw [memV₂, hφ₂g]; exact hgi
  have hg1 : (⟨_, hgF₀⟩ : ↥F₀) ∈ V₁ := hVV ▸ hg2
  have hV : (⟨_, hgK⟩ : ↥Kℓ) ∈ V := by
    have : φ₁ ⟨_, hgF₀⟩ ∈ V := hg1
    rwa [hφ₁g] at this
  refine ⟨hV, ?_⟩
  have h1 : (⟨_, hV⟩ : ↥V) ∈ maximalIdeal ↥V ↔ (⟨_, hgF₀⟩ : ↥F₀) ∈ V₁.nonunits := by
    rw [GaussRead.mem_nonunits_comap_iff φ₁.toRingHom V _ hg1]
    show _ ↔ ((φ₁ ⟨_, hgF₀⟩ : ↥Kℓ) : ↥Kℓ) ∈ V.nonunits
    rw [hφ₁g]
    exact (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨_, hV⟩)).symm
  have h2 : (⟨_, hgF₀⟩ : ↥F₀) ∈ V₂.nonunits ↔ (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0 := by
    rw [GaussRead.mem_nonunits_comap_iff φ₂ R₀.integers _ hg2]
    rw [← RingHom.mem_ker, R₀.ker_residue]
    have e : (⟨φ₂ ⟨_, hgF₀⟩, hg2⟩ : ↥R₀.integers) = ⟨_, hgi⟩ := Subtype.ext hφ₂g
    rw [← e]
    exact (ValuationSubring.coe_mem_nonunits_iff (A := R₀.integers) (a := ⟨_, hg2⟩))
  rw [h1, hVV, h2]

end S_ModularCurve_FullLevel_qExpand_coeffEmb_mem_maximalIdeal_iff_residue_eq_zero_of_forall_aeval_jqNModC_mem
end P2MW
export P2MW.S_ModularCurve_FullLevel_qExpand_coeffEmb_mem_maximalIdeal_iff_residue_eq_zero_of_forall_aeval_jqNModC_mem (solution)
