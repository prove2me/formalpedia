-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.placeOfPoint_eq_delta_sp_restrictAlong_of_comp_one_of_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/da7c288a-a0a9-5087-a9e1-c1fbee4cd49e

import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_XHDRModelAtP_placeOfPoint_eq_sp_restrictAlong_of_comp_zero_of_gauss
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_placeOfPoint_eq_delta_sp_restrictAlong_of_comp_one_of_gauss
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.coe_laurentReductionDegZero ModularCurve.laurentReductionDiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

noncomputable section

namespace R1V433

theorem restrictAlong_ofAlgAut_smul_comp {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (σ : F' ≃ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hσφ : (σ.toAlgHom.comp φ).toRingHom.IsIntegral) (V : Place K F') :
    (SemilinearAut.ofAlgAut σ • V).restrictAlong (σ.toAlgHom.comp φ) hσφ = V.restrictAlong φ hφ := by
  apply Place.ext
  change (SemilinearAut.ofAlgAut σ • V).toValuationSubring.comap (σ.toAlgHom.comp φ).toRingHom =
    V.toValuationSubring.comap φ.toRingHom
  ext x
  simp only [ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro h
    have : (SemilinearAut.ofAlgAut σ)⁻¹ • ((σ.toAlgHom.comp φ).toRingHom x) = φ.toRingHom x := by
      rw [SemilinearAut.inv_smul_def, SemilinearAut.toRingAut_ofAlgAut]
      show (σ : F' ≃+* F').symm (σ (φ x)) = φ x
      exact (σ : F' ≃+* F').symm_apply_apply (φ x)
    rwa [this] at h
  · intro h
    have : (SemilinearAut.ofAlgAut σ)⁻¹ • ((σ.toAlgHom.comp φ).toRingHom x) = φ.toRingHom x := by
      rw [SemilinearAut.inv_smul_def, SemilinearAut.toRingAut_ofAlgAut]
      show (σ : F' ≃+* F').symm (σ (φ x)) = φ x
      exact (σ : F' ≃+* F').symm_apply_apply (φ x)
    rwa [this]

section Plumbing

variable {p : ℕ} {Γ Γ' Γ'' : Subgroup SL(2, ℤ)} {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  {κ : Type} [CommRing κ] (toκ : R p →+* κ)

theorem fibreMap_fst (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) :
    XHDRLevel.fibreMap φ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ.1 := by
  rw [XHDRLevel.fibreMap]
  exact pullback.lift_fst _ _ _

theorem fibreMap_snd (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) :
    XHDRLevel.fibreMap φ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [XHDRLevel.fibreMap]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem fibreMap_comp (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj))
    (ψ : SchemeHomOver (toBase p Γ' hj) (toBase p Γ'' hj)) :
    XHDRLevel.fibreMap φ toκ ≫ XHDRLevel.fibreMap ψ toκ =
      XHDRLevel.fibreMap (⟨φ.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, φ.2]⟩ :
        SchemeHomOver (toBase p Γ hj) (toBase p Γ'' hj)) toκ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_fst, reassoc_of% (fibreMap_fst toκ φ), fibreMap_fst]
  · rw [Category.assoc, fibreMap_snd, fibreMap_snd, fibreMap_snd]

theorem fibreMap_id' (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ hj)) (hφ : φ.1 = 𝟙 _) :
    XHDRLevel.fibreMap φ toκ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [fibreMap_fst, hφ, Category.id_comp, Category.comp_id]
  · rw [fibreMap_snd, Category.id_comp]

theorem fibreMap_congr (φ ψ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) (h : φ.1 = ψ.1) :
    XHDRLevel.fibreMap φ toκ = XHDRLevel.fibreMap ψ toκ := by
  obtain ⟨φ, hφ⟩ := φ; obtain ⟨ψ, hψ⟩ := ψ; cases h; rfl

end Plumbing

section Bundle

variable {p M : ℕ} [Fact p.Prime] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)

def liftPt (g : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X p (ΓM M H) hj)
    (hg : g ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) :
    {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} :=
  ⟨pullback.lift g (𝟙 _) (by rw [hg, Category.id_comp]) ≫ inv 𝔛.eeta, by
    rw [← 𝔛.heeta, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_snd]⟩

theorem liftPt_fst (g : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X p (ΓM M H) hj)
    (hg : g ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) :
    (liftPt 𝔛 g hg).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = g := by
  simp only [liftPt, Category.assoc, IsIso.inv_hom_id_assoc]
  exact pullback.lift_fst _ _ _

theorem pt_fst_toBase (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) :
    (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta,
    ← Category.assoc, y.2, Category.id_comp]

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥A)

abbrev diaκ (d : (ZMod M)ˣ) :=
  XHDRLevel.fibreMap (overOfIso (𝔛.dia d) (𝔛.dia_over d)) ((IsLocalRing.residue ↥A).comp ρ)

abbrev dia0κ (e : (ZMod (M / p))ˣ) :=
  XHDRLevel.fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)

abbrev wκ := XHDRLevel.fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ)

theorem diaκ_mul (d d' : (ZMod M)ˣ) :
    diaκ 𝔛 A ρ d ≫ diaκ 𝔛 A ρ d' = diaκ 𝔛 A ρ (d * d') := by
  rw [diaκ, diaκ, fibreMap_comp]
  exact fibreMap_congr _ _ _ (𝔛.dia_mul d d').symm

theorem diaκ_one : diaκ 𝔛 A ρ 1 = 𝟙 _ :=
  fibreMap_id' _ _ (by simp [overOfIso, 𝔛.dia_mem 1 H.one_mem])

theorem wκ_wκ (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1) :
    wκ 𝔛 A ρ ≫ wκ 𝔛 A ρ = diaκ 𝔛 A ρ d := by
  rw [wκ, fibreMap_comp]
  exact fibreMap_congr _ _ _ (𝔛.w_sq d hd)

theorem dia0κ_dia0κ_inv_apply (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (d : (ZMod M)ˣ)
    (x : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :
    (dia0κ 𝔛 A ρ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d⁻¹)).base
      ((dia0κ 𝔛 A ρ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).base x) = x := by
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  apply (𝔛.comp A hA ρ hρ 0).isClosedEmbedding.injective
  have key : dia0κ 𝔛 A ρ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) ≫
      dia0κ 𝔛 A ρ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d⁻¹) ≫ 𝔛.comp A hA ρ hρ 0 = 𝔛.comp A hA ρ hρ 0 := by
    have h1 := 𝔛.comp_dia A hA ρ hρ 0 d
    have h2 := 𝔛.comp_dia A hA ρ hρ 0 d⁻¹
    rw [← h2, reassoc_of% h1.symm, diaκ_mul, mul_inv_cancel, diaκ_one, Category.comp_id]
  have := congrArg (fun φ => φ.base x) key
  simpa [Scheme.Hom.comp_base, TopCat.comp_app] using this

theorem base_inv_base_apply {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (y : Y) : f.base ((inv f).base y) = y := by
  show ((inv f) ≫ f).base y = y
  rw [IsIso.inv_hom_id]; rfl

theorem inv_base_base_apply {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (x : X) : (inv f).base (f.base x) = x := by
  show (f ≫ inv f).base x = x
  rw [IsIso.hom_inv_id]; rfl

theorem exists_closedPoint_dia0κ [NeZero M] (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C) :
    ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
      (𝔛.efib A hA ρ hρ).base P'.1 = (dia0κ 𝔛 A ρ e).base ((𝔛.efib A hA ρ hρ).base P.1) ∧
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P' =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by
  obtain ⟨h, hpl⟩ :=
    ModularCurve.XHDRModelAtP.exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ e P
  exact ⟨⟨_, h⟩, base_inv_base_apply _ _, hpl⟩

end Bundle

end R1V433

end

open R1V433 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hβ : (θ.toAlgHom.comp α).IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut
      (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (R : RegularProlongation A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (sp : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (hgauss : ∀ f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), f ∈ R.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (hres : ∀ (f : R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
      (((f : R.integers) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
      ((R.residue f : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y =
        coeffMap (IsLocalRing.residue ↥A) x)

    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
        ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f))

    (huniq : ∀ sp' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
          ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp)

    (hq : ∀ (y : LaurentSeries ↥A)
      (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ' : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = δ (sp ((𝔛.Meta.pointEquivPlace y).restrictAlong (θ.toAlgHom.comp α) hβ)) := by

  obtain ⟨d, hd⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) pb⁻¹
  have hdp : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) *
      (p : ZMod (M / p)) = 1 := by
    rw [hd, ← hpb, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdinv : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d⁻¹ = pb := by rw [map_inv, hd, inv_inv]

  have hg : ((y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ 𝔛.w.hom) ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, 𝔛.w_over]; exact pt_fst_toBase 𝔛 y
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
      y₀.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ 𝔛.w.hom :=
    ⟨liftPt 𝔛 _ hg, liftPt_fst 𝔛 _ hg⟩
  have hW : 𝔛.Meta.pointEquivPlace y = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y₀ := by
    apply hwgen y₀ y
    rw [hy₀]; simp only [Category.assoc]
  have hβW : (𝔛.Meta.pointEquivPlace y).restrictAlong (θ.toAlgHom.comp α) hβ =
      (𝔛.Meta.pointEquivPlace y₀).restrictAlong α hα := by
    rw [hW]; exact restrictAlong_ofAlgAut_smul_comp α θ hα hβ _

  have hu₀_over : (u.1 ≫ 𝔛.w.hom) ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom ρ) := by
    rw [Category.assoc, 𝔛.w_over]; exact u.2
  have hu₀ : barPt A ≫ (⟨u.1 ≫ 𝔛.w.hom, hu₀_over⟩ :
      SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)).1 = y₀.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
    rw [hy₀]; show barPt A ≫ u.1 ≫ 𝔛.w.hom = _; rw [← Category.assoc, hu]
  have huκ₀ : (uκ ≫ wκ 𝔛 A ρ) ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (⟨u.1 ≫ 𝔛.w.hom, hu₀_over⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)).1 := by
    show (uκ ≫ wκ 𝔛 A ρ) ≫ pullback.fst _ _ = Spec.map _ ≫ u.1 ≫ 𝔛.w.hom
    rw [Category.assoc, fibreMap_fst, ← Category.assoc, huκ, Category.assoc]; rfl
  have huκ₀' : (uκ ≫ wκ 𝔛 A ρ) ≫ pullback.snd _ _ = 𝟙 _ := by
    rw [Category.assoc, fibreMap_snd, huκ']

  obtain ⟨P₁, hP₁val, hpl₁⟩ := exists_closedPoint_dia0κ 𝔛 A ρ hpM2 hHp hA hρ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) P0
  have e2 : 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ wκ 𝔛 A ρ =
      𝔛.efib A hA ρ hρ ≫ dia0κ 𝔛 A ρ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) ≫ 𝔛.comp A hA ρ hρ 0 := by
    rw [← 𝔛.comp_w A hA ρ hρ, Category.assoc, wκ_wκ 𝔛 A ρ d hdp, ← 𝔛.comp_dia A hA ρ hρ 0 d]
  have hP₁ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P₁.1 =
      (uκ ≫ wκ 𝔛 A ρ).base (IsLocalRing.closedPoint (ResidueField ↥A)) := by
    have e2' := congrArg (fun φ => φ.base P0.1) e2
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e2' hP0 ⊢
    rw [← hP0, e2', hP₁val]

  have hfirst := ModularCurve.XHDRModelAtP.placeOfPoint_eq_sp_restrictAlong_of_comp_zero_of_gauss p M H hpM hpM2
    hHp hj 𝔛 A hA ρ hρ α hα hα_coe R sp hgauss hres hdiv huniq hq y₀ ⟨u.1 ≫ 𝔛.w.hom, hu₀_over⟩ hu₀
    (uκ ≫ wκ 𝔛 A ρ) huκ₀ huκ₀' P₁ hP₁

  obtain ⟨P₂, hP₂val, hpl₂⟩ := exists_closedPoint_dia0κ 𝔛 A ρ hpM2 hHp hA hρ pb P₁
  have hP₂ : P₂ = P0 := by
    apply Subtype.ext
    have e3 : (𝔛.efib A hA ρ hρ).base P₂.1 = (𝔛.efib A hA ρ hρ).base P0.1 := by
      rw [hP₂val, hP₁val, ← hdinv]
      exact dia0κ_dia0κ_inv_apply 𝔛 A ρ hA hρ d _
    have e4 := congrArg (fun z => (inv (𝔛.efib A hA ρ hρ)).base z) e3
    simpa only [inv_base_base_apply] using e4
  rw [hP₂] at hpl₂
  rw [hβW, ← hfirst, hδ]
  exact hpl₂

end S_ModularCurve_XHDRModelAtP_placeOfPoint_eq_delta_sp_restrictAlong_of_comp_one_of_gauss
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_placeOfPoint_eq_delta_sp_restrictAlong_of_comp_one_of_gauss (solution)
