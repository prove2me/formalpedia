-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_zpow_unit_principle_evalAt_read_chart_of_section_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ba65ced8-2d6b-5346-bfe6-6a1f89a2fece

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel

import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_ringEquiv_adicCompletion_uvCrossingModel_and_forall_section_exists_ringHom_evalAt_eq_of_chart
import Theorems.Thm_IsLocalRing_exists_units_forall_mul_const_pow_eq_mul_monomial_of_ringEquiv_adicCompletion_uvCrossingModel_of_forall_prime_mem_localization
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_read_chart_mul_eq_and_isUnit_germ_and_smul_eq_and_evalAt_eq_of_chart
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_zpow_unit_principle_evalAt_read_chart_of_section_of_chart
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
    letI Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
    letI φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
    letI gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
    ∀ hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤)),
    letI read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
    letI param : ↥(xHFunctionFieldBar M H) := read gv
    ∀ g : ↥(xHFunctionFieldBar M H), g ≠ 0 →
      (∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
        ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
        s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
        barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
        U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
        W.ord g = 0) →
      ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧
        ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
          ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
          s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
          barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
          U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
          ∃ h : W.evalAt g * c⁻¹ * (W.evalAt param) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
  intro hgen g hg hord
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
  let VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
  let Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
  let φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
  let gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
  let read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
        ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
  let param : ↥(xHFunctionFieldBar M H) := read gv
  have hNT := ModularCurve.XHDRModelAtP.exists_ringEquiv_adicCompletion_uvCrossingModel_and_forall_section_exists_ringHom_evalAt_eq_of_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ hgen g
  obtain ⟨O', _, _, _, ϖ', hϖ', ιA', hιinj, hιloc, B, _, _, _, _, σB, hσB, emb, hemb, W', _, _, _, _, π', hπ', E', hE',
    ι', w₀, hϖB, bu, bv, wu, hbu, hbv, hembv, hembu, hgfrac, S, _, jA, hdesc, hχ, hprime⟩ := hNT
  have hCR := ModularCurve.XHDRModelAtP.exists_read_chart_mul_eq_and_isUnit_germ_and_smul_eq_and_evalAt_eq_of_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄
  obtain ⟨hgen', h1, -, -, -⟩ := hCR
  letI : Algebra B ↥(xHFunctionFieldBar M H) := emb.toAlgebra
  obtain ⟨r₀, s₀, hs₀, hgs⟩ := hgfrac

  have hunit : ∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → σB ϖ' ∉ P →
      (∃ r s : B, s ∉ P ∧ g * algebraMap B ↥(xHFunctionFieldBar M H) s = algebraMap B ↥(xHFunctionFieldBar M H) r) ∧
      (∃ r s : B, s ∉ P ∧ g⁻¹ * algebraMap B ↥(xHFunctionFieldBar M H) s = algebraMap B ↥(xHFunctionFieldBar M H) r) := by
    intro P hP hP0 hϖP
    obtain ⟨W, hrat, s, hs1, hs2, hs3, χ, ⟨-, -, -, hfrac⟩, hker⟩ := hprime P hP hP0 hϖP
    have h0 : W.ord g = 0 := hord W hrat s hs1 hs2 hs3
    have hgW : g ∈ W.toValuationSubring := AlgebraicCurve.Place.mem_of_ord_nonneg W hg h0.symm.le
    have hgiW : g⁻¹ ∈ W.toValuationSubring :=
      AlgebraicCurve.Place.mem_of_ord_nonneg W (inv_ne_zero hg) (by rw [AlgebraicCurve.Place.ord_inv, h0, neg_zero])
    have hr₀ : emb r₀ ≠ 0 := by
      rw [← hgs]; exact mul_ne_zero hg (fun h => hs₀ (hemb (by rw [h, map_zero])))
    have hgifrac : ∃ r s : B, s ≠ 0 ∧ g⁻¹ * emb s = emb r := by
      refine ⟨s₀, r₀, fun h => hr₀ (by rw [h, map_zero]), ?_⟩
      rw [← hgs, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]
    constructor
    · obtain ⟨r, s', hs', hx⟩ := hfrac g hgW ⟨r₀, s₀, hs₀, hgs⟩
      exact ⟨r, s', fun hmem => hs' ((hker s').mp hmem), hx⟩
    · obtain ⟨r, s', hs', hx⟩ := hfrac g⁻¹ hgiW hgifrac
      exact ⟨r, s', fun hmem => hs' ((hker s').mp hmem), hx⟩
  obtain ⟨w, a, b, nn, k, hab, hmono⟩ :=
    IsLocalRing.exists_units_forall_mul_const_pow_eq_mul_monomial_of_ringEquiv_adicCompletion_uvCrossingModel_of_forall_prime_mem_localization
      (B := B) (K := ↥(xHFunctionFieldBar M H)) hemb π' hπ' E' hE' ι' (σB ϖ') 1 le_rfl w₀ (by rw [pow_one]; exact hϖB) g hg ⟨r₀, s₀, hs₀, hgs⟩ hunit

  have hpL : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hϖ0 : ϖ' ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field O'
    rw [hϖ', h0, Ideal.span_singleton_eq_bot]
  have hϖL : ((ιA' ϖ' : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    exact hϖ0 (hιinj (by rw [map_zero]; exact_mod_cast h0))
  refine ⟨(b : ℤ) - a, (((p : ℕ) : AlgebraicClosure ℚ) ^ e) ^ a * ((ιA' ϖ' : ↥A) : AlgebraicClosure ℚ) ^ ((nn : ℤ) - k), ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hpL)) (zpow_ne_zero _ hϖL)
  intro W hrat s hs1 hs2 hs3
  obtain ⟨χ, ψ, hloc, hcomp, hψ, hev, hfrac⟩ := hχ W hrat s hs1 hs2 hs3
  have h0 : W.ord g = 0 := hord W hrat s hs1 hs2 hs3
  have hgW : g ∈ W.toValuationSubring := AlgebraicCurve.Place.mem_of_ord_nonneg W hg h0.symm.le
  obtain ⟨r, s', hs', hx⟩ := hfrac g hgW ⟨r₀, s₀, hs₀, hgs⟩
  have hm := hmono r s' hx

  let ψ' : UVCrossingModel W' (π' ^ E') →+* S := ψ.comp ι'.symm.toRingHom
  have hψ'ι : ∀ z, ψ' (ι' z) = ψ z := fun z => by
    show ψ (ι'.symm (ι' z)) = _
    rw [RingEquiv.symm_apply_apply]
  have hψB : ∀ bb : B, ψ (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) bb) = jA (χ bb) :=
    fun bb => RingHom.congr_fun hψ bb
  have hVv : ψ' (UVCrossingModel.V (π' ^ E')) = jA (χ bv) := by rw [← hbv, hψ'ι, hψB]
  have hUu : ψ' (UVCrossingModel.U (π' ^ E')) * ψ' wu = jA (χ bu) := by rw [← map_mul, ← hbu, hψ'ι, hψB]
  have hCc : ψ' w₀ * ψ' (UVCrossingModel.const (π' ^ E') π') = jA (ιA' ϖ') := by
    rw [← map_mul, ← hϖB, hψ'ι, hψB]
    exact congrArg jA (RingHom.congr_fun hcomp ϖ')
  have hmS := congrArg ψ' hm
  simp only [map_mul, map_pow, hψ'ι, hψB] at hmS

  let uw : Sˣ := Units.map ψ'.toMonoidHom w
  let uw₀ : Sˣ := Units.map ψ'.toMonoidHom w₀
  let uwu : Sˣ := Units.map ψ'.toMonoidHom wu
  have huw : (uw : S) = ψ' w := rfl
  have huw₀ : (uw₀ : S) = ψ' w₀ := rfl
  have huwu : (uwu : S) = ψ' wu := rfl

  let α : ↥A := χ r * ιA' ϖ' ^ k
  let β : ↥A := χ s' * χ bu ^ a * χ bv ^ b * ιA' ϖ' ^ nn
  have hkey : jA α * (uw₀ ^ nn * uwu ^ a : Sˣ) = jA β * (uw * uw₀ ^ k : Sˣ) := by
    simp only [α, β, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, huw, huw₀, huwu, ← hVv, ← hUu, ← hCc]

    linear_combination (ψ' w₀) ^ k * (ψ' w₀) ^ nn * (ψ' wu) ^ a * hmS
  have hkey' : jA α = jA β * ((uw * uw₀ ^ k) * (uw₀ ^ nn * uwu ^ a)⁻¹ : Sˣ) := by
    rw [Units.val_mul, ← mul_assoc, ← hkey, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨v, hv⟩ := hdesc α β _ hkey'

  have hevr := (hev r).2
  have hevs := (hev s').2
  have hevu : W.evalAt (emb bu) = ((χ bu : ↥A) : AlgebraicClosure ℚ) := (hev bu).2
  have hevv : W.evalAt (emb bv) = ((χ bv : ↥A) : AlgebraicClosure ℚ) := (hev bv).2
  have hsL : ((χ s' : ↥A) : AlgebraicClosure ℚ) ≠ 0 := fun h => hs' (by exact_mod_cast h)
  have hgval : W.evalAt g * ((χ s' : ↥A) : AlgebraicClosure ℚ) = ((χ r : ↥A) : AlgebraicClosure ℚ) := by
    rw [← hevs, ← hevr, ← AlgebraicCurve.Place.evalAt_mul W hrat hgW (hev s').1, hx]
  have hxy : ((χ bv : ↥A) : AlgebraicClosure ℚ) * ((χ bu : ↥A) : AlgebraicClosure ℚ) = ((p : ℕ) : AlgebraicClosure ℚ) ^ e := by
    rw [← hevv, ← hevu, ← AlgebraicCurve.Place.evalAt_mul W hrat (hev bv).1 (hev bu).1, hembv, hembu, h1,
      AlgebraicCurve.Place.evalAt_algebraMap]
  have hpeq : param = emb bv := hembv.symm
  have hparam : W.evalAt param = ((χ bv : ↥A) : AlgebraicClosure ℚ) := by rw [hpeq]; exact hevv
  have hyL : ((χ bv : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0; apply pow_ne_zero e hpL; rw [← hxy, h0, zero_mul]
  have hvL : (α : AlgebraicClosure ℚ) = (β : AlgebraicClosure ℚ) * ((v : ↥A) : AlgebraicClosure ℚ) := by exact_mod_cast congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hv
  simp only [α, β, MulMemClass.coe_mul, SubmonoidClass.coe_pow] at hvL
  have hgoal : W.evalAt g * ((((p : ℕ) : AlgebraicClosure ℚ) ^ e) ^ a * ((ιA' ϖ' : ↥A) : AlgebraicClosure ℚ) ^ ((nn : ℤ) - k))⁻¹ *
      W.evalAt param ^ (-((b : ℤ) - a)) = ((v : ↥A) : AlgebraicClosure ℚ) := by
    have hXa : ((χ bu : ↥A) : AlgebraicClosure ℚ) ^ a * ((χ bv : ↥A) : AlgebraicClosure ℚ) ^ a = (((p : ℕ) : AlgebraicClosure ℚ) ^ e) ^ a := by
      rw [← mul_pow, mul_comm, hxy]
    have hG : W.evalAt g = ((χ r : ↥A) : AlgebraicClosure ℚ) * (((χ s' : ↥A) : AlgebraicClosure ℚ))⁻¹ := by
      rw [← hgval, mul_assoc, mul_inv_cancel₀ hsL, mul_one]
    have hY : ((χ bv : ↥A) : AlgebraicClosure ℚ) ^ (-((b : ℤ) - a)) = ((χ bv : ↥A) : AlgebraicClosure ℚ) ^ a * (((χ bv : ↥A) : AlgebraicClosure ℚ) ^ b)⁻¹ := by
      rw [zpow_neg, zpow_sub₀ hyL, zpow_natCast, zpow_natCast, inv_div, div_eq_mul_inv]
    have hPi : ((ιA' ϖ' : ↥A) : AlgebraicClosure ℚ) ^ ((nn : ℤ) - k) = ((ιA' ϖ' : ↥A) : AlgebraicClosure ℚ) ^ nn * (((ιA' ϖ' : ↥A) : AlgebraicClosure ℚ) ^ k)⁻¹ := by
      rw [zpow_sub₀ hϖL, zpow_natCast, zpow_natCast, div_eq_mul_inv]
    rw [hparam, hY, hPi, hG]
    field_simp
    linear_combination ((χ bv : ↥A) : AlgebraicClosure ℚ) ^ a * hvL
      + (((χ s' : ↥A) : AlgebraicClosure ℚ) * ((ιA' ϖ' : ↥A) : AlgebraicClosure ℚ) ^ nn * ((χ bv : ↥A) : AlgebraicClosure ℚ) ^ b * ((v : ↥A) : AlgebraicClosure ℚ)) * hXa
  have hfinal : ∃ h : W.evalAt g * ((((p : ℕ) : AlgebraicClosure ℚ) ^ e) ^ a * ((ιA' ϖ' : ↥A) : AlgebraicClosure ℚ) ^ ((nn : ℤ) - k))⁻¹ *
      W.evalAt param ^ (-((b : ℤ) - a)) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
    rw [hgoal]
    exact ⟨(v : ↥A).2, by simpa using Units.isUnit v⟩
  exact hfinal

end S_ModularCurve_XHDRModelAtP_exists_zpow_unit_principle_evalAt_read_chart_of_section_of_chart
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_zpow_unit_principle_evalAt_read_chart_of_section_of_chart (solution)
