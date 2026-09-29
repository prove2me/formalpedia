-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isZeroSide_iff_isInftySide_smul_prolongationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3a5de1d6-c85f-5b65-a666-3ec233b38b87

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_XHDRModelAtP_isInftySide_of_isCuspidal_of_section_comp_zero
import Theorems.Thm_ModularCurve_XHDRModelAtP_isZeroSide_of_isCuspidal_of_section_comp_one
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isCuspidalPrime
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_XHDRModelAtP_isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isZeroSide_iff_isInftySide_smul_prolongationDatum
p2m_attr_erase "instance" "ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01"
p2m_attr_erase "simp" "CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun"
p2m_attr_erase "simp" "KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace CuspSwapBlr

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem fibreMap_comp (φ ψ : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓM M H) hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (Γ := ΓM M H) (hj := hj) φ toκ ≫ XHDRLevel.fibreMap ψ toκ =
      XHDRLevel.fibreMap (⟨φ.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, φ.2]⟩ : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓM M H) hj)) toκ := by
  apply pullback.hom_ext
  · simp only [XHDRLevel.fibreMap, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    rfl
  · simp only [XHDRLevel.fibreMap, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
    simp

theorem fibreMap_id {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (Γ := ΓM M H) (hj := hj) (⟨𝟙 _, by rw [Category.id_comp]⟩ : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓM M H) hj)) toκ = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [XHDRLevel.fibreMap, pullback.map]

theorem fibreMap_overOfIso_hom_inv (e : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (he : e.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (overOfIso e he) toκ ≫ XHDRLevel.fibreMap (overOfIso e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq, he])) toκ = 𝟙 _ := by
  rw [fibreMap_comp]
  convert fibreMap_id (p := p) (M := M) (H := H) (hj := hj) toκ using 2
  simp [overOfIso]

theorem fibreMap_overOfIso_inv_hom (e : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (he : e.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (overOfIso e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq, he])) toκ ≫ XHDRLevel.fibreMap (overOfIso e he) toκ = 𝟙 _ := by
  rw [fibreMap_comp]
  convert fibreMap_id (p := p) (M := M) (H := H) (hj := hj) toκ using 2
  simp [overOfIso]

theorem translate (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A)
    (e : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (he : e.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _) :
    ∃ (y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u'.1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1)
      (_ : uκ' ≫ pullback.snd _ _ = 𝟙 _),
      u'.1 = u.1 ≫ e.hom ∧ uκ' = uκ ≫ XHDRLevel.fibreMap (overOfIso e he) ((IsLocalRing.residue ↥A).comp ρ) ∧
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ e.hom := by
  haveI := 𝔛.eeta_iso

  set g := y.1 ≫ 𝔛.eeta with hg
  have hcond : (g ≫ pullback.fst _ _ ≫ e.hom) ≫ toBase p (ΓM M H) hj =
      (g ≫ pullback.snd _ _) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    simp only [Category.assoc, he]
    rw [pullback.condition]
  set g' := pullback.lift (g ≫ pullback.fst _ _ ≫ e.hom) (g ≫ pullback.snd _ _) hcond with hg'
  refine ⟨⟨g' ≫ inv 𝔛.eeta, ?_⟩, ⟨u.1 ≫ e.hom, by rw [Category.assoc, he, u.2]⟩, ?_,
    uκ ≫ XHDRLevel.fibreMap (overOfIso e he) ((IsLocalRing.residue ↥A).comp ρ), ?_, ?_, rfl, rfl, ?_⟩
  ·
    rw [← 𝔛.heeta]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hg', pullback.lift_snd, hg, Category.assoc, 𝔛.heeta]
    exact y.2
  ·
    show barPt A ≫ u.1 ≫ e.hom = (g' ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hg', pullback.lift_fst, hg, ← Category.assoc (barPt A), hu]
    simp only [Category.assoc]
  ·
    show (uκ ≫ XHDRLevel.fibreMap _ _) ≫ pullback.fst _ _ = Spec.map _ ≫ u.1 ≫ e.hom
    rw [Category.assoc, XHDRLevel.fibreMap, pullback.lift_fst, ← Category.assoc, huκ₁]
    simp [overOfIso]
  ·
    show (uκ ≫ XHDRLevel.fibreMap _ _) ≫ pullback.snd _ _ = 𝟙 _
    rw [Category.assoc, XHDRLevel.fibreMap, pullback.lift_snd, ← Category.assoc, huκ₂]
    simp
  · show (g' ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _ = _
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hg', pullback.lift_fst, hg]
    simp only [Category.assoc]

end CuspSwapBlr

namespace CuspSwapBlr

theorem comp_one_fibreMap_wInv
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    𝔛.comp A hA ρ hρ 1 ≫ XHDRLevel.fibreMap (overOfIso 𝔛.w.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq, 𝔛.w_over])) ((IsLocalRing.residue ↥A).comp ρ) =
      𝔛.comp A hA ρ hρ 0 := by
  rw [← 𝔛.comp_w A hA ρ hρ, Category.assoc, fibreMap_overOfIso_hom_inv, Category.comp_id]

set_option synthInstance.maxHeartbeats 1600000 in

theorem isInftySide_smul_of_isZeroSide
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hz : (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) W) :
    (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) (SemilinearAut.ofAlgAut θ • W) := by
  classical
  haveI := 𝔛.eeta_iso
  set y := 𝔛.Meta.pointEquivPlace.symm W with hy_def
  have hW : 𝔛.Meta.pointEquivPlace y = W := Equiv.apply_symm_apply _ _
  obtain ⟨u, hu, uκ, huκ₁, huκ₂, i, P0, hP0⟩ :=
    ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq p M H hpM hj 𝔛 A hA ρ hρ y
  have hcusp : (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y) := by
    rw [hW]; exact ModularCurve.JHPlaceSpecialization.isCuspidal_of_isCuspidalPrime p M H hpM A hA W hz.1

  have hi : i = 0 ∨ i = 1 := by
    rcases i with ⟨_ | _ | n, hn⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  rcases hi with rfl | rfl
  · exfalso
    have hinf := ModularCurve.XHDRModelAtP.isInftySide_of_isCuspidal_of_section_comp_zero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      y u hu uκ huκ₁ huκ₂ P0 hP0 hcusp
    rw [hW] at hinf
    exact ModularCurve.JHPlaceSpecialization.not_isInftySide_of_isZeroSide p M H hpM A hA W hz hinf

  have hnaff := (ModularCurve.XHDRModelAtP.isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      1 y u hu uκ huκ₁ huκ₂ P0 hP0).mp hcusp

  obtain ⟨y', u', hu', uκ', huκ₁', huκ₂', hu'eq, huκ'eq, hy'⟩ :=
    translate 𝔛 A ρ 𝔛.w.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq, 𝔛.w_over]) y u hu uκ huκ₁ huκ₂
  have hP0' : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by
    have hc := congrArg (fun F => F.base ((𝔛.efib A hA ρ hρ).base P0.1)) (comp_one_fibreMap_wInv p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ)
    rw [huκ'eq]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hP0 hc ⊢
    rw [← hP0]
    exact hc.symm
  have hplace : 𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y := by
    apply hwgen y y'
    rw [reassoc_of% hy']
    simp
  have hcusp' : (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y') :=
    (ModularCurve.XHDRModelAtP.isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      0 y' u' hu' uκ' huκ₁' huκ₂' P0 hP0').mpr hnaff
  have h := ModularCurve.XHDRModelAtP.isInftySide_of_isCuspidal_of_section_comp_zero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
    y' u' hu' uκ' huκ₁' huκ₂' P0 hP0' hcusp'
  rwa [hplace, hW] at h

set_option synthInstance.maxHeartbeats 1600000 in

theorem isZeroSide_inv_smul_of_isInftySide
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hinf : (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) W) :
    (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) ((SemilinearAut.ofAlgAut θ)⁻¹ • W) := by
  classical
  haveI := 𝔛.eeta_iso
  set y := 𝔛.Meta.pointEquivPlace.symm W with hy_def
  have hW : 𝔛.Meta.pointEquivPlace y = W := Equiv.apply_symm_apply _ _
  obtain ⟨u, hu, uκ, huκ₁, huκ₂, i, P0, hP0⟩ :=
    ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq p M H hpM hj 𝔛 A hA ρ hρ y
  have hcusp : (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y) := by
    rw [hW]; exact hinf.1
  have hi : i = 0 ∨ i = 1 := by
    rcases i with ⟨_ | _ | n, hn⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  rcases hi with rfl | rfl
  swap
  · exfalso
    have hz := ModularCurve.XHDRModelAtP.isZeroSide_of_isCuspidal_of_section_comp_one p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      y u hu uκ huκ₁ huκ₂ P0 hP0 hcusp
    rw [hW] at hz
    exact ModularCurve.JHPlaceSpecialization.not_isInftySide_of_isZeroSide p M H hpM A hA W hz hinf
  have hnaff := (ModularCurve.XHDRModelAtP.isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      0 y u hu uκ huκ₁ huκ₂ P0 hP0).mp hcusp

  obtain ⟨y', u', hu', uκ', huκ₁', huκ₂', hu'eq, huκ'eq, hy'⟩ := translate 𝔛 A ρ 𝔛.w 𝔛.w_over y u hu uκ huκ₁ huκ₂
  have hP0' : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by
    have hc := congrArg (fun F => F.base ((𝔛.efib A hA ρ hρ).base P0.1)) (𝔛.comp_w A hA ρ hρ)
    rw [huκ'eq]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hP0 hc ⊢
    rw [← hP0]
    exact hc.symm
  have hplace : 𝔛.Meta.pointEquivPlace y = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y' :=
    hwgen y' y hy'.symm
  have hplace' : 𝔛.Meta.pointEquivPlace y' = (SemilinearAut.ofAlgAut θ)⁻¹ • W := by
    rw [eq_inv_smul_iff, ← hplace, hW]
  have hcusp' : (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y') :=
    (ModularCurve.XHDRModelAtP.isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      1 y' u' hu' uκ' huκ₁' huκ₂' P0 hP0').mpr hnaff
  have h := ModularCurve.XHDRModelAtP.isZeroSide_of_isCuspidal_of_section_comp_one p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
    y' u' hu' uκ' huκ₁' huκ₂' P0 hP0' hcusp'
  rwa [hplace'] at h

theorem isZeroSide_iff_isInftySide_smul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) W ↔
      (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) (SemilinearAut.ofAlgAut θ • W) := by
  constructor
  · exact isInftySide_smul_of_isZeroSide p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen W
  · intro h
    have h' := isZeroSide_inv_smul_of_isInftySide p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen _ h
    rwa [inv_smul_smul] at h'

end CuspSwapBlr

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : (∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) W ↔ (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) (SemilinearAut.ofAlgAut θ • W) := by
  exact CuspSwapBlr.isZeroSide_iff_isInftySide_smul p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen W

end S_ModularCurve_XHDRModelAtP_isZeroSide_iff_isInftySide_smul_prolongationDatum
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isZeroSide_iff_isInftySide_smul_prolongationDatum (solution)
