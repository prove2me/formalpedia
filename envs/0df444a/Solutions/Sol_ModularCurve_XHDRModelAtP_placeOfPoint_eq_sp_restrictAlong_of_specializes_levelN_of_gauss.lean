-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.placeOfPoint_eq_sp_restrictAlong_of_specializes_levelN_of_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3911758a-a440-5bdc-80e2-7636b339a886

import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd
import Theorems.Thm_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
import Theorems.Thm_AlgebraicCurve_CurveModel_eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_baseChange
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffMap_residue
import Theorems.Thm_ModularCurve_placeReduction_unique_of_forall_mapDomain_eq_ord_gammaH_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_placeOfPoint_eq_sp_restrictAlong_of_specializes_levelN_of_gauss
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun"
p2m_attr_erase "simp" "KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel Opposite

open scoped MatrixGroups

namespace PlaceSpecLevelN

universe u

theorem not_dvd_div {p M : ℕ} (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ¬ p ∣ M / p := by
  intro h
  apply hpM2
  have := Nat.mul_dvd_mul_left p h
  rwa [Nat.mul_div_cancel' hpM, ← pow_two] at this

theorem gamma1_le_gammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    CongruenceSubgroup.Gamma1 N ≤ CohCarrier.GammaH N H := by
  intro γ hγ
  rw [CohCarrier.mem_GammaH_iff]
  obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem N γ).mp hγ
  refine ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
  have h1 : CohCarrier.gamma0Units N ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr h10⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    simpa [CongruenceSubgroup.Gamma0Map] using h11
  rw [h1]
  exact one_mem H

theorem exists_eq_specMap_comp {B : Type} [CommRing B] {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}}
    (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι] (f : Spec (CommRingCat.of A) ⟶ X)
    (h : f.base (IsLocalRing.closedPoint A) ∈ Set.range ι.base) :
    ∃ β : B →+* A, f = Spec.map (CommRingCat.ofHom β) ≫ ι := by
  have hrange : Set.range f.base ⊆ Set.range ι.base := by
    rintro _ ⟨x, rfl⟩
    have hs : f.base x ⤳ f.base (IsLocalRing.closedPoint A) :=
      (IsLocalRing.specializes_closedPoint x).map f.base.hom.continuous
    exact hs.mem_open ι.isOpenEmbedding.isOpen_range h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ι f hrange)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem mem_nonunits_iff' {K : Type*} [Field K] (O : ValuationSubring K) (x : K) :
    x ∈ O.nonunits ↔ x ∈ O ∧ (x ≠ 0 → x⁻¹ ∉ O) := by
  rw [ValuationSubring.mem_nonunits_iff]
  constructor
  · intro h
    refine ⟨(O.valuation_le_one_iff x).mp h.le, fun hx hinv => ?_⟩
    have h1 := (O.valuation_le_one_iff x⁻¹).mpr hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hx))] at h1
    exact not_le.mpr h h1
  · rintro ⟨hx, hinv⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · rw [lt_iff_not_ge]
      intro h1
      apply hinv hx0
      rw [← O.valuation_le_one_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hx0))]
      exact h1

theorem mem_nonunits_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring.nonunits ↔ φ x ∈ w.toValuationSubring.nonunits := by
  have hval : (w.restrictAlong φ hφ).toValuationSubring = w.toValuationSubring.comap φ.toRingHom := rfl
  rw [hval, mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀, ne_eq, map_eq_zero]

theorem section_ext {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] (a b : Spec (CommRingCat.of K) ⟶ X) (ha : a ≫ f = 𝟙 _) (hb : b ≫ f = 𝟙 _)
    (h : a.base (IsLocalRing.closedPoint K) = b.base (IsLocalRing.closedPoint K)) : a = b := by
  have := (pointEquivClosedPoint f).injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext h)
  exact congrArg Subtype.val this

theorem app_germToFunctionField_eq {X Z : Scheme.{u}} [IrreducibleSpace Z] (g : Z ⟶ X)
    {V V' : X.Opens} (hle : V' ≤ V)
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V))] [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V'))] :
    g.app V ≫ Z.germToFunctionField (g ⁻¹ᵁ V) =
      X.presheaf.map (homOfLE hle).op ≫ g.app V' ≫ Z.germToFunctionField (g ⁻¹ᵁ V') := by
  rw [Scheme.Hom.naturality_assoc]
  simp only [Scheme.germToFunctionField]
  rw [TopCat.Presheaf.germ_res]

theorem appIso_inv_appLE_of_eq {X : Scheme.{u}} {B B' : Type u} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι]
    (φ : B →+* B') (κ : Spec (CommRingCat.of B') ⟶ X)
    (hκ : κ = Spec.map (CommRingCat.ofHom φ) ≫ ι) (e : (⊤ : (Spec (CommRingCat.of B')).Opens) ≤ κ ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv ≫ κ.appLE (ι ''ᵁ ⊤) ⊤ e =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).inv := by
  subst hκ
  have h2 : (Spec.map (CommRingCat.ofHom φ) ≫ ι).appLE (ι ''ᵁ ⊤) ⊤ e =
      ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) ≫ (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
  have h3 : (ι.appIso ⊤).inv ≫ ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) = 𝟙 _ := by
    rw [Scheme.Hom.appIso_inv_appLE]
    convert (Spec (CommRingCat.of B)).presheaf.map_id _ <;> first | rfl | exact Subsingleton.elim _ _ | skip
  have h4 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [h2, ← Category.assoc (ι.appIso ⊤).inv, h3, Category.id_comp, h4, ← Scheme.ΓSpecIso_inv_naturality]

theorem germToFunctionField_app_eq_of_eq_comp {X X' Z : Scheme.{u}} [IrreducibleSpace Z]
    (g : Z ⟶ X) (π : X ⟶ X') (f : Z ⟶ X') (hf : f = g ≫ π)
    {B B' : Type u} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι]
    (ι' : Spec (CommRingCat.of B') ⟶ X') [IsOpenImmersion ι']
    (φ : B' →+* B) (hsq : ι ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ ι')
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (ι ''ᵁ ⊤)))]
    [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ (ι' ''ᵁ ⊤)))] (b : B') :
    Z.germToFunctionField (f ⁻¹ᵁ (ι' ''ᵁ ⊤))
        ((f.app (ι' ''ᵁ ⊤)).hom ((ι'.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B')).inv b))) =
      Z.germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (φ b)))) := by
  subst hf
  have hle : ι ''ᵁ ⊤ ≤ π ⁻¹ᵁ (ι' ''ᵁ ⊤) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
    rintro _ ⟨x, rfl⟩
    show (ι ≫ π).base x ∈ Set.range ι'.base
    rw [hsq]
    exact ⟨_, rfl⟩
  haveI hne : Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (π ⁻¹ᵁ (ι' ''ᵁ ⊤)))) :=
    ‹Nonempty (Scheme.Opens.toScheme ((g ≫ π) ⁻¹ᵁ (ι' ''ᵁ ⊤)))›

  have key : (Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ (ι'.appIso ⊤).inv ≫ π.app (ι' ''ᵁ ⊤) ≫
      X.presheaf.map (homOfLE hle).op =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv := by
    rw [← cancel_mono (ι.appIso ⊤).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE π, Scheme.Hom.appLE_comp_appLE]
    exact appIso_inv_appLE_of_eq ι' φ (ι ≫ π) hsq _

  have H1 : (g ≫ π).app (ι' ''ᵁ ⊤) ≫ Z.germToFunctionField ((g ≫ π) ⁻¹ᵁ (ι' ''ᵁ ⊤)) =
      π.app (ι' ''ᵁ ⊤) ≫ g.app (π ⁻¹ᵁ (ι' ''ᵁ ⊤)) ≫ Z.germToFunctionField (g ⁻¹ᵁ (π ⁻¹ᵁ (ι' ''ᵁ ⊤))) := rfl
  have H2 : (Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ (ι'.appIso ⊤).inv ≫ (g ≫ π).app (ι' ''ᵁ ⊤) ≫
      Z.germToFunctionField ((g ≫ π) ⁻¹ᵁ (ι' ''ᵁ ⊤)) =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv ≫ g.app (ι ''ᵁ ⊤) ≫
        Z.germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤)) := by
    rw [H1, app_germToFunctionField_eq g hle, reassoc_of% key]
  have H3 := congrArg (fun k : CommRingCat.of B' ⟶ Z.functionField => k.hom b) H2
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using H3

end PlaceSpecLevelN

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP in
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
    (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
    (hxA : barPt A ≫ xA.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1)
    (xκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hxκ : xκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ xA.1)
    (hxκ' : xκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ).base P0.1 = xκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = sp ((𝔛.Meta.pointEquivPlace y).restrictAlong α hα) := by
  classical
  haveI := 𝔛.isProper0
  haveI := 𝔛.efib_iso A hA ρ hρ
  haveI := 𝔛.Mfib_chart_nonempty A hA ρ hρ
  haveI := 𝔛.Meta_chart_nonempty
  have hp' : ¬ p ∣ M / p := PlaceSpecLevelN.not_dvd_div hpM hpM2
  have hΓ₁ : CongruenceSubgroup.Gamma1 (M / p) ≤ ΓN p M H hpM :=
    PlaceSpecLevelN.gamma1_le_gammaH (M / p) (infSubgroup p M H hpM)
  have hΓ₀ : ΓN p M H hpM ≤ CongruenceSubgroup.Gamma0 (M / p) := CohCarrier.GammaH_le_Gamma0 _

  obtain ⟨r, hr, hfin, hinf⟩ :=
    ModularCurve.exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd (M / p) (ΓN p M H hpM) hΓ₁ hΓ₀ p hp'
      (jAt (ΓN p M H hpM) hj) (coe_jAt _ _) A hA

  have hsp : sp = r := by
    refine ModularCurve.placeReduction_unique_of_forall_mapDomain_eq_ord_gammaH_of_not_dvd (M / p)
      (infSubgroup p M H hpM) p hp' A hA sp r ?_ hr.2
    intro y hy hyk hne D hD Q
    obtain ⟨hint, hresid⟩ := hq y hy
    have hRy : R.residue ⟨_, hint⟩ =
        (⟨coeffMap (IsLocalRing.residue ↥A) y, hyk⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
      Subtype.ext hresid
    have hne' : R.residue ⟨_, hint⟩ ≠ 0 := by
      rw [hRy]
      exact fun h => hne (congrArg Subtype.val h)
    rw [← hRy]
    exact hdiv ⟨_, hint⟩ hne' D hD Q

  obtain ⟨ρ', hρ', Ms, es, hes, hes', πFin, πInf, hall⟩ :=
    ModularCurve.exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
      (M / p) (ΓN p M H hpM) hΓ₁ hΓ₀ p hp' (jAt (ΓN p M H hpM) hj) (coe_jAt _ _)
  obtain ⟨hliftF, hliftI, -⟩ := hall A hA
  rw [hsp]

  obtain ⟨z, hzP⟩ : ∃ z, pointEquivClosedPoint (𝔛.Mfib A hA ρ hρ).toBase z = P0 :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  have hzP0 : (𝔛.Mfib A hA ρ hρ).pointEquivPlace z = (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 := by
    rw [CurveModel.pointEquivPlace_apply, hzP]
  have hzbase : z.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) = P0.1 :=
    congrArg Subtype.val hzP

  have hze : z.1 ≫ 𝔛.efib A hA ρ hρ = xκ := by
    refine PlaceSpecLevelN.section_ext (pullback.snd (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) _ _ ?_ hxκ' ?_
    · rw [Category.assoc, 𝔛.hefib]
      exact z.2
    · rw [← hP0, ← hzbase]
      rfl
  have hzfst : z.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ xA.1 := by
    rw [← Category.assoc, hze, hxκ]

  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (XHDRLevel.R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))
      (jAt (ΓN p M H hpM) hj) (xA.1.base (IsLocalRing.closedPoint ↥A)) with hF | hI
  · obtain ⟨βx, hβx⟩ := PlaceSpecLevelN.exists_eq_specMap_comp (ιFin p (ΓN p M H hpM) hj) xA.1 hF

    have hyβ : y.1 ≫ (𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) =
        Spec.map (CommRingCat.ofHom (A.subtype.comp βx)) ≫ ιFin p (ΓN p M H hpM) hj := by
      rw [← hxA, hβx, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ)))) ≫ 𝔛.π.1) ⁻¹ᵁ
        ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))) :=
      ⟨⟨y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)), by
        show (y.1 ≫ (𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈
          (ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤
        rw [hyβ, Scheme.Hom.image_top_eq_opensRange]
        exact ⟨_, rfl⟩⟩⟩
    have hgen := fun b =>
      𝔛.Meta.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
        (𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) (ιFin p (ΓN p M H hpM) hj) y (A.subtype.comp βx) hyβ b

    have hread : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
        ((𝔛.Meta.ffEquiv.symm
            (𝔛.Meta.C.germToFunctionField
              ((𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
              (((𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1).app ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιFin p (ΓN p M H hpM) hj).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj))).inv b))))
            : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := by
      intro b
      rw [PlaceSpecLevelN.germToFunctionField_app_eq_of_eq_comp (𝔛.eeta ≫ pullback.fst _ _) 𝔛.π.1
        (𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) (Category.assoc _ _ _).symm (ιFin p (ΓM M H) hj)
        (ιFin p (ΓN p M H hpM) hj) 𝔛.iota0.toRingHom 𝔛.pi_chart, 𝔛.Meta_pin]
      exact congrArg (fun t : LaurentSeries ℚ => coeffEmb (AlgebraicClosure ℚ) t) (𝔛.iota0_spec b)
    have hcen : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))).2⟩ :
            ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) -
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
            ((βx b : ↥A) : AlgebraicClosure ℚ) ∈
          ((𝔛.Meta.pointEquivPlace y).restrictAlong α hα).toValuationSubring.nonunits := by
      intro b
      rw [PlaceSpecLevelN.mem_nonunits_restrictAlong_iff, map_sub, AlgHom.commutes]
      convert hgen b using 2 <;> first | (with_reducible_and_instances rfl) | rfl | (apply Subtype.ext; rw [hα_coe, hread]) | skip
    have hcen' := hfin ((𝔛.Meta.pointEquivPlace y).restrictAlong α hα) βx hcen

    have hz' : z.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp βx)) ≫ ιFin p (ΓN p M H hpM) hj := by
      rw [hzfst, hβx, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rw [← hzP0]
    symm
    refine AlgebraicCurve.CurveModel.eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_baseChange
      ((IsLocalRing.residue ↥A).comp ρ) (toBase p (ΓN p M H hpM) hj) (ιFin p (ΓN p M H hpM) hj) (𝔛.Mfib A hA ρ hρ) (𝔛.efib A hA ρ hρ)
      (𝔛.hefib A hA ρ hρ) z _ (by simpa only [Category.assoc] using hz') _ (fun b => ?_)
    obtain ⟨yb, hyb, -⟩ := hliftF b
    exact hcen' b yb _ hyb (𝔛.Mfib_pin A hA ρ hρ b yb hyb)
  · obtain ⟨βx, hβx⟩ := PlaceSpecLevelN.exists_eq_specMap_comp (ιInf p (ΓN p M H hpM) hj) xA.1 hI

    have hyβ : y.1 ≫ (𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) =
        Spec.map (CommRingCat.ofHom (A.subtype.comp βx)) ≫ ιInf p (ΓN p M H hpM) hj := by
      rw [← hxA, hβx, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ)))) ≫ 𝔛.π.1) ⁻¹ᵁ
        ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))) :=
      ⟨⟨y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)), by
        show (y.1 ≫ (𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈
          (ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤
        rw [hyβ, Scheme.Hom.image_top_eq_opensRange]
        exact ⟨_, rfl⟩⟩⟩
    have hgen := fun b =>
      𝔛.Meta.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
        (𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) (ιInf p (ΓN p M H hpM) hj) y (A.subtype.comp βx) hyβ b

    have hread : ∀ b : ↥(chartAlgInf p (ΓN p M H hpM) hj),
        ((𝔛.Meta.ffEquiv.symm
            (𝔛.Meta.C.germToFunctionField
              ((𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
              (((𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b))))
            : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := by
      intro b
      obtain ⟨hne, hb⟩ :=
        𝔛.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb p M H hpM hj (𝔛.iotaInf.toRingHom b)
      haveI := hne
      rw [PlaceSpecLevelN.germToFunctionField_app_eq_of_eq_comp (𝔛.eeta ≫ pullback.fst _ _) 𝔛.π.1
        (𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) (Category.assoc _ _ _).symm (ιInf p (ΓM M H) hj)
        (ιInf p (ΓN p M H hpM) hj) 𝔛.iotaInf.toRingHom 𝔛.pi_chartInf, hb]
      exact congrArg (fun t : LaurentSeries ℚ => coeffEmb (AlgebraicClosure ℚ) t) (𝔛.iotaInf_spec b)
    have hcen : ∀ b : ↥(chartAlgInf p (ΓN p M H hpM) hj),
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))).2⟩ :
            ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) -
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
            ((βx b : ↥A) : AlgebraicClosure ℚ) ∈
          ((𝔛.Meta.pointEquivPlace y).restrictAlong α hα).toValuationSubring.nonunits := by
      intro b
      rw [PlaceSpecLevelN.mem_nonunits_restrictAlong_iff, map_sub, AlgHom.commutes]
      convert hgen b using 2 <;> first | (with_reducible_and_instances rfl) | rfl | (apply Subtype.ext; rw [hα_coe, hread]) | skip
    have hcen' := hinf ((𝔛.Meta.pointEquivPlace y).restrictAlong α hα) βx hcen

    have hz' : z.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp βx)) ≫ ιInf p (ΓN p M H hpM) hj := by
      rw [hzfst, hβx, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))) :=
      ⟨⟨z.1.base (IsLocalRing.closedPoint (ResidueField ↥A)), by
        show (z.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈
          (ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤
        rw [hz', Scheme.Hom.image_top_eq_opensRange]
        exact ⟨_, rfl⟩⟩⟩
    rw [← hzP0]
    symm
    refine AlgebraicCurve.CurveModel.eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_baseChange
      ((IsLocalRing.residue ↥A).comp ρ) (toBase p (ΓN p M H hpM) hj) (ιInf p (ΓN p M H hpM) hj) (𝔛.Mfib A hA ρ hρ) (𝔛.efib A hA ρ hρ)
      (𝔛.hefib A hA ρ hρ) z _ (by simpa only [Category.assoc] using hz') _ (fun b => ?_)
    obtain ⟨yb, hyb, -⟩ := hliftI b
    exact hcen' b yb _ hyb
      (𝔛.coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffMap_residue p M H hpM hpM2 hj A hA ρ hρ b yb hyb)

end S_ModularCurve_XHDRModelAtP_placeOfPoint_eq_sp_restrictAlong_of_specializes_levelN_of_gauss
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_placeOfPoint_eq_sp_restrictAlong_of_specializes_levelN_of_gauss (solution)
