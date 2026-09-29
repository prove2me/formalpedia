-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b74bb523-c2f0-5e8d-ab69-c0e74bc57595

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffMap_residue
import Theorems.Thm_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule"
p2m_attr_erase "instance" "KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective ModularCurve.XHDRLevel"
open scoped MatrixGroups

namespace CuspPoleRedH

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

theorem jqModC_ne_zero' (R : Type*) [CommRing R] [Nontrivial R] : jqModC R ≠ 0 := by
  intro h
  have h1 : (jqModC R).coeff (-1 : ℤ) = 1 := coeff_jqModC_neg_one R
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

theorem coeffEmb_jqModC (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L (jqModC ℚ) = jqModC L :=
  coeffMap_jqModC _

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun s : LaurentSeries S => s.coeff k) h
  simpa using this

theorem qExpand_jqModC (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] :
    qExpand κ p (jqModC κ) = jqModC κ ^ p := by
  refine qExpand_eq_pow_of_coeff_fixed κ p _ (fun k => ?_)
  rw [jqModC_eq_map_intCast, HahnSeries.map_coeff, eq_intCast, ← frobenius_def, map_intCast]

theorem frob_eq_pow_of_coe_eq {κ : Type*} [Field κ] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime] [CharP κ p]
    (g : ↥(qExpFunctionFieldC κ Γ)) (e : ℤ) (hg : (g : LaurentSeries κ) = jqModC κ ^ e) :
    qExpFrobeniusModL κ Γ p g = g ^ p := by
  apply Subtype.ext
  rw [coe_qExpFrobeniusModL]
  push_cast
  rw [hg, map_zpow₀, qExpand_jqModC, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]

section IntermediateFieldFacts

variable {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))

theorem coe_algebraMap_eq_single (a : K) : ((algebraMap K F a : F) : LaurentSeries K) = HahnSeries.single 0 a := by
  rw [← algebraMap_laurentSeries_eq_single]
  rfl

theorem ne_algebraMap_of_coe_eq_jqModC (x : F) (hx : (x : LaurentSeries K) = jqModC K) (a : K) :
    x ≠ algebraMap K F a := by
  intro h
  have h1 := congrArg (fun t : F => (t : LaurentSeries K).coeff (-1)) h
  try simp only at h1
  rw [hx, coeff_jqModC_neg_one, coe_algebraMap_eq_single, HahnSeries.coeff_single_of_ne (by decide)] at h1
  exact one_ne_zero h1

theorem ne_zero_of_coe_eq_jqModC (x : F) (hx : (x : LaurentSeries K) = jqModC K) : x ≠ 0 := by
  intro h
  rw [h] at hx
  exact jqModC_ne_zero' K (by simpa using hx.symm)

theorem coe_inv_eq_of_coe_eq_inv (x : F) (hx : (x : LaurentSeries K) = (jqModC K)⁻¹) :
    ((x⁻¹ : F) : LaurentSeries K) = jqModC K := by
  push_cast
  rw [hx, inv_inv]

end IntermediateFieldFacts

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_nonunits_iff' (O : ValuationSubring F) (x : F) :
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

theorem mem_nonunits_restrictAlong_iff {F' : Type*} [Field F'] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring.nonunits ↔ φ x ∈ w.toValuationSubring.nonunits := by
  have hval : (w.restrictAlong φ hφ).toValuationSubring = w.toValuationSubring.comap φ.toRingHom := rfl
  rw [hval, mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀, ne_eq, map_eq_zero]

theorem pow_mem_nonunits_iff (O : ValuationSubring F) (x : F) {n : ℕ} (hn : n ≠ 0) :
    x ^ n ∈ O.nonunits ↔ x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff, map_pow]
  refine ⟨fun h => ?_, fun h => pow_lt_one₀ zero_le' h hn⟩
  by_contra h'
  exact not_le.mpr h (one_le_pow₀ (not_lt.mp h'))

theorem hasValue_of_sub_mem_nonunits (v : Place K F) {g : F} {c : K}
    (h : g - algebraMap K F c ∈ v.toValuationSubring.nonunits) : v.HasValue g c := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
  have hg : g ∈ v.toValuationSubring := by
    have := add_mem hmem (v.algebraMap_mem' c)
    simpa using this
  refine ⟨hg, ?_⟩
  have hres0 : IsLocalRing.residue v.toValuationSubring ⟨_, hmem⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  have hsplit : (⟨g, hg⟩ : v.toValuationSubring) = ⟨g - algebraMap K F c, hmem⟩ + algebraMap K v.toValuationSubring c := by
    ext
    simp
  rw [hsplit, map_add, hres0, zero_add, Place.residue_algebraMap]

theorem not_mem_of_inv_mem_nonunits (v : Place K F) {g : F} (hg : g ≠ 0)
    (h : g⁻¹ ∈ v.toValuationSubring.nonunits) : g ∉ v.toValuationSubring := by
  have h2 := ((mem_nonunits_iff' _ _).mp h).2 (inv_ne_zero hg)
  rwa [inv_inv] at h2

theorem ne_zero_of_ord_ne_zero (v : Place K F) {f : F} (h : v.ord f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h (Place.ord_zero v)

theorem hasValue_of_ord_sub_pos (v : Place K F) (g : F) (b : K)
    (h : 0 < v.ord (g - algebraMap K F b)) : v.HasValue g b := by
  have hne : g - algebraMap K F b ≠ 0 := ne_zero_of_ord_ne_zero v h.ne'
  have hmem : g - algebraMap K F b ∈ v.toValuationSubring := v.mem_of_ord_nonneg hne h.le
  have hgmem : g ∈ v.toValuationSubring := by
    have := add_mem hmem (v.algebraMap_mem' b)
    simpa using this
  refine ⟨hgmem, ?_⟩
  have hnu : ¬ IsUnit (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (g - algebraMap K F b) = 0 at h0
    omega
  have hmax : (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hres0 : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F b, hmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  have hsplit : (⟨g, hgmem⟩ : v.toValuationSubring) =
      ⟨g - algebraMap K F b, hmem⟩ + algebraMap K v.toValuationSubring b := by
    ext
    simp
  rw [hsplit, map_add, hres0, zero_add, Place.residue_algebraMap]

theorem ord_sub_pos_of_hasValue (v : Place K F) {g : F} {b : K} (h : v.HasValue g b)
    (hne : g ≠ algebraMap K F b) : 0 < v.ord (g - algebraMap K F b) := by
  obtain ⟨hg, hres⟩ := h
  have hmem : g - algebraMap K F b ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' b)
  have hres0 : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F b, hmem⟩ = 0 := by
    have hsplit : (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring b := by
      ext
      simp
    rw [hsplit, map_sub, hres, Place.residue_algebraMap, sub_self]
  have hmax : (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres0
  have hnu : ¬ IsUnit (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) :=
    (IsLocalRing.mem_maximalIdeal _).mp hmax
  have hne' : g - algebraMap K F b ≠ 0 := sub_ne_zero.mpr hne
  have hnn : 0 ≤ v.ord (g - algebraMap K F b) := v.ord_nonneg_of_mem hmem
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hne' heq.symm
    exact hnu hu

end PlaceFacts

section Fibre

variable {κ : Type*} [Field κ] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime] [CharP κ p] [IsAlgClosed κ]

theorem frob_pull (v0 vz : Place κ ↥(qExpFunctionFieldC κ Γ))
    (hvz : vz = v0 ∨ vz = qExpFrobeniusPlaceModL κ Γ p v0)
    (g : ↥(qExpFunctionFieldC κ Γ)) (hg : qExpFrobeniusModL κ Γ p g = g ^ p) (c : κ)
    (h : g - algebraMap κ ↥(qExpFunctionFieldC κ Γ) c ∈ vz.toValuationSubring.nonunits) :
    ∃ c' : κ, (c' = 0 ↔ c = 0) ∧ g - algebraMap κ ↥(qExpFunctionFieldC κ Γ) c' ∈ v0.toValuationSubring.nonunits := by
  rcases hvz with rfl | rfl
  · exact ⟨c, Iff.rfl, h⟩
  · have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c (Fact.out : p.Prime).pos
    refine ⟨c', ⟨fun h0 => ?_, fun h0 => ?_⟩, ?_⟩
    · rw [← hc', h0, zero_pow hp0]
    · rw [h0] at hc'
      exact eq_zero_of_pow_eq_zero hc'
    · haveI : CharP ↥(qExpFunctionFieldC κ Γ) p :=
        charP_of_injective_algebraMap (algebraMap κ ↥(qExpFunctionFieldC κ Γ)).injective p
      have h' := (mem_nonunits_restrictAlong_iff (qExpFrobeniusModL κ Γ p) (qExpFrobeniusModL_isIntegral κ Γ p) v0 _).mp h
      rw [map_sub, AlgHom.commutes, hg, ← hc', map_pow, ← sub_pow_char] at h'
      exact (pow_mem_nonunits_iff _ _ hp0).mp h'

theorem fin_special (v0 vz : Place κ ↥(qExpFunctionFieldC κ Γ))
    (hvz : vz = v0 ∨ vz = qExpFrobeniusPlaceModL κ Γ p v0)
    {g : ↥(qExpFunctionFieldC κ Γ)} {c : κ}
    (h : g - algebraMap κ ↥(qExpFunctionFieldC κ Γ) c ∈ vz.toValuationSubring.nonunits)
    (hg : (g : LaurentSeries κ) = jqModC κ) :
    ∃ (x : ↥(qExpFunctionFieldC κ Γ)) (a : κ), (x : LaurentSeries κ) = jqModC κ ∧ v0.HasValue x a := by
  obtain ⟨c', -, hc'⟩ := frob_pull Γ p v0 vz hvz g (frob_eq_pow_of_coe_eq Γ p g 1 (by rw [zpow_one]; exact hg)) c h
  exact ⟨g, c', hg, hasValue_of_sub_mem_nonunits v0 hc'⟩

theorem inf_special (v0 vz : Place κ ↥(qExpFunctionFieldC κ Γ))
    (hvz : vz = v0 ∨ vz = qExpFrobeniusPlaceModL κ Γ p v0)
    {g : ↥(qExpFunctionFieldC κ Γ)} {c : κ}
    (h : g - algebraMap κ ↥(qExpFunctionFieldC κ Γ) c ∈ vz.toValuationSubring.nonunits)
    (hg : (g : LaurentSeries κ) = (jqModC κ)⁻¹) :
    (c ≠ 0 → ∃ (x : ↥(qExpFunctionFieldC κ Γ)) (a : κ), (x : LaurentSeries κ) = jqModC κ ∧ v0.HasValue x a) ∧
    (c = 0 → ∀ x : ↥(qExpFunctionFieldC κ Γ), (x : LaurentSeries κ) = jqModC κ → x ∉ v0.toValuationSubring) := by
  obtain ⟨c', hc0, hc'⟩ :=
    frob_pull Γ p v0 vz hvz g (frob_eq_pow_of_coe_eq Γ p g (-1) (by rw [zpow_neg_one]; exact hg)) c h
  have hginv : ((g⁻¹ : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = jqModC κ := coe_inv_eq_of_coe_eq_inv _ g hg
  refine ⟨fun hc => ?_, fun hc x hx => ?_⟩
  · have hc'0 : c' ≠ 0 := fun h0 => hc (hc0.mp h0)
    exact ⟨g⁻¹, c'⁻¹, hginv, (hasValue_of_sub_mem_nonunits v0 hc').inv hc'0⟩
  · have hc'0 : c' = 0 := hc0.mpr hc
    rw [hc'0, map_zero, sub_zero] at hc'
    have hx' : x = g⁻¹ := Subtype.ext (by rw [hx, hginv])
    rw [hx']
    exact not_mem_of_inv_mem_nonunits v0 (ne_zero_of_coe_eq_jqModC _ _ hginv) (by rwa [inv_inv])

end Fibre

section Generic

variable {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) (A : ValuationSubring K) (W : Place K ↥F)

theorem fin_generic {g : ↥F} {c : ↥A} (h : g - algebraMap K F (c : K) ∈ W.toValuationSubring.nonunits)
    (hg : (g : LaurentSeries K) = jqModC K) :
    ¬ (∀ x : ↥F, (x : LaurentSeries K) = jqModC K → ∀ a : ↥A, W.ord (x - algebraMap K F (a : K)) ≤ 0) := by
  intro hc
  exact absurd (hc g hg c)
    (not_le.mpr (ord_sub_pos_of_hasValue W (hasValue_of_sub_mem_nonunits W h) (ne_algebraMap_of_coe_eq_jqModC F g hg _)))

theorem inf_generic_unit {g : ↥F} {c : ↥A} (h : g - algebraMap K F (c : K) ∈ W.toValuationSubring.nonunits)
    (hg : (g : LaurentSeries K) = (jqModC K)⁻¹) (hcu : IsUnit c) :
    ¬ (∀ x : ↥F, (x : LaurentSeries K) = jqModC K → ∀ a : ↥A, W.ord (x - algebraMap K F (a : K)) ≤ 0) := by
  intro hcusp
  have hc0 : (c : K) ≠ 0 := by
    intro h0
    apply hcu.ne_zero
    exact Subtype.ext h0
  have hv : W.HasValue g⁻¹ (c : K)⁻¹ := (hasValue_of_sub_mem_nonunits W h).inv hc0
  have hginv : ((g⁻¹ : ↥F) : LaurentSeries K) = jqModC K := coe_inv_eq_of_coe_eq_inv F g hg
  have hcinv : (((hcu.unit⁻¹ : (↥A)ˣ) : ↥A) : K) = (c : K)⁻¹ := by
    have h1 : ((hcu.unit⁻¹ : (↥A)ˣ) : ↥A) * c = 1 := by
      have h0 := hcu.unit.inv_mul
      rw [IsUnit.unit_spec] at h0
      exact h0
    have h2 : (((hcu.unit⁻¹ : (↥A)ˣ) : ↥A) : K) * (c : K) = 1 := by
      have h3 := congrArg Subtype.val h1
      push_cast at h3
      exact h3
    exact eq_inv_of_mul_eq_one_left h2
  have h3 := hcusp g⁻¹ hginv ((hcu.unit⁻¹ : (↥A)ˣ) : ↥A)
  rw [hcinv] at h3
  exact absurd h3 (not_le.mpr (ord_sub_pos_of_hasValue W hv (ne_algebraMap_of_coe_eq_jqModC F _ hginv _)))

theorem inf_generic_nonunit {g : ↥F} {c : ↥A} (h : g - algebraMap K F (c : K) ∈ W.toValuationSubring.nonunits)
    (hg : (g : LaurentSeries K) = (jqModC K)⁻¹) (hcu : ¬ IsUnit c) :
    ∀ x : ↥F, (x : LaurentSeries K) = jqModC K → ∀ a : ↥A, W.ord (x - algebraMap K F (a : K)) ≤ 0 := by
  intro x hx a
  have hginv : ((g⁻¹ : ↥F) : LaurentSeries K) = jqModC K := coe_inv_eq_of_coe_eq_inv F g hg
  have hxg : x = g⁻¹ := Subtype.ext (by rw [hx, hginv])
  by_contra hlt
  rw [not_le] at hlt
  have hva : W.HasValue x (a : K) := hasValue_of_ord_sub_pos W x a hlt
  by_cases hc0 : (c : K) = 0
  · rw [hc0, map_zero, sub_zero] at h
    have hx0 : x ≠ 0 := ne_zero_of_coe_eq_jqModC F x hx
    exact not_mem_of_inv_mem_nonunits W hx0 (by rwa [hxg, inv_inv]) hva.mem
  · have hv : W.HasValue x (c : K)⁻¹ := by
      rw [hxg]
      exact (hasValue_of_sub_mem_nonunits W h).inv hc0
    have haeq : (a : K) = (c : K)⁻¹ := hva.unique hv
    apply hcu
    have hca : c * a = 1 := Subtype.ext (by push_cast; rw [haeq, mul_inv_cancel₀ hc0])
    exact IsUnit.of_mul_eq_one a hca

end Generic

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

theorem section_ext {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] (a b : Spec (CommRingCat.of K) ⟶ X) (ha : a ≫ f = 𝟙 _) (hb : b ≫ f = 𝟙 _)
    (h : a.base (IsLocalRing.closedPoint K) = b.base (IsLocalRing.closedPoint K)) : a = b := by
  have := (pointEquivClosedPoint f).injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext h)
  exact congrArg Subtype.val this

noncomputable abbrev jInv (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ↥(chartAlgInf p Γ hj) :=
  TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)

theorem coe_coe_jInv (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    (((jInv p Γ hj : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = (jqModC ℚ)⁻¹ := by
  simp [jInv, TwoChartIntegralModel.coe_jInvChartInf]

theorem coe_coe_jChartFin (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    (((jChartFin p Γ hj : ↥(chartAlgFin p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = jqModC ℚ := rfl

end CuspPoleRedH

open CuspPoleRedH

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open GoodReductionJacobian NeronModelInfra ModularCurve.JZeroNeronObjectAtP in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (i : Fin 2)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y) ↔ ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0) := by
  classical
  haveI := 𝔛.lfp
  haveI := 𝔛.efib_iso A hA ρ hρ
  haveI := 𝔛.Mfib_chart_nonempty A hA ρ hρ
  haveI := 𝔛.Meta_chart_nonempty
  have hp' : ¬ p ∣ M / p := not_dvd_div hpM hpM2
  have hΓ₁ : CongruenceSubgroup.Gamma1 (M / p) ≤ ΓN p M H hpM := gamma1_le_gammaH (M / p) (infSubgroup p M H hpM)
  have hΓ₀ : ΓN p M H hpM ≤ CongruenceSubgroup.Gamma0 (M / p) := CohCarrier.GammaH_le_Gamma0 _

  obtain ⟨ρ', hρ', Ms, es, hes, hes', πFin, πInf, hall⟩ :=
    ModularCurve.exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
      (M / p) (ΓN p M H hpM) hΓ₁ hΓ₀ p hp' (jAt (ΓN p M H hpM) hj) (coe_jAt _ _)
  obtain ⟨-, hliftI, -⟩ := hall A hA

  obtain ⟨Q, hQ, hQplace⟩ : ∃ Q : closedPoints (𝔛.Mfib A hA ρ hρ).C,
      Q.1 = (inv (𝔛.efib A hA ρ hρ)).base
        ((uκ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A))) ∧
      ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q = (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 ∨
        (𝔛.Mfib A hA ρ hρ).placeOfPoint Q =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) := by
    have huπ : (uκ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) =
        (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base P0.1 := by
      show (XHDRLevel.fibreMap 𝔛.π _).base (uκ.base _) =
        (XHDRLevel.fibreMap 𝔛.π _).base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1)
      rw [hP0]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · refine ⟨P0, ?_, Or.inl rfl⟩
      rw [huπ, 𝔛.comp_pi, Category.comp_id]
      show P0.1 = (𝔛.efib A hA ρ hρ ≫ inv (𝔛.efib A hA ρ hρ)).base P0.1
      rw [IsIso.hom_inv_id]
      rfl
    · obtain ⟨h, hplace⟩ := 𝔛.comp1_pi_place A hA ρ hρ P0
      exact ⟨⟨_, h⟩, by rw [huπ], Or.inr hplace⟩

  obtain ⟨z, hzP⟩ : ∃ z, pointEquivClosedPoint (𝔛.Mfib A hA ρ hρ).toBase z = Q :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  have hzQ : (𝔛.Mfib A hA ρ hρ).pointEquivPlace z = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q := by
    rw [CurveModel.pointEquivPlace_apply, hzP]
  have hvz : (𝔛.Mfib A hA ρ hρ).pointEquivPlace z = (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 ∨
      (𝔛.Mfib A hA ρ hρ).pointEquivPlace z =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0) := by
    rw [hzQ]
    exact hQplace
  have hzbase : z.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) = Q.1 := congrArg Subtype.val hzP
  have hze : z.1 ≫ 𝔛.efib A hA ρ hρ = uκ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) := by
    have key : z.1 = (uκ ≫ XHDRLevel.fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)) ≫ inv (𝔛.efib A hA ρ hρ) := by
      refine section_ext (𝔛.Mfib A hA ρ hρ).toBase _ _ z.2 ?_ ?_
      · rw [← 𝔛.hefib A hA ρ hρ, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc]
        unfold XHDRLevel.fibreMap
        rw [pullback.lift_snd, ← Category.assoc, huκ₂, Category.id_comp]
      · rw [hzbase, hQ]
        rfl
    rw [key, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hzfst : z.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 ≫ 𝔛.π.1 := by
    rw [← Category.assoc, hze, Category.assoc]
    unfold XHDRLevel.fibreMap
    rw [pullback.lift_fst, ← Category.assoc, huκ₁, Category.assoc]

  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
      (u.1.base (IsLocalRing.closedPoint ↥A)) with hF | hI
  ·
    obtain ⟨βu, hβu⟩ := exists_eq_specMap_comp (ιFin p (ΓM M H) hj) u.1 hF

    have hyβ : y.1 ≫ (𝔛.eeta ≫ pullback.fst _ _) =
        Spec.map (CommRingCat.ofHom (A.subtype.comp βu)) ≫ ιFin p (ΓM M H) hj := by
      rw [← hu, hβu, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hgen := 𝔛.Meta.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
      (𝔛.eeta ≫ pullback.fst _ _) (ιFin p (ΓM M H) hj) y (A.subtype.comp βu) hyβ (jChartFin p (ΓM M H) hj)
    have hgen' : _ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((βu (jChartFin p (ΓM M H) hj) : ↥A) : AlgebraicClosure ℚ) ∈
        (𝔛.Meta.pointEquivPlace y).toValuationSubring.nonunits := hgen
    have hreadM : _ = jqModC (AlgebraicClosure ℚ) :=
      (𝔛.Meta_pin (jChartFin p (ΓM M H) hj)).trans (by rw [coe_coe_jChartFin, coeffEmb_jqModC])
    have hnc := fin_generic (xHFunctionFieldBar M H) A (𝔛.Meta.pointEquivPlace y) hgen' hreadM

    have hz' : z.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥A).comp βu).comp (RingHomClass.toRingHom 𝔛.iota0))) ≫
          ιFin p (ΓN p M H hpM) hj := by
      rw [hzfst, hβu, Category.assoc, 𝔛.pi_chart, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp,
        Spec.map_comp, Category.assoc, Category.assoc]
      rfl
    have hsp := (𝔛.Mfib A hA ρ hρ).ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
      (𝔛.efib A hA ρ hρ ≫ pullback.fst _ _) (ιFin p (ΓN p M H hpM) hj) z _ (by simpa only [Category.assoc] using hz')
      (jChartFin p (ΓN p M H hpM) hj)
    have hliftj : coeffMap A.subtype (jqModC ↥A) =
        coeffEmb (AlgebraicClosure ℚ) (((jChartFin p (ΓN p M H hpM) hj : ↥(chartAlgFin p (ΓN p M H hpM) hj)) :
          ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := by
      rw [coeffMap_jqModC, coe_coe_jChartFin, coeffEmb_jqModC]
    have hreadN : _ = jqModC (ResidueField ↥A) :=
      (𝔛.Mfib_pin A hA ρ hρ (jChartFin p (ΓN p M H hpM) hj) (jqModC ↥A) hliftj).trans (coeffMap_jqModC _)
    obtain ⟨xb, a, hxb, hva⟩ := fin_special (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)
      ((𝔛.Mfib A hA ρ hρ).pointEquivPlace z) hvz hsp hreadN
    have haff : JHPlaceSpecialization.IsAffinePlace p M H hpM A ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0) := ⟨xb, a, hxb, hva⟩
    exact iff_of_false hnc (not_not.mpr haff)
  ·
    obtain ⟨βu, hβu⟩ := exists_eq_specMap_comp (ιInf p (ΓM M H) hj) u.1 hI

    have hyβ : y.1 ≫ (𝔛.eeta ≫ pullback.fst _ _) =
        Spec.map (CommRingCat.ofHom (A.subtype.comp βu)) ≫ ιInf p (ΓM M H) hj := by
      rw [← hu, hβu, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))) :=
      ⟨⟨y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)), by
        show (y.1 ≫ (𝔛.eeta ≫ pullback.fst _ _)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈
          (ιInf p (ΓM M H) hj) ''ᵁ ⊤
        rw [hyβ, Scheme.Hom.image_top_eq_opensRange]
        exact ⟨_, rfl⟩⟩⟩
    have hgen := 𝔛.Meta.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
      (𝔛.eeta ≫ pullback.fst _ _) (ιInf p (ΓM M H) hj) y (A.subtype.comp βu) hyβ (jInv p (ΓM M H) hj)
    have hgen' : _ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((βu (jInv p (ΓM M H) hj) : ↥A) : AlgebraicClosure ℚ) ∈
        (𝔛.Meta.pointEquivPlace y).toValuationSubring.nonunits := hgen
    have hreadM : _ = (jqModC (AlgebraicClosure ℚ))⁻¹ :=
      (𝔛.coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb p M H hpM hj (jInv p (ΓM M H) hj)).trans
        (by rw [coe_coe_jInv, map_inv₀, coeffEmb_jqModC])

    have hz' : z.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥A).comp βu).comp (RingHomClass.toRingHom 𝔛.iotaInf))) ≫
          ιInf p (ΓN p M H hpM) hj := by
      rw [hzfst, hβu, Category.assoc, 𝔛.pi_chartInf, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp,
        Spec.map_comp, Category.assoc, Category.assoc]
      rfl
    haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))) :=
      ⟨⟨z.1.base (IsLocalRing.closedPoint (ResidueField ↥A)), by
        show (z.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈
          (ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤
        rw [hz', Scheme.Hom.image_top_eq_opensRange]
        exact ⟨_, rfl⟩⟩⟩
    have hsp := (𝔛.Mfib A hA ρ hρ).ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
      (𝔛.efib A hA ρ hρ ≫ pullback.fst _ _) (ιInf p (ΓN p M H hpM) hj) z _ (by simpa only [Category.assoc] using hz')
      (jInv p (ΓN p M H hpM) hj)

    have hiota : 𝔛.iotaInf (jInv p (ΓN p M H hpM) hj) = jInv p (ΓM M H) hj := by
      apply Subtype.ext
      apply Subtype.ext
      rw [𝔛.iotaInf_spec, coe_coe_jInv, coe_coe_jInv]
    have hcoord : (((IsLocalRing.residue ↥A).comp βu).comp (RingHomClass.toRingHom 𝔛.iotaInf)) (jInv p (ΓN p M H hpM) hj) =
        IsLocalRing.residue ↥A (βu (jInv p (ΓM M H) hj)) := by
      rw [← hiota]
      rfl
    rw [hcoord] at hsp

    obtain ⟨yI, hyI, -⟩ := hliftI (jInv p (ΓN p M H hpM) hj)
    have hrI := 𝔛.coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffMap_residue p M H hpM hpM2 hj A hA ρ hρ
      (jInv p (ΓN p M H hpM) hj) yI hyI
    have hyI1 : yI * jqModC ↥A = 1 := by
      apply coeffMap_injective A.subtype Subtype.val_injective
      rw [map_mul, map_one, hyI, coeffMap_jqModC, coe_coe_jInv, map_inv₀, coeffEmb_jqModC]
      exact inv_mul_cancel₀ (jqModC_ne_zero' _)
    have hreadN : _ = (jqModC (ResidueField ↥A))⁻¹ := hrI.trans (by
      have h1 := congrArg (coeffMap (IsLocalRing.residue ↥A)) hyI1
      rw [map_mul, map_one, coeffMap_jqModC] at h1
      exact eq_inv_of_mul_eq_one_left h1)
    have hspec := inf_special (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)
      ((𝔛.Mfib A hA ρ hρ).pointEquivPlace z) hvz hsp hreadN

    by_cases hcu : IsUnit (βu (jInv p (ΓM M H) hj))
    · have hnc := inf_generic_unit (xHFunctionFieldBar M H) A (𝔛.Meta.pointEquivPlace y) hgen' hreadM hcu
      have hres : IsLocalRing.residue ↥A (βu (jInv p (ΓM M H) hj)) ≠ 0 :=
        (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hcu
      obtain ⟨xb, a, hxb, hva⟩ := hspec.1 hres
      have haff : JHPlaceSpecialization.IsAffinePlace p M H hpM A ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0) := ⟨xb, a, hxb, hva⟩
      exact iff_of_false hnc (not_not.mpr haff)
    · have hc := inf_generic_nonunit (xHFunctionFieldBar M H) A (𝔛.Meta.pointEquivPlace y) hgen' hreadM hcu
      have hres : IsLocalRing.residue ↥A (βu (jInv p (ΓM M H) hj)) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hcu)
      have hpole := hspec.2 hres
      have hna : ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0) := by
        rintro ⟨xb, a, hxb, hva⟩
        exact hpole xb hxb hva.mem
      exact iff_of_true hc hna

end S_ModularCurve_XHDRModelAtP_isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp (solution)
