-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_section_slopeLaw_isUnit_ord_eq_zero_at_crossing_of_dvd_width
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a688f159-b550-5067-abe5-caa32d6f9aa3

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
import Theorems.Thm_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_comp_eq_and_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective
import Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_orientedEtaleCrossingChart
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_through_crossing_iff_reduceFst_eq_and_not_isStrict_of_offDiag_of_surjective
import Theorems.Thm_ModularCurve_XHDRModelAtP_readA_mem_integers_and_residue_eq_restrict_comp_of_mem
import Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOn_germ_chart_eq_one_of_chart_of_residue_surjective
import Theorems.Thm_AlgebraicCurve_Annulus_eq_of_mul_eq_algebraMap_pow_of_isUnit_evalAt_mul_evalAt_param_zpow_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_section_slopeLaw_isUnit_ord_eq_zero_at_crossing_of_dvd_width
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CartierGeneric

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem appIso_inv_appTop {X : Scheme.{u}} (U : X.Opens) (z : Γ(X, ⊤)) :
    (U.ι.appIso ⊤).inv.hom (U.ι.appTop.hom z) = (X.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op).hom z := by
  have h := Scheme.Hom.appLE_appIso_inv U.ι (U := ⊤) (V := ⊤) le_top
  have h' : U.ι.appLE ⊤ ⊤ le_top = U.ι.appTop := Scheme.Hom.appLE_eq_app _
  rw [h'] at h
  have := congrArg (fun φ => φ.hom z) h
  simpa using this

theorem isUnit_map_of_isUnit {R S : Type*} [Monoid R] [Monoid S] {F : Type*} [FunLike F R S] [MonoidHomClass F R S]
    (φ : F) {x : R} (hx : IsUnit x) : IsUnit (φ x) := hx.map φ

end CartierGeneric

namespace Cartier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

section Frame

variable {p M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

noncomputable def q {O : Type} [CommRing O] (ρO : R p →+* O) {A : ValuationSubring (AlgebraicClosure ℚ)} (ρ : R p →+* ↥A)
    (ιA : O →+* ↥A) (hιAρ : ιA.comp ρO = ρ) : XO (ΓM M H) hj ρ ⟶ XO (ΓM M H) hj ρO :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ιA)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιAρ])

variable {O : Type} [CommRing O] (ρO : R p →+* O) {A : ValuationSubring (AlgebraicClosure ℚ)} (ρ : R p →+* ↥A)
    (ιA : O →+* ↥A) (hιAρ : ιA.comp ρO = ρ)

@[reassoc (attr := simp)]
theorem q_fst : q (hj := hj) (M := M) (H := H) ρO ρ ιA hιAρ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [q, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem q_snd : q (hj := hj) (M := M) (H := H) ρO ρ ιA hιAρ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ιA) := by
  rw [q, pullback.lift_snd]

theorem bc_q {κ : Type} [CommRing κ] {toκ' : R p →+* κ} (r : ↥A →+* κ) (toκ : O →+* κ) (hιAκ : r.comp ιA = toκ)
    (htoκ : toκ.comp ρO = toκ')
    (bc : fibre (Γ := ΓM M H) (hj := hj) toκ' ⟶ XO (ΓM M H) hj ρ)
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom r)) :
    bc ≫ q ρO ρ ιA hιAρ = bcMap (ΓM M H) hj ρO toκ htoκ := by
  apply pullback.hom_ext
  · rw [Category.assoc, q_fst, hbc₁, bcMap_fst]
  · rw [Category.assoc, q_snd, reassoc_of% hbc₂, bcMap_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιAκ]

theorem gA_q [Fact p.Prime] (𝔛 : XHDRModelAtP p M H hpM hj)
    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (hιA : A.subtype.comp ιA = jO)
    (gA : 𝔛.Meta.C ⟶ XO (ΓM M H) hj ρ)
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A) :
    gA ≫ q ρO ρ ιA hιAρ = 𝔛.eeta ≫
      (pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
        (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])) := by
  apply pullback.hom_ext
  · rw [Category.assoc, q_fst, hgA₁, Category.assoc, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, q_snd, reassoc_of% hgA₂, Category.assoc, pullback.lift_snd, reassoc_of% 𝔛.heeta, barPt,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιA]

theorem gA_q_snd [Fact p.Prime] (𝔛 : XHDRModelAtP p M H hpM hj)
    (jO : O →+* AlgebraicClosure ℚ) (hιA : A.subtype.comp ιA = jO)
    (gA : 𝔛.Meta.C ⟶ XO (ΓM M H) hj ρ)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A) :
    gA ≫ q ρO ρ ιA hιAρ ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ Spec.map (CommRingCat.ofHom jO) := by
  rw [q_snd, reassoc_of% hgA₂, barPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιA]

end Frame

section Chart

variable {O : Type} [CommRing O]

theorem chartSection_algebraMap {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of O)) (U : X.Opens)
    {Q : Type} [CommRing Q] [Algebra O Q] (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of Q))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O Q)) = U.ι ≫ π) (o : O) :
    (U.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom (algebraMap O Q o))) =
      (π.appLE ⊤ (U.ι ''ᵁ ⊤) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
  have hnat := congrArg (fun φ => φ.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O Q)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  rw [hnat, ← CommRingCat.comp_apply _ f.appTop, ← Scheme.Hom.comp_appTop, hover, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, CartierGeneric.appIso_inv_appTop, Scheme.Hom.appLE, CommRingCat.comp_apply]
  rfl

theorem chart_gv_mul_gu {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of O)) (U : X.Opens) (t : O)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme t)
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O t))) = U.ι ≫ π) :
    (U.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O t))).inv.hom (CrossingQuotient.V t))) *
      (U.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O t))).inv.hom (CrossingQuotient.U t))) =
      (π.appLE ⊤ (U.ι ''ᵁ ⊤) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom t) := by
  rw [← map_mul, ← map_mul, ← map_mul, mul_comm (CrossingQuotient.V _) (CrossingQuotient.U _), CrossingQuotient.U_mul_V]
  exact chartSection_algebraMap π U f hover t

theorem isUnit_app_const {X Y : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of O)) (U : X.Opens)
    {K : Type} [CommRing K] (τ : Y ⟶ Spec (CommRingCat.of K)) (g : O →+* K) (h : Y ⟶ X)
    (hsq : h ≫ π = τ ≫ Spec.map (CommRingCat.ofHom g)) (o : O) (ho : IsUnit (g o)) :
    IsUnit ((h.app (U.ι ''ᵁ ⊤)).hom ((π.appLE ⊤ (U.ι ''ᵁ ⊤) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hsq, Scheme.Hom.comp_appLE,
    CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
  have hnat := congrArg (fun φ => φ.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  rw [show (Spec.map (CommRingCat.ofHom g)).appLE ⊤ _ le_rfl = (Spec.map (CommRingCat.ofHom g)).appTop from
    Scheme.Hom.appLE_eq_app _]
  change IsUnit ((τ.appLE _ _ _).hom ((Spec.map (CommRingCat.ofHom g)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)))
  rw [← hnat]
  exact ((ho.map _).map _)

end Chart

end Cartier

namespace Cartier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

section Horizontal

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem ord_placeOfPoint_read_pow_eq_zero (𝔛 : XHDRModelAtP p M H hpM hj)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (ρ : R p →+* ↥A)
    {O : Type} [CommRing O] (ρO : R p →+* O) (ιA : O →+* ↥A) (hιAρ : ιA.comp ρO = ρ)
    (jO : O →+* AlgebraicClosure ℚ) (hιA : A.subtype.comp ιA = jO)
    (gA : 𝔛.Meta.C ⟶ XO (ΓM M H) hj ρ)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (U₀ : (XO (ΓM M H) hj ρO).Opens) (o : O) (ho : jO o ≠ 0)
    (gv gu : Γ(XO (ΓM M H) hj ρO, U₀.ι ''ᵁ ⊤))
    (hprod : gv * gu = ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).appLE ⊤ (U₀.ι ''ᵁ ⊤) le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))
    (m : ℕ) (x : closedPoints 𝔛.Meta.C)
    (hx : gA.base x.1 ∈ q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ (q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))))] :
    (𝔛.Meta.placeOfPoint x).ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))
      ((gA.app (q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gv ^ m)))) = 0 := by
  apply AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit 𝔛.Meta _ x hx
  rw [map_pow]
  refine IsUnit.pow m ?_

  have hcomp : (gA.app (q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gv) =
      ((gA ≫ q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gv := rfl
  rw [hcomp]
  have hunit : IsUnit (((gA ≫ q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom (gv * gu)) := by
    rw [hprod]
    exact isUnit_app_const (pullback.snd _ _) U₀ 𝔛.Meta.toBase jO (gA ≫ q ρO ρ ιA hιAρ)
      (by rw [Category.assoc, gA_q_snd ρO ρ ιA hιAρ 𝔛 jO hιA gA hgA₂]) o (isUnit_iff_ne_zero.mpr ho)
  rw [map_mul] at hunit
  exact isUnit_of_mul_isUnit_left hunit

end Horizontal

end Cartier

namespace CartierGeneric

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem isUnit_germ_appTop_ΓSpecIso_inv {Q : Type u} [CommRing Q] {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of Q))
    (y : S) (r : Q) (hr : r ∉ (f.base y).asIdeal) :
    IsUnit ((S.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom r))) := by
  have h1 : (S.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom r)) =
      (f.stalkMap y).hom (((Spec (CommRingCat.of Q)).presheaf.germ ⊤ (f.base y) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom r)) := by
    rw [← CommRingCat.comp_apply _ (f.stalkMap y), Scheme.Hom.germ_stalkMap]
    rfl
  rw [h1]
  refine IsUnit.map _ ?_
  have h2 : ((Spec (CommRingCat.of Q)).presheaf.germ ⊤ (f.base y) trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom r) =
      algebraMap Q ((Spec.structureSheaf Q).presheaf.stalk (f.base y)) r := rfl
  rw [h2]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff ((Spec.structureSheaf Q).presheaf.stalk (f.base y)) (f.base y).asIdeal r).mpr hr

theorem isUnit_germ_appIso_inv {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U.ι ''ᵁ ⊤) (z : Γ(U, ⊤))
    (hz : ∀ y : U, U.ι.base y = x → IsUnit (((U : Scheme.{u}).presheaf.germ ⊤ y trivial).hom z)) :
    IsUnit ((X.presheaf.germ (U.ι ''ᵁ ⊤) x hx).hom ((U.ι.appIso ⊤).inv.hom z)) := by
  obtain ⟨y, -, rfl⟩ := hx
  have hy := hz y rfl
  have key : (U.ι.stalkMap y).hom ((X.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι.base y) ⟨y, trivial, rfl⟩).hom ((U.ι.appIso ⊤).inv.hom z)) =
      ((U : Scheme.{u}).presheaf.germ ⊤ y trivial).hom z := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    rw [← CommRingCat.comp_apply (U.ι.appIso ⊤).inv, Scheme.Hom.appIso_inv_app]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [← key] at hy
  exact (isUnit_map_iff (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv _).mp hy

end CartierGeneric

namespace Cartier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

section VerticalOne

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem isUnit_germ_pullback_gv_pow_of_comp_one (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    {O : Type} [CommRing O] (ρO : R p →+* O) (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (ιA : O →+* ↥A) (hιAρ : ιA.comp ρO = ρ) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ XO (ΓM M H) hj ρ)
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (hinj : Function.Injective (bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (U₀ : (XO (ΓM M H) hj ρO).Opens)
    (f : (U₀ : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hfib : ∀ y : ↥(U₀ : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
        U₀.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hor₄ : ∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base →
      CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (m : ℕ) (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))
    (hne : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ≠
      bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)) :
    IsUnit (((XO (ΓM M H) hj ρ).presheaf.germ (q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) _ hQ).hom
      (((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom
        ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom
          (CrossingQuotient.V (((p : ℕ) : O) ^ e))))) ^ m)) := by
  rw [map_pow]
  refine IsUnit.pow m ?_

  rw [← Scheme.Hom.germ_stalkMap_apply (q ρO ρ ιA hιAρ) (U₀.ι ''ᵁ ⊤) _ hQ]
  refine IsUnit.map _ ?_
  have hbcq := bc_q ρO ρ ιA hιAρ (IsLocalRing.residue ↥A) toκ hιAκ htoκ bc hbc₁ hbc₂

  refine CartierGeneric.isUnit_germ_appIso_inv U₀ _ hQ _ (fun y hy => ?_)
  refine CartierGeneric.isUnit_germ_appTop_ΓSpecIso_inv f y _ (fun hV => ?_)

  have hyrange : U₀.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base := by
    refine ⟨(𝔛.efib A hA ρ hρ).base Q.1, ?_⟩
    rw [hy, ← hbcq]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
  have hU := hor₄ y hyrange
  have hyn := (hfib y).mp ⟨hU, hV⟩
  apply hne

  have h1 : (q ρO ρ ιA hιAρ).base (bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1)) =
      (q ρO ρ ιA hιAρ).base (bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)) := by
    rw [← hy, hyn, ← Scheme.Hom.comp_apply bc, hbcq]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
  have h2 : (bcMap (ΓM M H) hj ρO toκ htoκ).base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) =
      (bcMap (ΓM M H) hj ρO toκ htoκ).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) := by
    simpa only [← hbcq, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using h1
  rw [hinj h2]

end VerticalOne

end Cartier

namespace Cartier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

section VerticalZero

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem exists_opens_eq_pow_mul_isUnit_of_comp_zero (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    {O : Type} [CommRing O] (ρO : R p →+* O) (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (ιA : O →+* ↥A) (hιAρ : ιA.comp ρO = ρ) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ XO (ΓM M H) hj ρ)
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (hinj : Function.Injective (bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (U₀ : (XO (ΓM M H) hj ρO).Opens)
    (f : (U₀ : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U₀.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U₀ : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
        U₀.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hor₃ : ∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base →
      CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (m k : ℕ) (hk : e * m = k) (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))
    (hne : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ≠
      bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)) :
    letI Qr := CrossingQuotient O (((p : ℕ) : O) ^ e)
    letI φ : Qr →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Qr)).inv.hom
    letI gv : Γ(XO (ΓM M H) hj ρO, U₀.ι ''ᵁ ⊤) := (U₀.ι.appIso ⊤).inv.hom (f.appTop.hom (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
    letI gu : Γ(XO (ΓM M H) hj ρO, U₀.ι ''ᵁ ⊤) := (U₀.ι.appIso ⊤).inv.hom (f.appTop.hom (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
    letI UA : (XO (ΓM M H) hj ρ).Opens := q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)
    letI t : Γ(XO (ΓM M H) hj ρ, UA) := ((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gv ^ m
    ∃ (W : (XO (ΓM M H) hj ρ).Opens) (hWU : W ≤ UA)
      (hQW : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ W) (t₀ : Γ(XO (ΓM M H) hj ρ, W)),
      ((XO (ΓM M H) hj ρ).presheaf.map (homOfLE hWU).op).hom t = ((p : ℕ) : Γ(XO (ΓM M H) hj ρ, W)) ^ k * t₀ ∧
      IsUnit (((XO (ΓM M H) hj ρ).presheaf.germ W _ hQW).hom t₀) := by
  have hbcq := bc_q ρO ρ ιA hιAρ (IsLocalRing.residue ↥A) toκ hιAκ htoκ bc hbc₁ hbc₂

  have hunit : IsUnit (((XO (ΓM M H) hj ρ).presheaf.germ ((q ρO ρ ιA hιAρ) ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) _ hQ).hom (((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom (CrossingQuotient.U (((p : ℕ) : O) ^ e))))))) := by
    rw [← Scheme.Hom.germ_stalkMap_apply (q ρO ρ ιA hιAρ) (U₀.ι ''ᵁ ⊤) _ hQ]
    refine IsUnit.map _ ?_
    refine CartierGeneric.isUnit_germ_appIso_inv U₀ _ hQ _ (fun y hy => ?_)
    refine CartierGeneric.isUnit_germ_appTop_ΓSpecIso_inv f y _ (fun hU => ?_)
    have hyrange : U₀.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base := by
      refine ⟨(𝔛.efib A hA ρ hρ).base Q.1, ?_⟩
      rw [hy, ← hbcq]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have hV := hor₃ y hyrange
    have hyn := (hfib y).mp ⟨hU, hV⟩
    apply hne
    have h1 : (q ρO ρ ιA hιAρ).base (bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1)) =
        (q ρO ρ ιA hιAρ).base (bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)) := by
      rw [← hy, hyn, ← Scheme.Hom.comp_apply bc, hbcq]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have h2 : (bcMap (ΓM M H) hj ρO toκ htoκ).base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) =
        (bcMap (ΓM M H) hj ρO toκ htoκ).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) := by
      simpa only [← hbcq, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using h1
    rw [hinj h2]

  have hres : IsUnit (((XO (ΓM M H) hj ρ).presheaf.map (homOfLE ((XO (ΓM M H) hj ρ).basicOpen_le (((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom (CrossingQuotient.U (((p : ℕ) : O) ^ e)))))))).op).hom (((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom (CrossingQuotient.U (((p : ℕ) : O) ^ e))))))) :=
    AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen (X := (XO (ΓM M H) hj ρ).toLocallyRingedSpace.toRingedSpace) _
  obtain ⟨w, hw⟩ := hres

  have hprod0 : ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom (CrossingQuotient.V (((p : ℕ) : O) ^ e))))) * ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom (CrossingQuotient.U (((p : ℕ) : O) ^ e))))) = ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).appLE ⊤ (U₀.ι ''ᵁ ⊤) le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (((p : ℕ) : O) ^ e)) := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_comm (CrossingQuotient.V _) (CrossingQuotient.U _), CrossingQuotient.U_mul_V]
    exact chartSection_algebraMap (pullback.snd _ _) U₀ f hover _
  have hprodW := congrArg (fun s => ((XO (ΓM M H) hj ρ).presheaf.map (homOfLE ((XO (ΓM M H) hj ρ).basicOpen_le (((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom (CrossingQuotient.U (((p : ℕ) : O) ^ e)))))))).op).hom (((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom s)) hprod0
  simp only [map_mul, map_pow, map_natCast] at hprodW
  rw [← hw] at hprodW
  have hsv := (Units.eq_mul_inv_iff_mul_eq (c := w)).mpr hprodW

  refine ⟨(XO (ΓM M H) hj ρ).basicOpen (((q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (((p : ℕ) : O) ^ e)))).inv.hom (CrossingQuotient.U (((p : ℕ) : O) ^ e)))))), (XO (ΓM M H) hj ρ).basicOpen_le _, ((XO (ΓM M H) hj ρ).mem_basicOpen _ _ hQ).mpr hunit, (w⁻¹).val ^ m, ?_, ?_⟩
  · have h := congrArg (fun s => s ^ m) hsv
    simp only [mul_pow, ← pow_mul, hk] at h
    refine Eq.trans ?_ h
    exact map_pow _ _ m
  · exact ((w⁻¹).isUnit.pow m).map _

end VerticalZero

end Cartier

namespace Cartier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

section Inj
variable {p M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem bcMap_base_injective {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (h : toκ.comp ρO = toκ') (hsurj : Function.Surjective toκ) :
    Function.Injective (bcMap (ΓM M H) hj ρO toκ h).base := by
  have hsq : IsPullback (bcMap (ΓM M H) hj ρO toκ h)
      (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ')))
      (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)))
      (Spec.map (CommRingCat.ofHom toκ)) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)))
      (v₁₃ := toBase p (ΓM M H) hj) (h₂₂ := Spec.map (CommRingCat.ofHom ρO)) ?_ (bcMap_snd _ _ _ _ _) (IsPullback.of_hasPullback _ _)
    rw [bcMap_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    exact IsPullback.of_hasPullback _ _
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom toκ)) := IsClosedImmersion.spec_of_surjective _ hsurj
  haveI : IsClosedImmersion (bcMap (ΓM M H) hj ρO toκ h) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  exact (Scheme.Hom.isClosedEmbedding (bcMap (ΓM M H) hj ρO toκ h)).injective

end Inj

end Cartier

namespace CartierGeneric

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem germ_app_congr {X Y : Scheme.{u}} {h₁ h₂ : Y ⟶ X} (e : h₁ = h₂) (U : X.Opens) (y : Y)
    (m₁ : y ∈ h₁ ⁻¹ᵁ U) (m₂ : y ∈ h₂ ⁻¹ᵁ U) (s : Γ(X, U)) :
    (Y.presheaf.germ (h₁ ⁻¹ᵁ U) y m₁).hom ((h₁.app U).hom s) = (Y.presheaf.germ (h₂ ⁻¹ᵁ U) y m₂).hom ((h₂.app U).hom s) := by
  subst e; rfl

theorem germ_app_comp_congr {W X Y : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y) (e : a ≫ b = c) (U : Y.Opens) (w : W)
    (m₁ : w ∈ a ⁻¹ᵁ (b ⁻¹ᵁ U)) (m₂ : w ∈ c ⁻¹ᵁ U) (s : Γ(Y, U)) :
    (W.presheaf.germ (a ⁻¹ᵁ (b ⁻¹ᵁ U)) w m₁).hom ((a.app (b ⁻¹ᵁ U)).hom ((b.app U).hom s)) =
      (W.presheaf.germ (c ⁻¹ᵁ U) w m₂).hom ((c.app U).hom s) := by
  subst e; rfl

theorem germToFunctionField_app_of_eq_comp {W X Y : Scheme.{u}} [IsIntegral W] (g : W ⟶ Y) (a : W ⟶ X) (b : X ⟶ Y)
    (e : g = a ≫ b) (V : Y.Opens) [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V))] (hgen : genericPoint W ∈ a ⁻¹ᵁ (b ⁻¹ᵁ V)) (s : Γ(Y, V)) :
    W.germToFunctionField (g ⁻¹ᵁ V) ((g.app V).hom s) =
      (W.presheaf.germ (a ⁻¹ᵁ (b ⁻¹ᵁ V)) (genericPoint W) hgen).hom ((a.app (b ⁻¹ᵁ V)).hom ((b.app V).hom s)) := by
  subst e; rfl

private theorem _root_.CartierGeneric.ne_zero_of_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {r : F}
    (h : v.ord r = 1) : r ≠ 0 := by
  rintro rfl; rw [AlgebraicCurve.Place.ord_zero] at h; exact zero_ne_one h

p2m_export "CartierGeneric" "ne_zero_of_ord_eq_one"

theorem ord_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (f : F) (m : ℕ) :
    v.ord (f ^ m) = (m : ℤ) * v.ord f := by
  rw [← zpow_natCast]; exact AlgebraicCurve.Place.ord_zpow v f m

theorem existsIsUnit_congr {L : Type*} [Field L] {A : ValuationSubring L} {x y : L} (hxy : x = y)
    (h : ∃ h : x ∈ A, IsUnit (⟨x, h⟩ : ↥A)) : ∃ h : y ∈ A, IsUnit (⟨y, h⟩ : ↥A) := by
  subst hxy; exact h

end CartierGeneric

namespace CartierWidth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

theorem natCast_mem_maximalIdeal_of_liesOverPrime {L : Type*} [Field L] {A : ValuationSubring L} {q : ℕ}
    (hA : A.LiesOverPrime q) : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  exact hA

theorem natCast_prime_ne_zero (p : ℕ) [Fact p.Prime] : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

theorem coe_natCast_ne_zero (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime] :
    ((((p : ℕ) : ↥A) : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
  rw [show ((((p : ℕ) : ↥A) : ↥A) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) from rfl]
  exact natCast_prime_ne_zero p

theorem dom_nonempty_of_modulus_eq_mul_self {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F) (c : ↥A) (hc0 : (c : L) ≠ 0) (hc : ((An.modulus : ↥A) : L) = c * c) :
    An.dom.Nonempty := by
  have hmul : An.modulus = c * c := Subtype.ext (by rw [hc]; rfl)
  have hcm : c ∈ maximalIdeal ↥A := by
    have h := An.modulus_mem
    rw [hmul] at h
    exact ((Ideal.IsPrime.mem_or_mem inferInstance h).elim id id)
  obtain ⟨P, hP, -⟩ := (An.existsUnique_evalAt_eq c hcm hc0 ⟨c, hcm, hc⟩).exists
  exact ⟨P, hP⟩

theorem dom_nonempty_of_modulus_ne_zero {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F) (h0 : ((An.modulus : ↥A) : L) ≠ 0) : An.dom.Nonempty := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self ((An.modulus : ↥A) : L)
  have hz0 : z ≠ 0 := fun h => h0 (by rw [hz, h, mul_zero])
  have hzA : z ∈ A := by
    rcases A.mem_or_inv_mem z with h | h
    · exact h
    · have e : z = ((An.modulus : ↥A) : L) * z⁻¹ := by rw [hz, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
      rw [e]
      exact A.mul_mem _ _ (An.modulus).2 h
  exact dom_nonempty_of_modulus_eq_mul_self An ⟨z, hzA⟩ hz0 hz

theorem dom_nonempty_of_modulus_eq_pow_mul {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F) (p : ↥A) (hp0 : (p : L) ≠ 0) (e : ℕ) (u : ↥A) (hu : IsUnit u) (hmod : An.modulus = p ^ e * u) :
    An.dom.Nonempty := by
  refine dom_nonempty_of_modulus_ne_zero An ?_
  rw [hmod]
  have hu0 : ((u : ↥A) : L) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
  have : (((p ^ e * u : ↥A)) : L) = (p : L) ^ e * (u : L) := by norm_cast
  rw [this]
  exact mul_ne_zero (pow_ne_zero _ hp0) hu0

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem read_const (𝔛 : XHDRModelAtP p M H hpM hj)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (ρ : R p →+* ↥A)
    {O : Type} [CommRing O] (ρO : R p →+* O) (ιA : O →+* ↥A) (hιAρ : ιA.comp ρO = ρ)
    (jO : O →+* AlgebraicClosure ℚ) (hιA : A.subtype.comp ιA = jO)
    (gA : 𝔛.Meta.C ⟶ XO (ΓM M H) hj ρ)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (U₀ : (XO (ΓM M H) hj ρO).Opens) (o : O)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))))] :
    𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))
      ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom
        (((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).appLE ⊤ (U₀.ι ''ᵁ ⊤) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))))) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (jO o) := by
  apply 𝔛.Meta.ffEquiv.injective
  rw [RingEquiv.apply_symm_apply, 𝔛.Meta.ffEquiv_algebraMap]
  have hcomp : (gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom
        (((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).appLE ⊤ (U₀.ι ''ᵁ ⊤) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) =
      ((gA ≫ Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom (((XO (ΓM M H) hj ρO).presheaf.map (homOfLE (le_top : U₀.ι ''ᵁ ⊤ ≤ ⊤)).op).hom
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) := rfl
  rw [hcomp]
  have hnat := congrArg (fun ψ => ψ.hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) ((gA ≫ Cartier.q ρO ρ ιA hιAρ).naturality (homOfLE (le_top : U₀.ι ''ᵁ ⊤ ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  rw [hnat]
  refine (TopCat.Presheaf.germ_res_apply 𝔛.Meta.C.presheaf _ _ _ _).trans ?_
  have hnat2 := congrArg (fun φ => φ.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom jO))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat2
  show _ = (𝔛.Meta.C.presheaf.germ ⊤ (genericPoint 𝔛.Meta.C) trivial).hom
    (𝔛.Meta.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv.hom (jO o)))
  rw [hnat2, ← CommRingCat.comp_apply _ 𝔛.Meta.toBase.appTop, ← Scheme.Hom.comp_appTop,
    ← Cartier.gA_q_snd ρO ρ ιA hιAρ 𝔛 jO hιA gA hgA₂, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  rfl

theorem read_mul_read_eq_algebraMap (𝔛 : XHDRModelAtP p M H hpM hj)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (ρ : R p →+* ↥A)
    {O : Type} [CommRing O] (ρO : R p →+* O) (ιA : O →+* ↥A) (hιAρ : ιA.comp ρO = ρ)
    (jO : O →+* AlgebraicClosure ℚ) (hιA : A.subtype.comp ιA = jO)
    (gA : 𝔛.Meta.C ⟶ XO (ΓM M H) hj ρ)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (U₀ : (XO (ΓM M H) hj ρO).Opens) (o : O)
    (gv gu : Γ(XO (ΓM M H) hj ρO, U₀.ι ''ᵁ ⊤))
    (hprod : gv * gu = ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).appLE ⊤ (U₀.ι ''ᵁ ⊤) le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))))] :
    𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))
      ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gv))) *
    𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))
      ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gu))) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (jO o) := by
  have h := read_const 𝔛 ρ ρO ιA hιAρ jO hιA gA hgA₂ U₀ o
  rw [← hprod, map_mul, map_mul, map_mul, map_mul] at h
  exact h

theorem ord_placeOfPoint_read_gu_pow_eq_zero (𝔛 : XHDRModelAtP p M H hpM hj)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (ρ : R p →+* ↥A)
    {O : Type} [CommRing O] (ρO : R p →+* O) (ιA : O →+* ↥A) (hιAρ : ιA.comp ρO = ρ)
    (jO : O →+* AlgebraicClosure ℚ) (hιA : A.subtype.comp ιA = jO)
    (gA : 𝔛.Meta.C ⟶ XO (ΓM M H) hj ρ)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (U₀ : (XO (ΓM M H) hj ρO).Opens) (o : O) (ho : jO o ≠ 0)
    (gv gu : Γ(XO (ΓM M H) hj ρO, U₀.ι ''ᵁ ⊤))
    (hprod : gv * gu = ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).appLE ⊤ (U₀.ι ''ᵁ ⊤) le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))
    (m : ℕ) (x : closedPoints 𝔛.Meta.C)
    (hx : gA.base x.1 ∈ Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))))] :
    (𝔛.Meta.placeOfPoint x).ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))
      ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gu ^ m)))) = 0 := by
  apply AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit 𝔛.Meta _ x hx
  rw [map_pow]
  refine IsUnit.pow m ?_
  have hcomp : (gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gu) =
      ((gA ≫ Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gu := rfl
  rw [hcomp]
  have hunit : IsUnit (((gA ≫ Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom (gv * gu)) := by
    rw [hprod]
    exact Cartier.isUnit_app_const (pullback.snd _ _) U₀ 𝔛.Meta.toBase jO (gA ≫ Cartier.q ρO ρ ιA hιAρ)
      (by rw [Category.assoc, Cartier.gA_q_snd ρO ρ ιA hιAρ 𝔛 jO hιA gA hgA₂]) o (isUnit_iff_ne_zero.mpr ho)
  rw [map_mul] at hunit
  exact isUnit_of_mul_isUnit_right hunit

end CartierWidth

namespace CartierWidth

private theorem _root_.CartierWidth.ne_zero_of_ord_eq_one {k Fb : Type*} [Field k] [Field Fb] [Algebra k Fb] (x : AlgebraicCurve.Place k Fb) {r : Fb}
    (h : x.ord r = 1) : r ≠ 0 := by
  rintro rfl
  rw [AlgebraicCurve.Place.ord_zero] at h
  exact zero_ne_one h

p2m_export "CartierWidth" "ne_zero_of_ord_eq_one"
end CartierWidth

namespace CartierWidth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem read_mul_read_eq_algebraMap' (𝔛 : XHDRModelAtP p M H hpM hj)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (ρ : R p →+* ↥A)
    {O : Type} [CommRing O] (ρO : R p →+* O) (ιA : O →+* ↥A) (hιAρ : ιA.comp ρO = ρ)
    (jO : O →+* AlgebraicClosure ℚ) (hιA : A.subtype.comp ιA = jO)
    (gA : 𝔛.Meta.C ⟶ XO (ΓM M H) hj ρ)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (U₀ : (XO (ΓM M H) hj ρO).Opens) (o : O)
    (gv gu : Γ(XO (ΓM M H) hj ρO, U₀.ι ''ᵁ ⊤))
    (hprod : gv * gu = ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).appLE ⊤ (U₀.ι ''ᵁ ⊤) le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))
    (c : AlgebraicClosure ℚ) (hc : jO o = c)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))))] :
    𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))
      ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gv))) *
    𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))
      ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom gu))) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c := by
  rw [← hc]
  exact read_mul_read_eq_algebraMap 𝔛 ρ ρO ιA hιAρ jO hιA gA hgA₂ U₀ o gv gu hprod

end CartierWidth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

set_option maxHeartbeats 6400000 in
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

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
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
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    :
    ∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
      ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U)
        (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (t : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),

        (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0 ∧
            ∃ h : P.evalAt (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) → IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ U _ hQ).hom t)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) →
          ∃ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hWU : W ≤ U) (hQW : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ W) (t₀ : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)),
            (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map (homOfLE hWU).op t = ((p : ℕ) : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)) ^ k * t₀ ∧
            IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ W _ hQW).hom t₀)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C), gA.base x.1 ∈ U → (𝔛.Meta.placeOfPoint x).ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0) := by
  intro s n hn0 hn1
  classical

  obtain ⟨ιA, ρO, hιAval, hιAρ, hιAinj, hDVR, hϖ, hmaxmem, hsurjres, hinert⟩ :=
    ValuationSubring.exists_ringHom_comap_fixedField_inertiaSubgroupIn_comp_eq_and_isDiscreteValuationRing p A hA ρ hρ
  haveI := hDVR
  let toκ := (IsLocalRing.residue ↥A).comp ιA
  have htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ := by
    show ((IsLocalRing.residue ↥A).comp ιA).comp ρO = _
    rw [RingHom.comp_assoc, hιAρ]
  have hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ := rfl
  have hsurj : Function.Surjective toκ := hsurjres
  let jO := A.subtype.comp ιA
  have hιA : A.subtype.comp ιA = jO := rfl
  have hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ) := by
    show (A.subtype.comp ιA).comp ρO = _
    rw [RingHom.comp_assoc, hιAρ, hρ]

  have hrat := ModularCurve.XHDRModelAtP.forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ _ ρO toκ htoκ hsurj
  obtain ⟨e', he', U₀, hxU, f, hover, hfib, hpt, het, hor₁, hor₂, hor₃, hor₄⟩ :=
    ModularCurve.XHDRModelAtP.forall_exists_orientedEtaleCrossingChart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ _ ρO hϖ toκ htoκ
      (bcMap (ΓM M H) hj ρO toκ htoκ) (bcMap_fst _ _ _ _ _) (bcMap_snd _ _ _ _ _) hrat n

  obtain rfl : bc = bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl :=
    pullback.hom_ext (by rw [hbc₁, bcMap_fst]) (by rw [hbc₂, bcMap_snd])
  have hbcq := Cartier.bc_q ρO ρ ιA hιAρ (IsLocalRing.residue ↥A) toκ hιAκ htoκ (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl)
    (bcMap_fst _ _ _ _ _) (bcMap_snd _ _ _ _ _)
  have hinj : Function.Injective (bcMap (ΓM M H) hj ρO toκ htoκ).base :=
    Cartier.bcMap_base_injective ρO toκ htoκ hsurj

  have hnU : (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base
      ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈
      Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤) := by
    show (Cartier.q ρO ρ ιA hιAρ).base _ ∈ U₀.ι ''ᵁ ⊤
    rw [← Scheme.Hom.comp_apply, hbcq, Scheme.Opens.ι_image_top]
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using hxU
  haveI hneU : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) :=
    (ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H A hA hj 𝔛 ρ hρ gA hgA₁ hgA₂).2.1 _ ⟨⟨_, hnU⟩⟩

  have hprod := Cartier.chart_gv_mul_gu (pullback.snd _ _) U₀ _ f hover
  have hp0 : jO (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e') ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

  have hgAeq : gA = 𝔛.eeta ≫ (pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) :=
    pullback.hom_ext (by rw [hgA₁, Category.assoc, pullback.lift_fst, Category.comp_id])
      (by rw [hgA₂, Category.assoc, pullback.lift_snd, ← Category.assoc, 𝔛.heeta])
  have hgen : genericPoint 𝔛.Meta.C ∈ gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) := by
    obtain ⟨⟨x, hx⟩⟩ := hneU
    exact (genericPoint_specializes x).mem_open (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).isOpen hx
  have hgen' : genericPoint 𝔛.Meta.C ∈ 𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) := by
    have h := hgen
    rw [hgAeq] at h
    exact h

  have hordAll : ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom ((((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))) ^ (k / e s))))) = 0 := by
    intro P hP
    have hdomP := ((hAn s).1 P).mp hP
    have hex :=
      (ModularCurve.XHDRModelAtP.exists_section_through_crossing_iff_reduceFst_eq_and_not_isStrict_of_offDiag_of_surjective
        p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat'
        _ ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ hsurj n U₀ hxU s (Prod.ext hn0 hn1) P).mpr hdomP
    have hPy : 𝔛.Meta.placeOfPoint (pointEquivClosedPoint 𝔛.Meta.toBase (𝔛.Meta.pointEquivPlace.symm P)) = P := by
      rw [← AlgebraicCurve.CurveModel.pointEquivPlace_apply, Equiv.apply_symm_apply]
    have hcU : gA.base (pointEquivClosedPoint 𝔛.Meta.toBase (𝔛.Meta.pointEquivPlace.symm P)).1 ∈ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) := by
      rw [pointEquivClosedPoint_apply_coe]
      show (Cartier.q ρO ρ ιA hιAρ).base (gA.base (((𝔛.Meta.pointEquivPlace.symm P).1).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))) ∈ U₀.ι ''ᵁ ⊤
      rw [← Scheme.Hom.comp_apply _ (Cartier.q ρO ρ ιA hιAρ), ← Scheme.Hom.comp_apply _ (gA ≫ Cartier.q ρO ρ ιA hιAρ),
        Cartier.gA_q ρO ρ ιA hιAρ 𝔛 jO hjO hιA gA hgA₁ hgA₂, ← hex.choose_spec.2.1]
      exact ⟨hex.choose.base ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))), trivial, rfl⟩
    rw [← hPy]
    exact Cartier.ord_placeOfPoint_read_pow_eq_zero 𝔛 ρ ρO ιA hιAρ jO hιA gA hgA₂ U₀ _ hp0 _ _ hprod (k / e s) _ hcU

  have hxP : ∀ P ∈ (An s).dom, ∃ x : closedPoints 𝔛.Meta.C, 𝔛.Meta.placeOfPoint x = P ∧ gA.base x.1 ∈ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) := by
    intro P hP
    have hdomP := ((hAn s).1 P).mp hP
    have hex := (ModularCurve.XHDRModelAtP.exists_section_through_crossing_iff_reduceFst_eq_and_not_isStrict_of_offDiag_of_surjective
        p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat'
        _ ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ hsurj n U₀ hxU s (Prod.ext hn0 hn1) P).mpr hdomP
    refine ⟨pointEquivClosedPoint 𝔛.Meta.toBase (𝔛.Meta.pointEquivPlace.symm P), ?_, ?_⟩
    · rw [← AlgebraicCurve.CurveModel.pointEquivPlace_apply, Equiv.apply_symm_apply]
    · rw [pointEquivClosedPoint_apply_coe]
      show (Cartier.q ρO ρ ιA hιAρ).base (gA.base (((𝔛.Meta.pointEquivPlace.symm P).1).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))) ∈ U₀.ι ''ᵁ ⊤
      rw [← Scheme.Hom.comp_apply _ (Cartier.q ρO ρ ιA hιAρ), ← Scheme.Hom.comp_apply _ (gA ≫ Cartier.q ρO ρ ιA hιAρ),
        Cartier.gA_q ρO ρ ιA hιAρ 𝔛 jO hjO hιA gA hgA₁ hgA₂, ← hex.choose_spec.2.1]
      exact ⟨hex.choose.base ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))), trivial, rfl⟩

  have hζ0 : ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))))) = 0 := by
    intro P hP
    have hx := hxP P hP
    rw [← hx.choose_spec.1]
    have h := Cartier.ord_placeOfPoint_read_pow_eq_zero 𝔛 ρ ρO ιA hιAρ jO hιA gA hgA₂ U₀ _ hp0 _ _ hprod 1 _ hx.choose_spec.2
    rw [pow_one] at h
    exact h
  have hη0 : ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))))) = 0 := by
    intro P hP
    have hx := hxP P hP
    rw [← hx.choose_spec.1]
    have h := CartierWidth.ord_placeOfPoint_read_gu_pow_eq_zero 𝔛 ρ ρO ιA hιAρ jO hιA gA hgA₂ U₀ _ hp0 _ _ hprod 1 _ hx.choose_spec.2
    rw [pow_one] at h
    exact h

  have hζη : (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))))) * (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))))) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((((p : ℕ) : ↥A) : ↥A) : AlgebraicClosure ℚ) ^ e') := by
    exact CartierWidth.read_mul_read_eq_algebraMap' 𝔛 ρ ρO ιA hιAρ jO hιA gA hgA₂ U₀ _ _ _ hprod _
      (by rw [map_pow, map_natCast]; rfl)

  have hdomne : (An s).dom.Nonempty :=
    CartierWidth.dom_nonempty_of_modulus_eq_pow_mul (An s) ((p : ℕ) : ↥A) (CartierWidth.coe_natCast_ne_zero A p) (e s)
      (hAn s).2.1.choose (hAn s).2.1.choose_spec.1 (hAn s).2.1.choose_spec.2
  have hξ0 : 𝔛.ξzero A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) := by
    refine Specializes.mem_open ?_ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)).isOpen hnU
    have hsp := (𝔛.efib_genericPoint_specializes A hA ρ hρ (pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) n)).map
      (𝔛.comp A hA ρ hρ 1 ≫ (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl)).base.hom.continuous
    have hcond : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n =
        (𝔛.comp A hA ρ hρ 1).base ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) := by
      rw [pullback.condition]; rfl
    rw [hcond]
    first | simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using hsp | exact hsp | (simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hsp; exact hsp)

  have h94 :=
    (ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      θ Psp Rpd hwgen (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) hgen' (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))).2 hξ0
  have hg₁ := h94.choose_spec.1.choose
  have h₂' := h94.choose
  have hres' := h94.choose_spec.1.choose_spec
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h₂' hres'

  have hread : (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))))) = (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) :=
    congrArg 𝔛.Meta.ffEquiv.symm (CartierGeneric.germToFunctionField_app_of_eq_comp gA 𝔛.eeta _ hgAeq _ hgen' _)
  have hζ2U : (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) ∈ Rpd.R₂.integers := h₂'

  have hunif :=
    (ModularCurve.XHDRModelAtP.ord_placeOn_germ_chart_eq_one_of_chart_of_residue_surjective p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      _ ρO hϖ toκ htoκ hsurj jO hjO ιA hιA hιAκ n e' he' U₀ hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄).1
  have hg₁' := hunif.choose
  have hord1 := hunif.choose_spec
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  have e2 := CartierGeneric.germ_app_comp_congr (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl)) (Cartier.q ρO ρ ιA hιAρ) (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ)
    (by simp only [Category.assoc, hbcq]) (U₀.ι ''ᵁ ⊤) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₁ hg₁' ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))
  have A1 := congrArg (fun x => s.1.2.ord x) hres'
  have A2 := congrArg (fun x => s.1.2.ord ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm x)) e2
  have A3 := congrArg (fun P => AlgebraicCurve.Place.ord P ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
    (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ) ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₁').hom
      (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))))) hn1.symm
  have hζordU : s.1.2.ord (Rpd.R₂.residue ⟨_, hζ2U⟩) = 1 := A1.trans (A2.trans (A3.trans hord1))

  have hξinf : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) := by
    refine Specializes.mem_open ?_ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)).isOpen hnU
    have hsp := (𝔛.efib_genericPoint_specializes A hA ρ hρ (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) n)).map
      (𝔛.comp A hA ρ hρ 0 ≫ (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl)).base.hom.continuous
    first | simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using hsp | exact hsp | (simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hsp; exact hsp)

  have h94i :=
    (ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      θ Psp Rpd hwgen (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) hgen' (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))).1 hξinf
  have hg₀ := h94i.choose_spec.1.choose
  have h₁' := h94i.choose
  have hres₁' := h94i.choose_spec.1.choose_spec
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h₁' hres₁'

  have hreadU : (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))))) = (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) :=
    congrArg 𝔛.Meta.ffEquiv.symm (CartierGeneric.germToFunctionField_app_of_eq_comp gA 𝔛.eeta _ hgAeq _ hgen' _)
  have hη1U : (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) ∈ Rpd.R₁.integers := h₁'

  have hunif0 :=
    (ModularCurve.XHDRModelAtP.ord_placeOn_germ_chart_eq_one_of_chart_of_residue_surjective p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      _ ρO hϖ toκ htoκ hsurj jO hjO ιA hιA hιAκ n e' he' U₀ hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄).2
  have hg₀' := hunif0.choose
  have hord0 := hunif0.choose_spec
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  have e2i := CartierGeneric.germ_app_comp_congr (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl)) (Cartier.q ρO ρ ιA hιAρ) (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ)
    (by simp only [Category.assoc, hbcq]) (U₀.ι ''ᵁ ⊤) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀ hg₀' ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))
  have B1 := congrArg (fun x => s.1.1.ord x) hres₁'
  have B2 := congrArg (fun x => s.1.1.ord ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm x)) e2i
  have B3 := congrArg (fun P => AlgebraicCurve.Place.ord P ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
    (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ) ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀').hom
      (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))))) hn0.symm
  have hηordU : s.1.1.ord (Rpd.R₁.residue ⟨_, hη1U⟩) = 1 := B1.trans (B2.trans (B3.trans hord0))

  have hζ0U : ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) = 0 := fun P hP =>
    (congrArg (fun x => P.ord x) hread).symm.trans (hζ0 P hP)
  have hη0U : ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) = 0 := fun P hP =>
    (congrArg (fun x => P.ord x) hreadU).symm.trans (hη0 P hP)
  have hζηU : (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) * (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((((p : ℕ) : ↥A) : ↥A) : AlgebraicClosure ℚ) ^ e') :=
    (congrArg₂ (· * ·) hread hreadU).symm.trans hζη

  have hζatt : ∃ h : hdomne.some.evalAt (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) * (hdomne.some.evalAt (An s).param) ^ (-(1 : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
    have hgen : ∀ m : ℤ, s.1.2.ord (Rpd.R₂.residue ⟨_, hζ2U⟩) = m →
        ∃ h : hdomne.some.evalAt (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) * (hdomne.some.evalAt (An s).param) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
      rintro m rfl
      exact (hAn s).2.2.2.2.2.1.choose_spec.2 _ hζ2U (CartierWidth.ne_zero_of_ord_eq_one _ hζordU) hζ0U _ hdomne.some_mem
    exact hgen 1 hζordU
  have hηatt : ∃ h : hdomne.some.evalAt (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) *
      (hdomne.some.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^ (-(1 : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
    have hgen : ∀ m : ℤ, s.1.1.ord (Rpd.R₁.residue ⟨_, hη1U⟩) = m →
        ∃ h : hdomne.some.evalAt (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) *
          (hdomne.some.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
      rintro m rfl
      exact (hAn s).2.2.2.2.2.2.choose_spec.2 _ hη1U (CartierWidth.ne_zero_of_ord_eq_one _ hηordU) hη0U _ hdomne.some_mem
    exact hgen 1 hηordU
  have hwidth : e' = e s :=
    AlgebraicCurve.Annulus.eq_of_mul_eq_algebraMap_pow_of_isUnit_evalAt_mul_evalAt_param_zpow_neg_one (An s)
      ((p : ℕ) : ↥A) (CartierWidth.natCast_mem_maximalIdeal_of_liesOverPrime hA) (CartierWidth.coe_natCast_ne_zero A p)
      (e s) (hAn s).2.1.choose (hAn s).2.1.choose_spec.1 (hAn s).2.1.choose_spec.2
      (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) (𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.U (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) e' hζηU _ hdomne.some_mem (hζ0U _ hdomne.some_mem) (hη0U _ hdomne.some_mem) hζatt hηatt
  have hkm : e' * (k / e s) = k := by
    rw [hwidth]; exact Nat.mul_div_cancel' (hk s)
  refine ⟨(Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)), hnU, hneU, ((((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))) ^ (k / e s)), ?_, ?_, ?_, ?_⟩
  ·

    have hTeq : (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom ((((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))) ^ (k / e s))))) = (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e'))))))))) ^ (k / e s) := by
      simp only [map_pow]
    have hTeq2 := hTeq.trans (congrArg (fun w => w ^ (k / e s)) hread)
    have hT2 := pow_mem hζ2U (k / e s)
    have hsub : (⟨_, hζ2U⟩ : ↥Rpd.R₂.integers) ^ (k / e s) = ⟨_, hT2⟩ := Subtype.ext (SubmonoidClass.coe_pow _ _)
    have hresT := (congrArg Rpd.R₂.residue hsub).symm.trans (map_pow Rpd.R₂.residue _ (k / e s))
    have hres0 := CartierGeneric.ne_zero_of_ord_eq_one _ hζordU
    have hresT0 := ne_of_eq_of_ne hresT (pow_ne_zero (k / e s) hres0)
    have hordT : s.1.2.ord (Rpd.R₂.residue ⟨_, hT2⟩) = (((k / e s) : ℕ) : ℤ) :=
      (congrArg s.1.2.ord hresT).trans ((CartierGeneric.ord_pow _ _ _).trans (by rw [hζordU, mul_one]))
    have hordAllU : ∀ P ∈ (An s).dom, P.ord ((𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) ^ (k / e s)) = 0 :=
      fun P hP => (congrArg (fun w => AlgebraicCurve.Place.ord P w) hTeq2).symm.trans (hordAll P hP)

    have hatt := (hAn s).2.2.2.2.2.1.choose_spec.2
    refine ⟨1, one_ne_zero, fun P hP => ⟨hordAll P hP, ?_⟩⟩
    have hlaw := hatt _ hT2 hresT0 hordAllU P hP
    refine CartierGeneric.existsIsUnit_congr ?_ hlaw
    refine (congrArg (fun n : ℤ => P.evalAt ((𝔛.Meta.ffEquiv.symm ((𝔛.Meta.C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))) (genericPoint 𝔛.Meta.C) hgen').hom ((𝔛.eeta.app ((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)))).hom (((pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])).app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom (((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))))))) ^ (k / e s)) * (P.evalAt (An s).param) ^ (-n)) hordT).trans ?_
    refine (congrArg (fun w => P.evalAt w * (P.evalAt (An s).param) ^ (-(((k / e s) : ℕ) : ℤ))) hTeq2.symm).trans ?_
    exact congrArg (fun w => w * (P.evalAt (An s).param) ^ (-(((k / e s) : ℕ) : ℤ))) (mul_one (P.evalAt (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))) ((gA.app (Cartier.q ρO ρ ιA hιAρ ⁻¹ᵁ (U₀.ι ''ᵁ ⊤))).hom ((((Cartier.q ρO ρ ιA hιAρ).app (U₀.ι ''ᵁ ⊤)).hom ((U₀.ι.appIso ⊤).inv.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))).inv.hom (MvPolynomial.CrossingQuotient.V (((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ^ e')))))) ^ (k / e s))))))).symm
  ·
    intro Q hQ hne
    exact Cartier.isUnit_germ_pullback_gv_pow_of_comp_one 𝔛 A hA ρ hρ ρO toκ htoκ ιA hιAρ hιAκ _ (bcMap_fst _ _ _ _ _) (bcMap_snd _ _ _ _ _)
      hinj n e' U₀ f hfib hor₄ (k / e s) Q hQ hne
  ·
    intro Q hQ hne
    exact Cartier.exists_opens_eq_pow_mul_isUnit_of_comp_zero 𝔛 A hA ρ hρ ρO toκ htoκ ιA hιAρ hιAκ _ (bcMap_fst _ _ _ _ _) (bcMap_snd _ _ _ _ _)
      hinj n e' U₀ f hover hfib hor₃ (k / e s) k hkm Q hQ hne
  ·
    intro x hx
    exact Cartier.ord_placeOfPoint_read_pow_eq_zero 𝔛 ρ ρO ιA hιAρ jO hιA gA hgA₂ U₀ _ hp0 _ _ hprod (k / e s) x hx

end S_ModularCurve_XHDRModelAtP_exists_section_slopeLaw_isUnit_ord_eq_zero_at_crossing_of_dvd_width
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_section_slopeLaw_isUnit_ord_eq_zero_at_crossing_of_dvd_width (solution)
