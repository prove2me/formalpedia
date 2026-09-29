-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/64f56c90-1599-51a3-a4ab-0c37aa3582f0

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegrallyClosed_stalk_and_ringKrullDim_eq_two_of_isIso_residueFieldMap_of_not_mem_range_comp
import Theorems.Thm_ModularCurve_XHDRModelAtP_isLocalHom_and_injective_stalkRead_and_forall_section_evalAt_eq_of_point
import Theorems.Thm_IsIntegrallyClosed_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_point
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_one
import Theorems.Thm_IsIntegrallyClosed_mem_range_of_isPrime_span_of_forall_height_eq_one_of_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA MvPolynomial.CrossingQuotient.Resolution.instIsAffineXSchemeOpenCover MvPolynomial.CrossingQuotient.isOpenImmersion_overlapToChartRight MvPolynomial.CrossingQuotient.isOpenImmersion_torusToOverlap MvPolynomial.CrossingQuotient.isLocallyDirected_glueDiagram MvPolynomial.CrossingQuotient.GlueIndex.instPreorder MvPolynomial.CrossingQuotient.isOpenImmersion_torusToChart MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιTorus MvPolynomial.CrossingQuotient.isOpenImmersion_glueMap MvPolynomial.CrossingQuotient.GlueIndex.instLE MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιOverlap MvPolynomial.CrossingQuotient.isLocalization_away_torusRing MvPolynomial.CrossingQuotient.isOpenImmersion_glueDiagram_map MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ι AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup"
p2m_attr_erase "instance" "KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ MvPolynomial.CrossingQuotient.GlueIndex.chart_le_overlap MvPolynomial.CrossingQuotient.GlueIndex.torus.sizeOf_spec MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_torus MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.ι_toSpec MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing_assoc MvPolynomial.CrossingQuotient.glueMap_torus_overlap MvPolynomial.CrossingQuotient.GlueIndex.chart_le_torus MvPolynomial.CrossingQuotient.glueMap_overlap_overlap MvPolynomial.CrossingQuotient.GlueIndex.torus_le MvPolynomial.CrossingQuotient.Resolution.openCover_f MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing MvPolynomial.CrossingQuotient.glueMap_torus_chart MvPolynomial.CrossingQuotient.glueMap_torus_torus MvPolynomial.CrossingQuotient.glueDiagram_obj MvPolynomial.CrossingQuotient.GlueIndex.chart.injEq MvPolynomial.CrossingQuotient.GlueIndex.chart_le_chart MvPolynomial.CrossingQuotient.GlueIndex.chart.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.openCover_X MvPolynomial.CrossingQuotient.Resolution.openCover_I₀ MvPolynomial.CrossingQuotient.GlueIndex.overlap.injEq MvPolynomial.CrossingQuotient.glueMap_chart_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_overlap"
p2m_attr_erase "simp" "MvPolynomial.CrossingQuotient.Resolution.ι_toSpec_assoc MvPolynomial.CrossingQuotient.lift_V MvPolynomial.CrossingQuotient.lift_U MvPolynomial.CrossingQuotient.monomial_neg_natCast MvPolynomial.CrossingQuotient.monomial_zero MvPolynomial.CrossingQuotient.monomial_natCast MvPolynomial.CrossingQuotient.powMap_mk_X RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

universe u

namespace HartogsAux

theorem div_mul_algebraMap_eq_of_mul_eq {B K L : Type*} [CommRing B] [IsDomain B] [Field K] [Algebra B K] [IsFractionRing B K]
    [CommRing L] (e : B →+* L) (he : Function.Injective e) (f : L) (r₀ s₀ : B) (hs₀ : s₀ ≠ 0)
    (hfrac : f * e s₀ = e r₀) (r s : B) (h : f * e s = e r) :
    algebraMap B K r₀ / algebraMap B K s₀ * algebraMap B K s = algebraMap B K r := by
  have key : r₀ * s = r * s₀ := he (by
    rw [map_mul, map_mul, ← hfrac, ← h]; ring)
  have hs₀K : algebraMap B K s₀ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs₀)
  rw [div_mul_eq_mul_div, div_eq_iff hs₀K, ← map_mul, ← map_mul, key]

theorem eq_apply_of_algebraMap_eq_div {B K L : Type*} [CommRing B] [IsDomain B] [Field K] [Algebra B K] [IsFractionRing B K]
    [CommRing L] [IsDomain L] (e : B →+* L) (he : Function.Injective e) (f : L) (r₀ s₀ : B) (hs₀ : s₀ ≠ 0)
    (hfrac : f * e s₀ = e r₀) (b : B) (hb : algebraMap B K b = algebraMap B K r₀ / algebraMap B K s₀) : f = e b := by
  have hs₀K : algebraMap B K s₀ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs₀)
  rw [eq_div_iff hs₀K, ← map_mul] at hb
  have hbs : b * s₀ = r₀ := IsFractionRing.injective B K hb
  have hes : e s₀ ≠ 0 := (map_ne_zero_iff e he).mpr hs₀
  apply mul_right_cancel₀ hes
  rw [hfrac, ← map_mul, hbs]

theorem pullback_map_id_comp {X S T₁ T₂ T₃ : Scheme.{u}} (f : X ⟶ S) (g₁ : T₁ ⟶ S) (g₂ : T₂ ⟶ S) (g₃ : T₃ ⟶ S)
    (s : T₁ ⟶ T₂) (t : T₂ ⟶ T₃) (st : T₁ ⟶ T₃) (hst : s ≫ t = st)
    (e₁ : f ≫ 𝟙 S = 𝟙 X ≫ f) (e₂ : g₁ ≫ 𝟙 S = s ≫ g₂) (e₁' : f ≫ 𝟙 S = 𝟙 X ≫ f) (e₂' : g₂ ≫ 𝟙 S = t ≫ g₃)
    (e₁'' : f ≫ 𝟙 S = 𝟙 X ≫ f) (e₂'' : g₁ ≫ 𝟙 S = st ≫ g₃) :
    pullback.map f g₁ f g₂ (𝟙 X) s (𝟙 S) e₁ e₂ ≫ pullback.map f g₂ f g₃ (𝟙 X) t (𝟙 S) e₁' e₂' =
      pullback.map f g₁ f g₃ (𝟙 X) st (𝟙 S) e₁'' e₂'' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hst]

theorem base_apply_of_comp_eq {X Y Z : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ Z) (c : X ⟶ Z) (h : a ≫ g = c) (y : X) :
    g.base (a.base y) = c.base y := by
  rw [← Scheme.Hom.comp_apply, h]

theorem exists_stalkMap_stalkSpecializes_eq {XQ XA X' : Scheme.{u}} (prA : XQ ⟶ XA) (g : XA ⟶ X') (prJ : XQ ⟶ X')
    (hJ : prA ≫ g = prJ) (q : XQ) {x₀ : XA} {x' : X'} (hspA : prA.base q ⤳ x₀) (hsp' : prJ.base q ⤳ x')
    (hgx : g.base x₀ = x') (b : X'.presheaf.stalk x') :
    ∃ b₀ : XA.presheaf.stalk x₀,
      (prJ.stalkMap q).hom ((X'.presheaf.stalkSpecializes hsp').hom b) =
        (prA.stalkMap q).hom ((XA.presheaf.stalkSpecializes hspA).hom b₀) := by
  subst hJ; subst hgx
  refine ⟨(g.stalkMap x₀).hom b, ?_⟩
  rw [Scheme.Hom.stalkMap_comp]
  change (prA.stalkMap q).hom ((g.stalkMap (prA.base q)).hom ((X'.presheaf.stalkSpecializes hsp').hom b)) = _
  exact congrArg (prA.stalkMap q).hom (Scheme.Hom.stalkSpecializes_stalkMap_apply g _ _ hspA b)

end HartogsAux

namespace HartogsAux

theorem bcMap_comp_pullback_map {p : ℕ} (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    {O O' κ : Type} [CommRing O] [CommRing O'] [CommRing κ] (ρO : R p →+* O) (ρO' : R p →+* O') (ι : O' →+* O)
    (toκ : O →+* κ) {toκ₀ : R p →+* κ} (h : toκ.comp ρO = toκ₀) (h' : (toκ.comp ι).comp ρO' = toκ₀)
    (e₁ : toBase p Γ hj ≫ 𝟙 _ = 𝟙 _ ≫ toBase p Γ hj)
    (e₂ : Spec.map (CommRingCat.ofHom ρO) ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom ρO')) :
    bcMap Γ hj ρO toκ h ≫ pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ι)) (𝟙 _) e₁ e₂ =
      bcMap Γ hj ρO' (toκ.comp ι) h' := by
  rw [bcMap, bcMap]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end HartogsAux

namespace HART

theorem snd_SpecToEquivOfField_comp {K : Type u} [Field K] {X Y : Scheme.{u}} (a : Spec (CommRingCat.of K) ⟶ X) (t : X ⟶ Y) :
    (Scheme.SpecToEquivOfField K Y (a ≫ t)).2 =
      t.residueFieldMap (a.base (closedPoint K)) ≫ (Scheme.SpecToEquivOfField K X a).2 := by
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_mk]
  have i1 : IsLocalHom (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo a)) := Scheme.isLocalHom_stalkClosedPointTo a
  have i2 : IsLocalHom (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo (a ≫ t))) := Scheme.isLocalHom_stalkClosedPointTo (a ≫ t)
  have h3 : Y.residue _ ≫ @Scheme.descResidueField _ _ Y _ (Scheme.stalkClosedPointTo (a ≫ t)) i2 = Scheme.stalkClosedPointTo (a ≫ t) :=
    @Scheme.residue_descResidueField _ _ Y _ _ i2
  have h4 : Y.residue (t.base (a.base (closedPoint K))) ≫ t.residueFieldMap (a.base (closedPoint K)) ≫
      @Scheme.descResidueField _ _ X _ (Scheme.stalkClosedPointTo a) i1 = t.stalkMap (a.base (closedPoint K)) ≫ Scheme.stalkClosedPointTo a := by
    rw [Scheme.residue_residueFieldMap_assoc, @Scheme.residue_descResidueField _ _ X _ _ i1]
  have h5 : Y.residue (t.base (a.base (closedPoint K))) ≫ t.residueFieldMap (a.base (closedPoint K)) ≫
      @Scheme.descResidueField _ _ X _ (Scheme.stalkClosedPointTo a) i1 =
        Y.residue (t.base (a.base (closedPoint K))) ≫ @Scheme.descResidueField _ _ Y _ (Scheme.stalkClosedPointTo (a ≫ t)) i2 :=
    h4.trans ((Scheme.stalkClosedPointTo_comp a t).symm.trans h3.symm)
  haveI : Epi (Y.residue (t.base (a.base (closedPoint K)))) := ConcreteCategory.epi_of_surjective _ (Y.residue_surjective _)
  exact ((cancel_epi (Y.residue (t.base (a.base (closedPoint K))))).mp h5).symm

theorem residueFieldCongr_hom_comp_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) {x y : X} (h : x = y) :
    (Y.residueFieldCongr (congrArg f.base h : f.base x = f.base y)).hom ≫ f.residueFieldMap y =
      f.residueFieldMap x ≫ (X.residueFieldCongr h).hom := by
  subst h
  simp [Scheme.residueFieldCongr]

theorem ext_of_base_eq_of_comp_eq_of_isIso_residueFieldMap
    {K O : Type u} [Field K] [CommRing O] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of O))
    (a b : Spec (CommRingCat.of K) ⟶ X)
    (hab : a.base (IsLocalRing.closedPoint K) = b.base (IsLocalRing.closedPoint K))
    (ht : a ≫ t = b ≫ t)
    [IsIso (t.residueFieldMap (a.base (IsLocalRing.closedPoint K)))] :
    a = b := by
  apply (Scheme.SpecToEquivOfField K X).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨hab, ?_⟩

  have hc : Scheme.SpecToEquivOfField K _ (a ≫ t) = Scheme.SpecToEquivOfField K _ (b ≫ t) := by rw [ht]
  rw [Scheme.SpecToEquivOfField_eq_iff] at hc
  obtain ⟨e₁, he₁⟩ := hc
  rw [snd_SpecToEquivOfField_comp a t, snd_SpecToEquivOfField_comp b t] at he₁

  have hnat := residueFieldCongr_hom_comp_residueFieldMap t hab
  have he₂ : t.residueFieldMap (a.base (IsLocalRing.closedPoint K)) ≫ (Scheme.SpecToEquivOfField K X a).2 =
      t.residueFieldMap (a.base (IsLocalRing.closedPoint K)) ≫ (X.residueFieldCongr hab).hom ≫ (Scheme.SpecToEquivOfField K X b).2 :=
    he₁.trans (by
      have := congrArg (fun φ => φ ≫ (Scheme.SpecToEquivOfField K X b).2) hnat
      first | simpa only [Category.assoc] using this | (simp only [Category.assoc] at this ⊢; exact this) | exact this)
  exact (cancel_epi (t.residueFieldMap (a.base (IsLocalRing.closedPoint K)))).mp he₂

end HART

set_option maxHeartbeats 3200000 in
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

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    ∀ (hsp : prA.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x₀),
    letI emb : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))
    ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rpd.R₁.integers →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → f ∈ W.toValuationSubring) →
      f ∈ emb.range := by
  intro hspA f hf₁ hfW
  classical

  obtain ⟨O', _iCR, _iDom, _iDVR, ρO', ιA', hinj, hloc, hιA'ρ, jO', hjO', hιA'j, htoκ', key1⟩ :=
    ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ uκ huκ₂ f
  obtain ⟨hsp', hx'cl, hrat, r₀, s₀, hs₀, hfrac⟩ := key1
  obtain ⟨ϖ', hϖ'⟩ := (IsDiscreteValuationRing.exists_irreducible O').imp
    fun ϖ hϖ => (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ

  obtain ⟨hnoeth, hdom, hic, hdim, hprime⟩ := ModularCurve.XHDRModelAtP.isIntegrallyClosed_stalk_and_ringKrullDim_eq_two_of_isIso_residueFieldMap_of_not_mem_range_comp p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O' ρO' ιA' hinj hloc hιA'ρ jO' hjO' hιA'j htoκ' ϖ' hϖ' uκ huκ₂ 1 hsmooth hrat

  obtain ⟨⟨hσloc, hembinj, hembσ⟩, hsec⟩ := ModularCurve.XHDRModelAtP.isLocalHom_and_injective_stalkRead_and_forall_section_evalAt_eq_of_point p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O' ρO' ιA' hinj hloc hιA'ρ jO' hjO' hιA'j htoκ' ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) hx'cl hsp'
  have hϖ0 : ϖ' ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field O'
    rw [hϖ', h0, Ideal.span_singleton_eq_bot]
  have hϖne : (((XO (ΓM M H) hj ρO').presheaf.germ ⊤ ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)) ϖ' ≠ 0 := by
    intro h0
    have h1 : ((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO']) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO').stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp').hom))) ((((XO (ΓM M H) hj ρO').presheaf.germ ⊤ ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)) ϖ') = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (jO' ϖ') :=
      RingHom.congr_fun hembσ ϖ'
    rw [h0, map_zero, eq_comm, map_eq_zero_iff _ (RingHom.injective _), ← hιA'j] at h1
    exact hϖ0 (hinj (by rw [map_zero]; exact Subtype.ext (by simpa using h1)))
  have key5 := ModularCurve.XHDRModelAtP.exists_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_point p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O' ρO' ιA' hinj hloc hιA'ρ jO' hjO' hιA'j htoκ' ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) hx'cl ϖ' hϖ'
  have key6 := ModularCurve.XHDRModelAtP.exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_one p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd hwgen O' ρO' ιA' hinj hloc hιA'ρ jO' hjO' hιA'j htoκ' ϖ' hϖ' uκ huκ₂ hsmooth hrat hsp'

  haveI := hnoeth; haveI := hdom; haveI := hic
  have hrange : f ∈ (((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO']) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO').stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp').hom)))).range := by
    refine IsIntegrallyClosed.mem_range_of_isPrime_span_of_forall_height_eq_one_of_notMem ((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO']) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO').stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp').hom))) hembinj ((((XO (ΓM M H) hj ρO').presheaf.germ ⊤ ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)) ϖ') hϖne hprime f (key6 f hf₁ ⟨r₀, s₀, hs₀, hfrac⟩) ?_
    intro P hP hht hϖ

    have hPne : P ≠ ⊥ := by
      rintro rfl; simp [Ideal.height_bot] at hht
    obtain ⟨W, hWrat, s', hs'₁, hs'₂, hx, hker⟩ := key5 P hP hPne hϖ
    have hstrict : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceFst α hα W = Psp.reduceFst α hα Q := by

      have hover : (s' ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO'))) ≫ toBase p (ΓM M H) hj =
          Spec.map (CommRingCat.ofHom ρ) := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hs'₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιA'ρ]
      let uW : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj) :=
        ⟨s' ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO')), hover⟩
      have huW : barPt A ≫ uW.1 = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
        show barPt A ≫ s' ≫ pullback.fst _ _ = _
        rw [← Category.assoc, hs'₂, Category.assoc, Category.assoc, pullback.lift_fst, Category.comp_id]
      have hab : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s').base (IsLocalRing.closedPoint (ResidueField ↥A)) =
          (uκ ≫ (bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ')).base (IsLocalRing.closedPoint (ResidueField ↥A)) := by
        have hcl : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)) =
            IsLocalRing.closedPoint ↥A := IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcl, hx]
      have htt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s') ≫ XO.toBase (ΓM M H) hj ρO' =
          (uκ ≫ (bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ')) ≫ XO.toBase (ΓM M H) hj ρO' := by
        rw [Category.assoc, Category.assoc, show XO.toBase (ΓM M H) hj ρO' = pullback.snd _ _ from rfl, hs'₁, bcMap_snd, ← Category.assoc uκ, huκ₂,
          Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      haveI : IsIso ((XO.toBase (ΓM M H) hj ρO').residueFieldMap
          ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s').base (IsLocalRing.closedPoint (ResidueField ↥A)))) := by
        rw [hab]; exact hrat
      have hpts : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s' = uκ ≫ (bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ') :=
        HART.ext_of_base_eq_of_comp_eq_of_isIso_residueFieldMap (XO.toBase (ΓM M H) hj ρO') _ _ hab htt
      have huκ₁' : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ uW.1 := by
        show uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s' ≫ pullback.fst _ _
        rw [← Category.assoc, hpts, Category.assoc, bcMap_fst]

      have hrd := hcompat 0 ((𝔛.Meta).pointEquivPlace.symm W) uW huW uκ huκ₁' huκ₂ P0 hP0
      have hrd' := hcompat' 0 ((𝔛.Meta).pointEquivPlace.symm W) uW huW uκ huκ₁' huκ₂ P0 hP0
      simp only [if_true, eq_self_iff_true, Equiv.apply_symm_apply] at hrd hrd'
      have hFW : Psp.reduceFst α hα W = Psp.reduceFst α hα Q := by rw [← hrd, hP0Q]
      refine ⟨⟨?_, ?_⟩, hFW⟩
      · rw [← hrd]; exact hrd'.symm
      · rw [hFW]; exact hQ.2
    have hfV : f ∈ W.toValuationSubring := hfW W hstrict.1 hstrict.2
    obtain ⟨hχloc, hχσ, hval⟩ := hsec W hWrat s' hs'₁ hs'₂ hx
    have hcentre : ∀ b : ↥((XO (ΓM M H) hj ρO').presheaf.stalk ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))))), b ∈ P ↔ ((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO']) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO').stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp').hom))) b ∈ W.toValuationSubring.nonunits := by
      intro b
      obtain ⟨hbV, hbval⟩ := hval b
      rw [hker b, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      constructor
      · intro h0
        refine ⟨hbV, ?_⟩
        rw [← IsLocalRing.residue_eq_zero_iff, ← W.algebraMap_evalAt hWrat hbV, hbval, h0]
        simp
      · rintro ⟨h', hm⟩
        rw [← IsLocalRing.residue_eq_zero_iff, ← W.algebraMap_evalAt hWrat h', hbval,
          map_eq_zero_iff _ (RingHom.injective _)] at hm
        exact_mod_cast hm
    have hPm : P ≠ IsLocalRing.maximalIdeal _ := by
      intro hPm
      apply hϖ
      rw [hPm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      haveI := hσloc
      intro hu
      have hu' := (isUnit_map_iff (((XO (ΓM M H) hj ρO').presheaf.germ ⊤ ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)) ϖ').mp hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (hϖ' ▸ Ideal.mem_span_singleton_self ϖ') hu'
    exact IsIntegrallyClosed.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringKrullDim_le_two (le_of_eq hdim) ((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO']) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO').stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp').hom))) hembinj W.toValuationSubring (fun b => (hval b).1) P hcentre hPm
      f hfV ⟨r₀, s₀, hs₀, hfrac⟩
  obtain ⟨b, hfb⟩ := hrange

  have hJ := HartogsAux.pullback_map_id_comp (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (Spec.map (CommRingCat.ofHom ρ))
      (Spec.map (CommRingCat.ofHom ρO')) (Spec.map (CommRingCat.ofHom A.subtype)) (Spec.map (CommRingCat.ofHom ιA'))
      (Spec.map (CommRingCat.ofHom jO')) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hιA'j])
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιA'ρ])
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
  have hbc := HartogsAux.bcMap_comp_pullback_map (ΓM M H) hj ρ ρO' ιA' (IsLocalRing.residue ↥A) rfl htoκ'
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιA'ρ])
  have hgx := HartogsAux.base_apply_of_comp_eq _ _ _ hbc (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
  obtain ⟨b₀, hb₀⟩ := HartogsAux.exists_stalkMap_stalkSpecializes_eq _ _ _ hJ (𝔛.eeta.base (genericPoint (𝔛.Meta).C))
    hspA hsp' hgx b
  refine ⟨b₀, ?_⟩
  rw [← hfb]
  exact congrArg (fun t => (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom t)) hb₀.symm

end S_ModularCurve_XHDRModelAtP_mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem (solution)
