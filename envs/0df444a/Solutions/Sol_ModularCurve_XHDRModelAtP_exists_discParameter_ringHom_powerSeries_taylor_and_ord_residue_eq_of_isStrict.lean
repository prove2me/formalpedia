-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2007d255-05ca-5a10-8729-97943ab6c826

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_stalk_read_of_mem_integers_of_forall_isStrictSnd_mem
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_comp_zero_placeOfPoint_eq_reduceFst_of_isStrictFst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod MvPolynomial.CrossingQuotient.Resolution.instIsAffineXSchemeOpenCover MvPolynomial.CrossingQuotient.isOpenImmersion_overlapToChartRight MvPolynomial.CrossingQuotient.isOpenImmersion_torusToOverlap MvPolynomial.CrossingQuotient.isLocallyDirected_glueDiagram MvPolynomial.CrossingQuotient.GlueIndex.instPreorder MvPolynomial.CrossingQuotient.isOpenImmersion_torusToChart MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιTorus MvPolynomial.CrossingQuotient.isOpenImmersion_glueMap MvPolynomial.CrossingQuotient.GlueIndex.instLE MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιOverlap MvPolynomial.CrossingQuotient.isLocalization_away_torusRing MvPolynomial.CrossingQuotient.isOpenImmersion_glueDiagram_map MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ι AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup"
p2m_attr_erase "instance" "KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ MvPolynomial.CrossingQuotient.GlueIndex.chart_le_overlap MvPolynomial.CrossingQuotient.GlueIndex.torus.sizeOf_spec MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_torus MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.ι_toSpec MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing_assoc MvPolynomial.CrossingQuotient.glueMap_torus_overlap MvPolynomial.CrossingQuotient.GlueIndex.chart_le_torus MvPolynomial.CrossingQuotient.glueMap_overlap_overlap"
p2m_attr_erase "simp" "MvPolynomial.CrossingQuotient.GlueIndex.torus_le MvPolynomial.CrossingQuotient.Resolution.openCover_f MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing MvPolynomial.CrossingQuotient.glueMap_torus_chart MvPolynomial.CrossingQuotient.glueMap_torus_torus MvPolynomial.CrossingQuotient.glueDiagram_obj MvPolynomial.CrossingQuotient.GlueIndex.chart.injEq MvPolynomial.CrossingQuotient.GlueIndex.chart_le_chart MvPolynomial.CrossingQuotient.GlueIndex.chart.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.openCover_X MvPolynomial.CrossingQuotient.Resolution.openCover_I₀ MvPolynomial.CrossingQuotient.GlueIndex.overlap.injEq MvPolynomial.CrossingQuotient.glueMap_chart_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_overlap MvPolynomial.CrossingQuotient.Resolution.ι_toSpec_assoc MvPolynomial.CrossingQuotient.lift_V MvPolynomial.CrossingQuotient.lift_U MvPolynomial.CrossingQuotient.monomial_neg_natCast MvPolynomial.CrossingQuotient.monomial_zero MvPolynomial.CrossingQuotient.monomial_natCast MvPolynomial.CrossingQuotient.powMap_mk_X RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

theorem HSP_Fst
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
    prA.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x₀ := by

  let ut : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρ := pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp])
  have hut₁ : ut ≫ pullback.fst _ _ = u.1 := pullback.lift_fst _ _ _
  have hut₂ : ut ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

  have hκ : uκ ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ ut := by
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, huκ₁, Category.assoc, hut₁]
    · rw [Category.assoc, bcMap_snd, ← Category.assoc, huκ₂, Category.id_comp, Category.assoc, hut₂, Category.comp_id]
  have hx₀ : (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) =
      ut.base (IsLocalRing.closedPoint ↥A) := by
    rw [← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply]
    congr 1
    haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue ↥A)).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue ↥A))
    exact AlgebraicGeometry.Spec_closedPoint

  have hgen : ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) =
      barPt A ≫ ut := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, Category.comp_id, Category.assoc, hut₁, hu]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc,
        ((𝔛.Meta).pointEquivPlace.symm Q).2, Category.id_comp, Category.assoc, hut₂, Category.comp_id]

  have h2 : (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        _ ⟶ XO (ΓM M H) hj ρ).base
      (𝔛.eeta.base (((𝔛.Meta).pointEquivPlace.symm Q).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))) =
      ut.base ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgen]
  have hsp1 : genericPoint (𝔛.Meta).C ⤳ ((𝔛.Meta).pointEquivPlace.symm Q).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) :=
    genericPoint_specializes _
  have hsp2 := (hsp1.map 𝔛.eeta.base.hom.continuous).map
    (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        _ ⟶ XO (ΓM M H) hj ρ).base.hom.continuous
  rw [h2] at hsp2
  have hsp3 : (barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ IsLocalRing.closedPoint ↥A :=
    IsLocalRing.specializes_closedPoint _
  have hsp4 := hsp3.map ut.base.hom.continuous
  rw [← hx₀] at hsp4
  exact hsp2.trans hsp4

theorem HSP_Snd
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

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    prA.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x₀ := by

  let ut : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρ := pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp])
  have hut₁ : ut ≫ pullback.fst _ _ = u.1 := pullback.lift_fst _ _ _
  have hut₂ : ut ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

  have hκ : uκ ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ ut := by
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, huκ₁, Category.assoc, hut₁]
    · rw [Category.assoc, bcMap_snd, ← Category.assoc, huκ₂, Category.id_comp, Category.assoc, hut₂, Category.comp_id]
  have hx₀ : (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) =
      ut.base (IsLocalRing.closedPoint ↥A) := by
    rw [← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply]
    congr 1
    haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue ↥A)).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue ↥A))
    exact AlgebraicGeometry.Spec_closedPoint

  have hgen : ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) =
      barPt A ≫ ut := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, Category.comp_id, Category.assoc, hut₁, hu]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc,
        ((𝔛.Meta).pointEquivPlace.symm Q).2, Category.id_comp, Category.assoc, hut₂, Category.comp_id]

  have h2 : (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        _ ⟶ XO (ΓM M H) hj ρ).base
      (𝔛.eeta.base (((𝔛.Meta).pointEquivPlace.symm Q).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))) =
      ut.base ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgen]
  have hsp1 : genericPoint (𝔛.Meta).C ⤳ ((𝔛.Meta).pointEquivPlace.symm Q).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) :=
    genericPoint_specializes _
  have hsp2 := (hsp1.map 𝔛.eeta.base.hom.continuous).map
    (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        _ ⟶ XO (ΓM M H) hj ρ).base.hom.continuous
  rw [h2] at hsp2
  have hsp3 : (barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ IsLocalRing.closedPoint ↥A :=
    IsLocalRing.specializes_closedPoint _
  have hsp4 := hsp3.map ut.base.hom.continuous
  rw [← hx₀] at hsp4
  exact hsp2.trans hsp4

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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    (∀ (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q →
      JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →

      letI B : Subring ↥(xHFunctionFieldBar M H) :=
        Rpd.R₁.integers.toSubring ⊓
          ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) // Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceFst α hα W = Psp.reduceFst α hα Q}, W.1.toValuationSubring.toSubring
      ∃ (t : ↥(xHFunctionFieldBar M H)) (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ↥A) (Φ : ↥B →+* PowerSeries ↥A),

        t ∈ Rpd.R₁.integers ∧
        (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q →
          c W ∈ maximalIdeal ↥A ∧ W.ord (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c W : AlgebraicClosure ℚ)) = 1) ∧
        (∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα Q →
          c W = c W' → W = W') ∧

        (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ B), Φ ⟨_, hx⟩ = PowerSeries.C x) ∧
        (∀ ht : t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ B, Φ ⟨_, ht⟩ = PowerSeries.X) ∧

        (∀ (f : ↥B) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (f : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Φ f) : ↥A) : AlgebraicClosure ℚ) *
              (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) ∧

        (∀ (f : ↥B) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Φ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A →
          Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 ∧
            (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧

        (∀ (f : ↥B) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A)) ∧
    (∀ (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q →
      JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →

      letI B : Subring ↥(xHFunctionFieldBar M H) :=
        Rpd.R₂.integers.toSubring ⊓
          ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) // Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q}, W.1.toValuationSubring.toSubring
      ∃ (t : ↥(xHFunctionFieldBar M H)) (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ↥A) (Φ : ↥B →+* PowerSeries ↥A),

        t ∈ Rpd.R₂.integers ∧
        (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q →
          c W ∈ maximalIdeal ↥A ∧ W.ord (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c W : AlgebraicClosure ℚ)) = 1) ∧
        (∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W' → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q →
          c W = c W' → W = W') ∧

        (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ B), Φ ⟨_, hx⟩ = PowerSeries.C x) ∧
        (∀ ht : t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ B, Φ ⟨_, ht⟩ = PowerSeries.X) ∧

        (∀ (f : ↥B) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (f : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Φ f) : ↥A) : AlgebraicClosure ℚ) *
              (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) ∧

        (∀ (f : ↥B) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Φ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A →
          Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 ∧
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧

        (∀ (f : ↥B) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A)) := by
  refine ⟨?_, ?_⟩
  · intro Q hQ hv
    obtain ⟨u, uκ, P0, hu, huκ₁, huκ₂, hP0, hP0Q, hsm⟩ := ModularCurve.XHDRModelAtP.exists_section_comp_zero_placeOfPoint_eq_reduceFst_of_isStrictFst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ
    have keyE := ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsm
    have keyH := ModularCurve.XHDRModelAtP.mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsm

    have hsp := HSP_Fst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsm
    obtain ⟨t, c, Φ, ht, hc, hinj, hΦC, hΦX, hT, hR, hR'⟩ := keyE hsp
    have hH := keyH hsp
    obtain ⟨Bst, hBst, Ψ, hΨC, hΨX, hΨT, hΨR, hΨR'⟩ :
        ∃ (Bst : Subring ↥(xHFunctionFieldBar M H)) (_ : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rpd.R₁.integers →
            (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → f ∈ W.toValuationSubring) → f ∈ Bst)
          (Ψ : ↥Bst →+* PowerSeries ↥A),
        (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ Bst), Ψ ⟨_, hx⟩ = PowerSeries.C x) ∧
        (∀ ht : t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ Bst, Ψ ⟨_, ht⟩ = PowerSeries.X) ∧
        (∀ (f : ↥Bst) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (f : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Ψ f) : ↥A) : AlgebraicClosure ℚ) *
              (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) ∧
        (∀ (f : ↥Bst) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Ψ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Ψ f) ∉ maximalIdeal ↥A →
          Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 ∧
            (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧
        (∀ (f : ↥Bst) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Ψ f) ∉ maximalIdeal ↥A) :=
      ⟨_, hH, Φ, hΦC, hΦX, hT, hR, hR'⟩
    have hle : (Rpd.R₁.integers.toSubring ⊓ ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) // Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceFst α hα W = Psp.reduceFst α hα Q}, W.1.toValuationSubring.toSubring) ≤ Bst := by
      intro f hf
      exact hBst f (Subring.mem_inf.mp hf).1
        (fun W hW hred => Subring.mem_iInf.mp (Subring.mem_inf.mp hf).2 ⟨W, hW, hred⟩)
    refine ⟨t, c, Ψ.comp (Subring.inclusion hle), ht, hc, hinj, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; exact hΨC x (hle hx)
    · intro hx; exact hΨX (hle hx)
    · intro f k; exact hΨT (Subring.inclusion hle f) k
    · intro f hf k h1 h2; exact hΨR (Subring.inclusion hle f) hf k h1 h2
    · intro f hf h0; exact hΨR' (Subring.inclusion hle f) hf h0
  · intro Q hQ hv
    obtain ⟨u, uκ, P0, hu, huκ₁, huκ₂, hP0, hP0Q, hsm⟩ := ModularCurve.XHDRModelAtP.exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ
    have keyE := ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsm
    have keyH := ModularCurve.XHDRModelAtP.mem_range_stalk_read_of_mem_integers_of_forall_isStrictSnd_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsm

    have hsp := HSP_Snd p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsm
    obtain ⟨t, c, Φ, ht, hc, hinj, hΦC, hΦX, hT, hR, hR'⟩ := keyE hsp
    have hH := keyH hsp
    obtain ⟨Bst, hBst, Ψ, hΨC, hΨX, hΨT, hΨR, hΨR'⟩ :
        ∃ (Bst : Subring ↥(xHFunctionFieldBar M H)) (_ : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rpd.R₂.integers →
            (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → f ∈ W.toValuationSubring) → f ∈ Bst)
          (Ψ : ↥Bst →+* PowerSeries ↥A),
        (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ Bst), Ψ ⟨_, hx⟩ = PowerSeries.C x) ∧
        (∀ ht : t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ Bst, Ψ ⟨_, ht⟩ = PowerSeries.X) ∧
        (∀ (f : ↥Bst) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (f : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Ψ f) : ↥A) : AlgebraicClosure ℚ) *
              (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) ∧
        (∀ (f : ↥Bst) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Ψ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Ψ f) ∉ maximalIdeal ↥A →
          Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 ∧
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧
        (∀ (f : ↥Bst) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Ψ f) ∉ maximalIdeal ↥A) :=
      ⟨_, hH, Φ, hΦC, hΦX, hT, hR, hR'⟩
    have hle : (Rpd.R₂.integers.toSubring ⊓ ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) // Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q}, W.1.toValuationSubring.toSubring) ≤ Bst := by
      intro f hf
      exact hBst f (Subring.mem_inf.mp hf).1
        (fun W hW hred => Subring.mem_iInf.mp (Subring.mem_inf.mp hf).2 ⟨W, hW, hred⟩)
    refine ⟨t, c, Ψ.comp (Subring.inclusion hle), ht, hc, hinj, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; exact hΨC x (hle hx)
    · intro hx; exact hΨX (hle hx)
    · intro f k; exact hΨT (Subring.inclusion hle f) k
    · intro f hf k h1 h2; exact hΨR (Subring.inclusion hle f) hf k h1 h2
    · intro f hf h0; exact hΨR' (Subring.inclusion hle f) hf h0

end S_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict (solution)
