-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/34f287b6-b3d4-53c8-8f34-b24f3fa4274f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_comp_eq_and_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective
import Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_orientedEtaleCrossingChart
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_read_chart_mul_eq_and_isUnit_germ_and_smul_eq_and_evalAt_eq_of_chart
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_through_crossing_iff_reduceFst_eq_and_not_isStrict_of_offDiag_of_surjective
import Theorems.Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_annulus_mem_dom_iff_and_param_eq_read_chart_and_modulus_eq_pow_of_chart_of_residue_surjective
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isUnit_and_read_eq_and_ord_placeOn_eq_zero_of_forall_ord_eq_zero_of_forall_isUnit_evalAt_of_chart_of_residue_surjective
import Theorems.Thm_ModularCurve_XHDRModelAtP_read_mem_integers_and_residue_eq_restrict_comp_of_mem
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim instTopologicallyFGOfFiniteType"
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

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve~nodeEquiv ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial"

open scoped MatrixGroups

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
    ∃ (e : ↥SS → ℕ), (∀ s, 0 < e s) ∧
    ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by
  classical

  obtain ⟨ιA, ρO, hιval, hιρ, hιinj, hDVR, hϖ, hmax, hsurj, hfix⟩ :=
    ValuationSubring.exists_ringHom_comap_fixedField_inertiaSubgroupIn_comp_eq_and_isDiscreteValuationRing p A hA ρ hρ
  haveI := hDVR

  have htoκ : ((IsLocalRing.residue ↥A).comp ιA).comp ρO = (IsLocalRing.residue ↥A).comp ρ := by
    rw [RingHom.comp_assoc, hιρ]
  have hjO : (A.subtype.comp ιA).comp ρO = algebraMap (R p) (AlgebraicClosure ℚ) := by
    rw [RingHom.comp_assoc, hιρ, hρ]
  have hsurjκ : Function.Surjective ((IsLocalRing.residue ↥A).comp ιA) := hsurj

  have hrat := ModularCurve.XHDRModelAtP.forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ _ ρO ((IsLocalRing.residue ↥A).comp ιA) htoκ hsurjκ

  have hD1 := ModularCurve.XHDRModelAtP.forall_exists_orientedEtaleCrossingChart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ _ ρO hϖ
    ((IsLocalRing.residue ↥A).comp ιA) htoκ (bcMap (ΓM M H) hj ρO ((IsLocalRing.residue ↥A).comp ιA) htoκ)
    (bcMap_fst (ΓM M H) hj ρO _ htoκ) (bcMap_snd (ΓM M H) hj ρO _ htoκ) hrat
  choose eN heN U hxU f hch using hD1

  have hnode : ∀ s : ↥SS, ∃ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      (𝔛.placeOn0 A hA ρ hρ n, 𝔛.placeOn1 A hA ρ hρ n) =
        (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
    intro s
    have hs : (s : _ × _) ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p := (hSS s).1 s.2
    rw [mem_ssNodePairsQExp_iff] at hs
    refine ⟨(𝔛.nodeEquiv A hA ρ hρ).symm ⟨_, hs.1⟩, ?_⟩
    simp only [XHDRModelAtP.placeOn0, XHDRModelAtP.placeOn1, Equiv.apply_symm_apply]
    exact Prod.ext hs.2.symm rfl
  choose nOf hnOf using hnode
  refine ⟨fun s => eN (nOf s), fun s => heN (nOf s), fun s => ?_⟩

  have hn := hnOf s
  beta_reduce
  generalize nOf s = n at hn ⊢
  obtain ⟨⟨s₁, s₂⟩, hsS⟩ := s
  simp only [Prod.mk.injEq] at hn
  obtain ⟨rfl, rfl⟩ := hn

  obtain ⟨hgen, An, hdom, hparam, hmod, hiv1, hiv0⟩ :=
    ModularCurve.XHDRModelAtP.exists_annulus_mem_dom_iff_and_param_eq_read_chart_and_modulus_eq_pow_of_chart_of_residue_surjective p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ _ ρO hϖ
    ((IsLocalRing.residue ↥A).comp ιA) htoκ hsurjκ (A.subtype.comp ιA) hjO ιA rfl rfl
    n (eN n) (heN n) (U n) (hxU n) (f n)
    (hch n).1 (hch n).2.1 (hch n).2.2.1 (hch n).2.2.2.1
    (hch n).2.2.2.2.1 (hch n).2.2.2.2.2.1 (hch n).2.2.2.2.2.2.1 (hch n).2.2.2.2.2.2.2
  have hmodQ : ((An.modulus : ↥A) : AlgebraicClosure ℚ) = ((p : ℕ) : AlgebraicClosure ℚ) ^ (eN n) := by
    simp [hmod]

  have hCR := ModularCurve.XHDRModelAtP.exists_read_chart_mul_eq_and_isUnit_germ_and_smul_eq_and_evalAt_eq_of_chart
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ _ ρO hϖ ((IsLocalRing.residue ↥A).comp ιA) htoκ (A.subtype.comp ιA) hjO ιA rfl rfl
    n (eN n) (heN n) (U n) (hxU n) (f n)
    (hch n).1 (hch n).2.1 (hch n).2.2.1 (hch n).2.2.2.1
    (hch n).2.2.2.2.1 (hch n).2.2.2.2.2.1 (hch n).2.2.2.2.2.2.1 (hch n).2.2.2.2.2.2.2
  obtain ⟨hgen', hzz', ⟨hξ0, hξi, hgv0, hgvi, hgui, hgu0⟩, h3, h4⟩ := hCR

  have hE := ModularCurve.XHDRModelAtP.read_mem_integers_and_residue_eq_restrict_comp_of_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ _ ρO ((IsLocalRing.residue ↥A).comp ιA) htoκ (A.subtype.comp ιA) hjO ιA rfl rfl
    θ Psp Rpd hwgen

  obtain ⟨gv, hgv0n, hgvE⟩ : ∃ g, IsUnit ((XO (ΓM M H) hj ρO).presheaf.germ _ _ hξ0 g) ∧ g = _ := ⟨_, hgv0, rfl⟩
  obtain ⟨gu, hguin, hguE⟩ : ∃ g, IsUnit ((XO (ΓM M H) hj ρO).presheaf.germ _ _ hξi g) ∧ g = _ := ⟨_, hgui, rfl⟩
  have hEv := (hE ((U n).ι ''ᵁ ⊤) hgen' gv).2 hξ0
  have hEu := (hE ((U n).ι ''ᵁ ⊤) hgen' gu).1 hξi
  subst hgvE hguE
  obtain ⟨hv₂, ⟨hg₁, hresv⟩, hv₂ne⟩ := hEv
  obtain ⟨hu₁, ⟨hg₀, hresu⟩, hu₁ne⟩ := hEu

  have hp0 : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((((p : ℕ) : AlgebraicClosure ℚ)) ^ eN n) ≠ 0 :=
    (map_ne_zero _).2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
  obtain ⟨zu, hzuE, hzz⟩ : ∃ zu : ↥(xHFunctionFieldBar M H), zu = _ ∧
      An.param * zu = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((((p : ℕ) : AlgebraicClosure ℚ)) ^ eN n) :=
    ⟨_, rfl, by rw [hparam]; exact hzz'⟩
  have hzne : An.param ≠ 0 := fun h => hp0 (by rw [← hzz, h, zero_mul])
  have hzune : zu ≠ 0 := fun h => hp0 (by rw [← hzz, h, mul_zero])
  have hπz : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ = zu := by
    rw [hmodQ, ← hzz, mul_comm An.param, mul_inv_cancel_right₀ hzne]
  have hπz' : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ)⁻¹ * An.param = zu⁻¹ := by
    rw [← hπz, mul_inv, inv_inv, map_inv₀]

  have hzu₁ : ∃ h₁ : zu ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨zu, h₁⟩ ≠ 0 ∧ (𝔛.placeOn0 A hA ρ hρ n).ord (Rpd.R₁.residue ⟨zu, h₁⟩) = 1 := by
    subst hzuE
    obtain ⟨hg₀', h0⟩ := hiv0
    exact ⟨hu₁, hu₁ne hguin, (congrArg (𝔛.placeOn0 A hA ρ hρ n).ord hresu).trans h0⟩

  have hUG := ModularCurve.XHDRModelAtP.exists_isUnit_and_read_eq_and_ord_placeOn_eq_zero_of_forall_ord_eq_zero_of_forall_isUnit_evalAt_of_chart_of_residue_surjective p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ _ ρO hϖ
    ((IsLocalRing.residue ↥A).comp ιA) htoκ hsurjκ (A.subtype.comp ιA) hjO ιA rfl rfl
    n (eN n) (heN n) (U n) (hxU n) (f n)
    (hch n).1 (hch n).2.1 (hch n).2.2.1 (hch n).2.2.2.1
    (hch n).2.2.2.2.1 (hch n).2.2.2.2.2.1 (hch n).2.2.2.2.2.2.1 (hch n).2.2.2.2.2.2.2

  have hEA := ModularCurve.XHDRModelAtP.read_mem_integers_and_residue_eq_restrict_comp_of_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ ↥A ρ (IsLocalRing.residue ↥A) rfl A.subtype hρ (RingHom.id ↥A)
    (RingHom.comp_id _) (RingHom.comp_id _) θ Psp Rpd hwgen

  have hnA : (pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 1 ≫
        bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base n =
      (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫
        bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base n := by
    rw [← Category.assoc, ← Category.assoc, pullback.condition]
  have hξ0A : 𝔛.ξzero A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ⤳
      (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫
        bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base n := by
    rw [← hnA, Scheme.Hom.comp_base, TopCat.comp_app]
    exact ((𝔛.efib_genericPoint_specializes A hA ρ hρ ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)).map
      (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).continuous)
  have hξiA : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ⤳
      (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫
        bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base n := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app]
    exact ((𝔛.efib_genericPoint_specializes A hA ρ hρ ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)).map
      (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).continuous)

  have hATT := ModularCurve.JHPlaceSpecialization.ProlongationDatum.annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers p M H hpM A SS θ Psp Rpd ⟨(𝔛.placeOn0 A hA ρ hρ n, 𝔛.placeOn1 A hA ρ hρ n), hsS⟩ An
    (by

      rw [hparam]
      obtain ⟨hg₁', h1⟩ := hiv1
      exact ⟨hv₂, (congrArg (𝔛.placeOn1 A hA ρ hρ n).ord hresv).trans h1⟩)
    (by

      rw [hπz]
      exact ⟨hzu₁.choose, hzu₁.choose_spec.2⟩)
    (by

      intro g hg0 hord hunit
      obtain ⟨U', hxA, hgenA, γ, hγu, hγg, ⟨hg1, hne1, hord1⟩, -⟩ := hUG g (fun W hW sct h1 h2 h3 =>
        have hm := (hdom W).2 ⟨hW, sct, h1, h2, h3⟩
        ⟨hord W hm, hunit W hm⟩)
      subst hγg
      obtain ⟨h₂, ⟨hg₁'', hres⟩, hne⟩ := (hEA U' hgenA γ).2 (hξ0A.mem_open U'.2 hxA)
      exact ⟨h₂, hne (hγu.map ((XO (ΓM M H) hj ρ).presheaf.germ U' _ (hξ0A.mem_open U'.2 hxA)).hom),
        (congrArg (𝔛.placeOn1 A hA ρ hρ n).ord hres).trans hord1⟩)
    (by

      intro g hg0 hord hunit
      obtain ⟨U', hxA, hgenA, γ, hγu, hγg, -, ⟨hg0', hne0, hord0⟩⟩ := hUG g (fun W hW sct h1 h2 h3 =>
        have hm := (hdom W).2 ⟨hW, sct, h1, h2, h3⟩
        ⟨hord W hm, hunit W hm⟩)
      subst hγg
      obtain ⟨h₁, ⟨hg₀'', hres⟩, hne⟩ := (hEA U' hgenA γ).1 (hξiA.mem_open U'.2 hxA)
      exact ⟨h₁, hne (hγu.map ((XO (ΓM M H) hj ρ).presheaf.germ U' _ (hξiA.mem_open U'.2 hxA)).hom),
        (congrArg (𝔛.placeOn0 A hA ρ hρ n).ord hres).trans hord0⟩)
  refine ⟨An, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·

    intro W
    have hdd := ModularCurve.XHDRModelAtP.exists_section_through_crossing_iff_reduceFst_eq_and_not_isStrict_of_offDiag_of_surjective
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' _ ρO hϖ
      ((IsLocalRing.residue ↥A).comp ιA) htoκ (A.subtype.comp ιA) hjO ιA rfl rfl hsurjκ n (U n) (hxU n) ⟨(𝔛.placeOn0 A hA ρ hρ n, 𝔛.placeOn1 A hA ρ hρ n), hsS⟩ rfl W
    rw [hdom W, ← hdd]

    have hWrat : W.IsRational := by
      simpa only [Equiv.apply_symm_apply] using
        AlgebraicCurve.CurveModel.isRational_pointEquivPlace (𝔛.Meta) ((𝔛.Meta).pointEquivPlace.symm W)
    exact ⟨fun h => h.2, fun h => ⟨hWrat, h⟩⟩
  ·
    exact ⟨1, isUnit_one, by rw [hmod, map_pow, map_natCast, mul_one]⟩
  ·
    intro σ hσ
    rw [hparam]
    refine (h3 σ hσ ?_).1

    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hσ
    intro o
    exact congrArg Subtype.val (hfix τ hτ o)
  ·
    rw [hπz']
    obtain ⟨h₁, hne, -⟩ := hzu₁
    have hv1 : Rpd.R₁.integers.valuation zu = 1 :=
      (ValuationSubring.valuation_eq_one_iff _ ⟨zu, h₁⟩).1 (Rpd.R₁.isUnit_of_residue_ne_zero hne)
    exact ValuationSubring.mem_of_valuation_le_one _ _ (le_of_eq (by rw [map_inv₀, hv1, inv_one]))
  ·
    rw [hparam]
    exact ⟨hv₂, hv₂ne hgv0n⟩
  ·
    exact hATT.1
  ·
    exact hATT.2

end S_ModularCurve_XHDRModelAtP_exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag (solution)
