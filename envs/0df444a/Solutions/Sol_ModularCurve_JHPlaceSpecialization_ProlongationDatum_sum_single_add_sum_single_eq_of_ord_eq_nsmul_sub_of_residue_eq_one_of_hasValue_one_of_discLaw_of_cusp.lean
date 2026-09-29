-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ad2ba843-c071-5b84-85e8-b01631679299

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_fixed_of_mem_ssPlacesQExp
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

namespace Ws25
namespace RigB
section PlaceHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap' {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hc' : algebraMap K F c ≠ 0 := (_root_.map_ne_zero (algebraMap K F)).mpr hc
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ hc'),
      Subtype.ext (by simpa using inv_mul_cancel₀ hc')⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem ord_algebraMap_mul {c : K} (hc : c ≠ 0) (x : F) :
    v.ord (algebraMap K F c * x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [v.ord_mul ((_root_.map_ne_zero _).mpr hc) hx, ord_algebraMap' v hc, zero_add]

theorem ord_smul {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  rw [Algebra.smul_def]; exact ord_algebraMap_mul v hc x

theorem ord_neg (x : F) : v.ord (-x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : (-x) = algebraMap K F (-1) * x := by simp
    rw [h, ord_algebraMap_mul v (by norm_num) x]

theorem min_ord_le_ord_add {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (v.ord x) (v.ord y) ≤ v.ord (x + y) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπF : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  set m := min (v.ord x) (v.ord y) with hm
  have hmem : ∀ z : F, z ≠ 0 → m ≤ v.ord z → z * (π : F) ^ (-m) ∈ v.toValuationSubring := by
    intro z hz hmz
    rw [v.mem_iff_ord_nonneg (mul_ne_zero hz (zpow_ne_zero _ hπF)), v.ord_mul hz (zpow_ne_zero _ hπF),
      v.ord_zpow, v.ord_coe_irreducible hπ, mul_one]
    omega
  have hsum : (x + y) * (π : F) ^ (-m) ∈ v.toValuationSubring := by
    rw [add_mul]; exact add_mem (hmem x hx (min_le_left _ _)) (hmem y hy (min_le_right _ _))
  have h := v.ord_nonneg_of_mem hsum
  rw [v.ord_mul hxy (zpow_ne_zero _ hπF), v.ord_zpow, v.ord_coe_irreducible hπ, mul_one] at h
  omega

theorem ord_add_eq_of_lt {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hlt : v.ord x < v.ord y) :
    v.ord (x + y) = v.ord x := by
  have hxy : x + y ≠ 0 := by
    intro h
    have : x = -y := eq_neg_of_add_eq_zero_left h
    rw [this, ord_neg] at hlt; exact lt_irrefl _ hlt
  have h1 := min_ord_le_ord_add v hx hy hxy
  have h2 := min_ord_le_ord_add v hxy (neg_ne_zero.mpr hy) (by simpa using hx)
  rw [ord_neg, add_neg_cancel_right] at h2
  omega

theorem mem_of_ord_nonneg' {x : F} (h : 0 ≤ v.ord x) : x ∈ v.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  · exact v.mem_of_ord_nonneg hx h

theorem ord_nonneg_of_ord_add_algebraMap_nonneg {x : F} (c : K)
    (h : 0 ≤ v.ord (algebraMap K F c + x)) : 0 ≤ v.ord x := by
  have hmem := mem_of_ord_nonneg' v h
  have : x = (algebraMap K F c + x) - algebraMap K F c := by ring
  rw [this]
  exact v.ord_nonneg_of_mem (sub_mem hmem (v.algebraMap_mem' c))

theorem HasValue.add {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem HasValue.smul {g : F} {a : K} (h : v.HasValue g a) (c : K) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]; exact (v.hasValue_algebraMap c).mul h

theorem hasValue_zero : v.HasValue (0 : F) 0 := by
  simpa using v.hasValue_algebraMap (0 : K)

theorem eq_of_hasValue_algebraMap {c a : K} (h : v.HasValue (algebraMap K F c) a) : a = c :=
  h.unique (v.hasValue_algebraMap c)

theorem ord_nonneg_of_hasValue {g : F} {a : K} (h : v.HasValue g a) : 0 ≤ v.ord g :=
  v.ord_nonneg_of_mem h.mem

theorem ord_sub_pos_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (hne : g - algebraMap K F a ≠ 0) :
    0 < v.ord (g - algebraMap K F a) := by
  obtain ⟨hg, hres⟩ := h
  have hmem : g - algebraMap K F a ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' a)
  have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring)
        = ⟨g, hg⟩ - ⟨algebraMap K F a, v.algebraMap_mem' a⟩ := rfl
    rw [this, map_sub, hres, sub_eq_zero]
    rfl
  have h0 := v.ord_nonneg_of_mem hmem
  rcases h0.lt_or_eq with hpos | h0
  · exact hpos
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hne hπ
    rw [← h0, zpow_zero, mul_one] at hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hmax
    have : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this]; exact Units.isUnit u

theorem ord_pos_of_hasValue_zero {g : F} (h : v.HasValue g 0) (hne : g ≠ 0) : 0 < v.ord g := by
  have := ord_sub_pos_of_hasValue v h (by simpa using hne)
  simpa using this

theorem mapDomain_apply_nonneg {ι κ : Type*} (f : ι → κ) (D : ι →₀ ℤ) (v : κ)
    (h : ∀ i, f i = v → 0 ≤ D i) : 0 ≤ Finsupp.mapDomain f D v := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [Finsupp.single_apply]
  split_ifs with hi
  · exact h i hi
  · exact le_rfl

theorem mapDomain_apply_eq_zero {ι κ : Type*} (f : ι → κ) (D : ι →₀ ℤ) (v : κ)
    (h : ∀ i, f i = v → D i = 0) : Finsupp.mapDomain f D v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Finsupp.single_apply]
  split_ifs with hi
  · exact h i hi
  · rfl

theorem inv_mem_of_isUnit {S : ValuationSubring F} {x : F} (hx : x ∈ S) (hu : IsUnit (⟨x, hx⟩ : S)) :
    x⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : F) = x := by rw [hu]
  have h1 : x * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  have : (((u⁻¹ : Sˣ) : S) : F) = x⁻¹ := (eq_inv_of_mul_eq_one_right h1)
  rw [← this]; exact SetLike.coe_mem _

theorem le_ord_sub_algebraMap {x : F} (c : K) {m : ℤ} (hm : m ≤ 0) (hx : m ≤ v.ord x)
    (hne : x - algebraMap K F c ≠ 0) : m ≤ v.ord (x - algebraMap K F c) := by
  by_cases hc : c = 0
  · simpa [hc] using hx
  by_cases hx0 : x = 0
  · rw [hx0, zero_sub, ord_neg, ord_algebraMap' v hc]; exact hm
  have hy : -algebraMap K F c ≠ 0 := neg_ne_zero.mpr ((_root_.map_ne_zero _).mpr hc)
  have hxy : x + -algebraMap K F c ≠ 0 := by rwa [← sub_eq_add_neg]
  have h := min_ord_le_ord_add v hx0 hy hxy
  rw [← sub_eq_add_neg, ord_neg, ord_algebraMap' v hc] at h
  exact le_trans (le_min hx hm) h

end PlaceHelpers

section TupleH

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

local notation "QQ" => AlgebraicClosure ℚ
local notation "κ" => ResidueField ↥A
local notation "FM" => ↥(xHFunctionFieldBar M H)
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
local notation "Fr" => qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p

variable {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
  {Psp : JHPlaceSpecialization p M H hpM A} (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

private theorem _root_.Ws25.RigB.isUnit_of_residue_ne_zero {a : ↥A} (h : IsLocalRing.residue ↥A a ≠ 0) : IsUnit a :=
  (IsLocalRing.residue_ne_zero_iff_isUnit a).mp h

p2m_export "Ws25.RigB" "isUnit_of_residue_ne_zero"
theorem cst_mem₁ (a : ↥A) : algebraMap QQ FM (a : QQ) ∈ Rpd.R₁.integers := (Rpd.R₁.algebraMap_mem_iff _).mpr a.2
theorem cst_mem₂ (a : ↥A) : algebraMap QQ FM (a : QQ) ∈ Rpd.R₂.integers := (Rpd.R₂.algebraMap_mem_iff _).mpr a.2

theorem smul_mem₁ {f : FM} (hf : f ∈ Rpd.R₁.integers) (a : ↥A) : (a : QQ) • f ∈ Rpd.R₁.integers := by
  rw [Algebra.smul_def]; exact mul_mem (cst_mem₁ Rpd a) hf
theorem smul_mem₂ {f : FM} (hf : f ∈ Rpd.R₂.integers) (a : ↥A) : (a : QQ) • f ∈ Rpd.R₂.integers := by
  rw [Algebra.smul_def]; exact mul_mem (cst_mem₂ Rpd a) hf

theorem residue₁_cst (a : ↥A) :
    Rpd.R₁.residue ⟨algebraMap QQ FM (a : QQ), cst_mem₁ Rpd a⟩ = algebraMap κ Fb (IsLocalRing.residue ↥A a) :=
  Rpd.R₁.residue_algebraMap a
theorem residue₂_cst (a : ↥A) :
    Rpd.R₂.residue ⟨algebraMap QQ FM (a : QQ), cst_mem₂ Rpd a⟩ = algebraMap κ Fb (IsLocalRing.residue ↥A a) :=
  Rpd.R₂.residue_algebraMap a

theorem residue₁_smul (a : ↥A) {f : FM} (hf : f ∈ Rpd.R₁.integers) :
    Rpd.R₁.residue ⟨(a : QQ) • f, smul_mem₁ Rpd hf a⟩ = IsLocalRing.residue ↥A a • Rpd.R₁.residue ⟨f, hf⟩ := by
  have : (⟨(a : QQ) • f, smul_mem₁ Rpd hf a⟩ : Rpd.R₁.integers) = ⟨algebraMap QQ FM (a : QQ), cst_mem₁ Rpd a⟩ * ⟨f, hf⟩ :=
    Subtype.ext (Algebra.smul_def _ _)
  rw [this, map_mul, residue₁_cst, Algebra.smul_def]
theorem residue₂_smul (a : ↥A) {f : FM} (hf : f ∈ Rpd.R₂.integers) :
    Rpd.R₂.residue ⟨(a : QQ) • f, smul_mem₂ Rpd hf a⟩ = IsLocalRing.residue ↥A a • Rpd.R₂.residue ⟨f, hf⟩ := by
  have : (⟨(a : QQ) • f, smul_mem₂ Rpd hf a⟩ : Rpd.R₂.integers) = ⟨algebraMap QQ FM (a : QQ), cst_mem₂ Rpd a⟩ * ⟨f, hf⟩ :=
    Subtype.ext (Algebra.smul_def _ _)
  rw [this, map_mul, residue₂_cst, Algebra.smul_def]

variable {α β : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
  {hα : α.IsIntegral} {hβ : β.IsIntegral}
  {δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))}

theorem not_isStrictSnd_of_isStrictFst {W : Place QQ FM} (h : Psp.IsStrictFst α β hα hβ δ W) :
    ¬ Psp.IsStrictSnd α β hα hβ δ W := by
  rintro ⟨h1, -⟩
  apply h.2
  show Fr (δ (Fr (Psp.reduceFst α hα W))) = Psp.reduceFst α hα W
  rw [h.1]
  exact h1.symm

theorem reduceFst_ne_of_fixed
    (hcomm : ∀ w, Fr (δ w) = δ (Fr w)) (hinj : Function.Injective Fr)
    {v : Place κ Fb} (hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v)
    {W : Place QQ FM} (hW : Psp.IsStrictFst α β hα hβ δ W ∨ Psp.IsStrictSnd α β hα hβ δ W) :
    Psp.reduceFst α hα W ≠ v := by
  rintro rfl
  rcases hW with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2 hv
  · apply h2

    change Fr (δ (Fr (Psp.reduceFst α hα W))) = Psp.reduceFst α hα W at hv
    show Fr (δ (Fr (Psp.reduceSnd β hβ δ W))) = Psp.reduceSnd β hβ δ W
    rw [h1] at hv
    rw [hcomm]
    exact hinj hv

theorem reduceSnd_ne_of_fixed
    (hcomm : ∀ w, Fr (δ w) = δ (Fr w)) (hinj : Function.Injective Fr) (hδinj : Function.Injective δ)
    {v : Place κ Fb} (hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v)
    {W : Place QQ FM} (hW : Psp.IsStrictFst α β hα hβ δ W ∨ Psp.IsStrictSnd α β hα hβ δ W) :
    Psp.reduceSnd β hβ δ W ≠ v := by
  rintro rfl
  rcases hW with ⟨h1, h2⟩ | ⟨-, h2⟩
  · apply h2
    change Fr (δ (Fr (Psp.reduceSnd β hβ δ W))) = Psp.reduceSnd β hβ δ W at hv
    show Fr (δ (Fr (Psp.reduceFst α hα W))) = Psp.reduceFst α hα W

    rw [← h1] at hv

    rw [hcomm, hcomm, hcomm] at hv

    have hv' := hδinj hv
    rw [hcomm]
    rw [← hcomm] at hv'
    exact hinj hv'
  · exact h2 hv

end TupleH

section FacesH
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
local notation "QQ" => AlgebraicClosure ℚ
local notation "κ" => ResidueField ↥A
local notation "FM" => ↥(xHFunctionFieldBar M H)
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
local notation "Fr" => qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
local notation "InftyH" => JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)
local notation "ZeroH" => JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)
local notation "AffH" => JHPlaceSpecialization.IsAffinePlace p M H hpM A

theorem frob_injective : Function.Injective Fr :=
  (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1

theorem delta_injective {pb : (ZMod (M / p))ˣ} (δ : Place κ Fb → Place κ Fb)
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v) :
    Function.Injective δ := by
  intro a b h
  rw [hδ, hδ] at h
  exact smul_left_cancel _ h

theorem frob_delta_comm (hpM2 : ¬ p ^ 2 ∣ M) {pb : (ZMod (M / p))ˣ} (δ : Place κ Fb → Place κ Fb)
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (w : Place κ Fb) : Fr (δ w) = δ (Fr w) := by
  have hpM' : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)
  rw [hδ, hδ]
  exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpM'
    (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) w

theorem affine_frob (hA : A.LiesOverPrime p) (v : Place κ Fb) (hv : AffH v) : AffH (Fr v) :=
  (ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    p M H hpM A hA).1 v hv

theorem affine_of_affine_frob (hA : A.LiesOverPrime p) (v : Place κ Fb) (hv : AffH (Fr v)) : AffH v :=
  ModularCurve.JHPlaceSpecialization.isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL p M H hpM A hA v hv

theorem affine_delta (hA : A.LiesOverPrime p) {pb : (ZMod (M / p))ˣ} (δ : Place κ Fb → Place κ Fb)
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (v : Place κ Fb) (hv : AffH v) : AffH (δ v) := by
  rw [hδ]
  exact (ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    p M H hpM A hA).2 _ v hv

set_option maxHeartbeats 3200000 in
theorem affine_of_affine_delta (hA : A.LiesOverPrime p) {pb : (ZMod (M / p))ˣ} (δ : Place κ Fb → Place κ Fb)
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (v : Place κ Fb) (hv : AffH (δ v)) : AffH v := by
  have h := (ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    p M H hpM A hA).2 (CuspForm.gammaLift (M / p) pb)⁻¹ (δ v) hv
  have e : SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)⁻¹) •
      δ v = v := by
    rw [hδ v, map_inv, map_inv, inv_smul_smul]
  rwa [e] at h

theorem not_side_of_affine (hpM2 : ¬ p ^ 2 ∣ M) (hA : A.LiesOverPrime p) (Psp : JHPlaceSpecialization p M H hpM A)
    {α β : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
    (hα : α.IsIntegral) (hβ : β.IsIntegral) {pb : (ZMod (M / p))ˣ} (δ : Place κ Fb → Place κ Fb)
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (W : Place QQ FM) (h₁ : AffH (Psp.reduceFst α hα W)) (h₂ : AffH (Psp.reduceSnd β hβ δ W)) :
    ¬ InftyH W ∧ ¬ ZeroH W := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hjmem : jqModC ℚ ∈ xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM) := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
    exact intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ _)
  set xp : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjmem⟩ with hxp
  have hxp_coe : ((xp : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) := by
    show coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ)
    ext k
    rw [coeffEmb_coeff, jqModC_eq_map_intCast ℚ, jqModC_eq_map_intCast (AlgebraicClosure ℚ), HahnSeries.map_coeff,
      HahnSeries.map_coeff, eq_intCast, eq_intCast, map_intCast]

  have he : ∀ (φ : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
      (hφ : φ.IsIntegral) (V : Place QQ FM), 0 < Place.ramificationIndexAlong φ V := by
    intro φ hφ V
    letI := algebraAlong φ
    haveI := isScalarTower_along φ
    haveI := isIntegral_along φ hφ
    exact V.ramificationIndex_pos (F := ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)))

  have hdesc : ∀ (φ : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
      (hφ : φ.IsIntegral),
      (∀ a : ↥A, W.ord (φ xp - algebraMap (AlgebraicClosure ℚ) FM (a : AlgebraicClosure ℚ)) ≤ 0) →
      ∀ a : ↥A, (W.restrictAlong φ hφ).ord
        (xp - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro φ hφ hW a
    have key := Place.ord_restrictAlong φ hφ W
      (xp - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ))
    rw [map_sub, AlgHom.commutes] at key
    have hle := hW a
    rw [key] at hle
    by_contra hpos
    push Not at hpos
    exact absurd hle (not_le.mpr (mul_pos (by exact_mod_cast he φ hφ W) hpos))
  constructor
  · intro hI
    have hcusp := hI.1
    obtain ⟨xb, a', hxb, hva⟩ := h₁
    have hW : ∀ a : ↥A, W.ord (α xp - algebraMap (AlgebraicClosure ℚ) FM (a : AlgebraicClosure ℚ)) ≤ 0 :=
      fun a => hcusp (α xp) (by rw [hα_coe, hxp_coe]) a
    have hneg := ModularCurve.JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le p M H hpM hpM2 A hA Psp
      xp xb hxp_coe hxb (W.restrictAlong α hα) (hdesc α hα hW)
    have h0 : 0 ≤ (Psp.reduceFst α hα W).ord xb := ord_nonneg_of_hasValue _ hva
    exact absurd hneg (not_lt.mpr h0)
  · intro hZ
    have hcusp' := hZ.1
    have h₂' : AffH (Psp.sp (W.restrictAlong β hβ)) := affine_of_affine_delta hA δ hδ _ h₂
    obtain ⟨xb, a', hxb, hva⟩ := h₂'
    have hW : ∀ a : ↥A, W.ord (β xp - algebraMap (AlgebraicClosure ℚ) FM (a : AlgebraicClosure ℚ)) ≤ 0 :=
      fun a => hcusp' (β xp) (by rw [hβ_coe, hxp_coe]) a
    have hneg := ModularCurve.JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le p M H hpM hpM2 A hA Psp
      xp xb hxp_coe hxb (W.restrictAlong β hβ) (hdesc β hβ hW)
    exact absurd hneg (not_lt.mpr (ord_nonneg_of_hasValue _ hva))

theorem affine_both_of_strict (hA : A.LiesOverPrime p) (Psp : JHPlaceSpecialization p M H hpM A)
    {α β : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
    {hα : α.IsIntegral} {hβ : β.IsIntegral} {pb : (ZMod (M / p))ˣ} (δ : Place κ Fb → Place κ Fb)
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (W : Place QQ FM)
    (h : (Psp.IsStrictFst α β hα hβ δ W ∧ AffH (Psp.reduceFst α hα W)) ∨ (Psp.IsStrictSnd α β hα hβ δ W ∧ AffH (Psp.reduceSnd β hβ δ W))) :
    AffH (Psp.reduceFst α hα W) ∧ AffH (Psp.reduceSnd β hβ δ W) := by
  rcases h with ⟨hs, ha⟩ | ⟨hs, ha⟩
  · refine ⟨ha, ?_⟩
    rw [← hs.1]; exact affine_delta hA δ hδ _ (affine_frob hA _ ha)
  · refine ⟨?_, ha⟩
    rw [hs.1]; exact affine_frob hA _ ha

theorem exists_divisorH (f : FM) (hf : f ≠ 0) : ∃ D : Divisor QQ FM, ∀ W, D W = W.ord f := by
  have h : HasPrincipalDivisors (AlgebraicClosure ℚ) FM := ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M H
  obtain ⟨D, hD, -⟩ := h.exists_divisor f hf
  exact ⟨D, hD⟩

end FacesH

section FStubsBlr
open Polynomial

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

theorem fixed_frob {δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))}
    (hcomm : ∀ w, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ w) = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w))
    {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))} (hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v) : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) := by
  change qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v))) = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v
  change qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) = v at hv
  rw [hcomm] at hv
  rw [hv]

theorem delta_frob_frob_eq_of_fixed {δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))}
    (hcomm : ∀ w, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ w) = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w))
    {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))} (hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v) : δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) = v := by
  change qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) = v at hv
  rw [hcomm] at hv
  exact hv

theorem fst_eq_frob_snd_of_mem_SS
    {SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hs : s ∈ SS) :
    s.1 = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p s.2 :=
  ((mem_ssNodePairsQExp_iff s).mp ((hSS s).mp hs)).2

theorem fixed_of_mem_SS (hpM2 : ¬ p ^ 2 ∣ M)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    {δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))}
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (hcomm : ∀ w, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ w) = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w))
    {SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hs : s ∈ SS) :
    JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ s.1 := by
  obtain ⟨h2, h1⟩ := (mem_ssNodePairsQExp_iff s).mp ((hSS s).mp hs)
  rw [h1]
  exact fixed_frob hcomm
    (ModularCurve.JHPlaceSpecialization.fixed_of_mem_ssPlacesQExp p M H hpM hpM2 A pb hpb δ hδ s.2 h2)

theorem exists_mu (c : ResidueField ↥A) : ∃ μ : ↥A, IsLocalRing.residue ↥A μ ≠ 0 ∧ IsLocalRing.residue ↥A μ ≠ c := by
  by_cases h1 : c = 1
  · subst h1
    by_cases h2 : (2 : ResidueField ↥A) = 0
    ·
      obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, (X ^ 2 + X + 1 : (AlgebraicClosure ℚ)[X]).IsRoot ζ := by
        refine IsAlgClosed.exists_root _ ?_
        have hdeg : (X ^ 2 + X + 1 : (AlgebraicClosure ℚ)[X]).degree = 2 := by compute_degree!
        rw [hdeg]; norm_num
      have hζeq : ζ ^ 2 + ζ + 1 = 0 := by simpa using hζ
      have hζ3 : ζ ^ 3 = 1 := by
        have : ζ ^ 3 - 1 = (ζ - 1) * (ζ ^ 2 + ζ + 1) := by ring
        rw [hζeq, mul_zero, sub_eq_zero] at this; exact this
      have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζeq
      have hζA : ζ ∈ A := by
        rcases A.mem_or_inv_mem ζ with h | h
        · exact h
        · have : ζ = (ζ⁻¹) ^ 2 := by
            have h3 : ζ * ζ ^ 2 = 1 := by rw [← pow_succ', hζ3]
            rw [inv_pow]; exact eq_inv_of_mul_eq_one_left h3
          rw [this]; exact pow_mem h 2
      refine ⟨⟨ζ, hζA⟩, ?_, ?_⟩
      · intro h0
        have : IsLocalRing.residue ↥A (⟨ζ, hζA⟩ ^ 2 + ⟨ζ, hζA⟩ + 1) = 0 := by
          have hz : (⟨ζ, hζA⟩ ^ 2 + ⟨ζ, hζA⟩ + 1 : ↥A) = 0 := Subtype.ext (by simpa using hζeq)
          rw [hz, map_zero]
        rw [map_add, map_add, map_pow, h0, map_one] at this
        simp at this
      · intro h1
        have : IsLocalRing.residue ↥A (⟨ζ, hζA⟩ ^ 2 + ⟨ζ, hζA⟩ + 1) = 0 := by
          have hz : (⟨ζ, hζA⟩ ^ 2 + ⟨ζ, hζA⟩ + 1 : ↥A) = 0 := Subtype.ext (by simpa using hζeq)
          rw [hz, map_zero]
        rw [map_add, map_add, map_pow, h1, map_one, one_pow] at this
        have h11 : (1 : ResidueField ↥A) + 1 = 0 := one_add_one_eq_two.trans h2
        rw [h11, zero_add] at this
        exact one_ne_zero this
    · refine ⟨-1, ?_, ?_⟩
      · rw [map_neg, map_one]; exact neg_ne_zero.mpr one_ne_zero
      · rw [map_neg, map_one]
        intro h
        apply h2
        linear_combination -h
  · exact ⟨1, by rw [map_one]; exact one_ne_zero, by rw [map_one]; exact Ne.symm h1⟩

end FStubsBlr

section Key
open Ws25.RigB

set_option maxHeartbeats 16000000 in

theorem key_noPrimitivePart
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))

    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁ : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁ i)) (hQ₂ : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂ j))
    (hinj₁ : Function.Injective fun i => Psp.reduceFst α hα (Q₁ i))
    (hinj₂ : Function.Injective fun j => Psp.reduceSnd β hβ δ (Q₂ j))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁' : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁' i)) (hQ₂' : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂' j))
    (hred₁ : ∀ i, Psp.reduceFst α hα (Q₁' i) = Psp.reduceFst α hα (Q₁ i))
    (hred₂ : ∀ j, Psp.reduceSnd β hβ δ (Q₂' j) = Psp.reduceSnd β hβ δ (Q₂ j))
    {T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁ i) = v) (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, Psp.reduceSnd β hβ δ (Q₂ j) = v)
    (hT₁W : Disjoint T₁ (SS.image Prod.fst))
    (hT₁aff : ∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hT₂aff : ∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
    (hgp₁ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ (SS.image Prod.fst), w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : (ResidueField ↥A), h = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c)
    (Qs : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQs : Psp.IsStrictFst α β hα hβ δ Qs) (hQs' : ∀ i, Psp.reduceFst α hα Qs ≠ Psp.reduceFst α hα (Q₁ i))
    (n : ℕ) (hn : (n : (ResidueField ↥A)) ≠ 0)

    (f₂ : ↥(xHFunctionFieldBar M H)) (h₁ : f₂ ∈ Rpd.R₁.integers) (h₂ : f₂ ∈ Rpd.R₂.integers)
    (hres₁ : Rpd.R₁.residue ⟨f₂, h₁⟩ = 1) (hres₂ : Rpd.R₂.residue ⟨f₂, h₂⟩ = 1)
    (hval : Qs.HasValue f₂ (1 : AlgebraicClosure ℚ))
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord f₂ = (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V))

    (hcomm : ∀ w, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ w) = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w))
    (hFrinj : Function.Injective (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p))
    (hδinj : Function.Injective δ)

    (s₀ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hs₀ : s₀ ∈ SS)

    (g : ↥(xHFunctionFieldBar M H)) (hg_def : g = f₂ - 1)
    (e : (AlgebraicClosure ℚ)) (he : e ≠ 0)
    (hε₁ : e • g ∈ Rpd.R₁.integers) (hε₂ : e • g ∈ Rpd.R₂.integers)
    (hAB : Rpd.R₁.residue ⟨e • g, hε₁⟩ ≠ 0 ∨ Rpd.R₂.residue ⟨e • g, hε₂⟩ ≠ 0)

    (hgpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord g < 0 → (∃ i, V = Q₁ i ∧ Q₁' i ≠ Q₁ i) ∨ (∃ j, V = Q₂ j ∧ Q₂' j ≠ Q₂ j))
    (hgval : Qs.HasValue g (0 : (AlgebraicClosure ℚ)))
    (hpQ₁ : ∀ i, Q₁' i ≠ Q₁ i → (Q₁ i).ord f₂ = -(n : ℤ) ∧ (Q₁' i).ord f₂ = n)
    (hpQ₂ : ∀ j, Q₂' j ≠ Q₂ j → (Q₂ j).ord f₂ = -(n : ℤ) ∧ (Q₂' j).ord f₂ = n)
    (hg0₁ : ∀ i (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα (Q₁ i) → W ≠ Q₁ i → W ≠ Q₁' i → W.ord f₂ = 0)
    (hg0₂ : ∀ j (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ (Q₂ j) → W ≠ Q₂ j → W ≠ Q₂' j → W.ord f₂ = 0) :
    False := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have hf₂₁ : f₂ ∈ Rpd.R₁.integers := h₁
  have hf₂₂ : f₂ ∈ Rpd.R₂.integers := h₂
  have hres₁f₂' : Rpd.R₁.residue ⟨f₂, hf₂₁⟩ ≠ 0 := by rw [hres₁]; exact one_ne_zero
  have hres₂f₂' : Rpd.R₂.residue ⟨f₂, hf₂₂⟩ ≠ 0 := by rw [hres₂]; exact one_ne_zero

  have hSSfix : ∀ s ∈ SS, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ s.1 := fun s hs => fixed_of_mem_SS hpM2 pb hpb hδ hcomm hSS s hs
  have hSSsnd : ∀ s ∈ SS, s.1 = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p s.2 := fun s hs => fst_eq_frob_snd_of_mem_SS hSS s hs
  set ε : ↥(xHFunctionFieldBar M H) := e • g with hεg
  have hordε : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord ε = V.ord g := fun V => by rw [hεg, ord_smul V he]
  have hεpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord ε < 0 →
      (∃ i, V = Q₁ i ∧ Q₁' i ≠ Q₁ i) ∨ (∃ j, V = Q₂ j ∧ Q₂' j ≠ Q₂ j) :=
    fun V hV => hgpole V (by rwa [← hordε])
  have hεstrict : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord ε < 0 → Psp.IsStrictFst α β hα hβ δ V ∨ Psp.IsStrictSnd α β hα hβ δ V := by
    intro V hV
    rcases hεpole V hV with ⟨i, rfl, -⟩ | ⟨j, rfl, -⟩
    exacts [Or.inl (hQ₁ i), Or.inr (hQ₂ j)]
  have hεT : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord ε < 0 →
      (Psp.IsStrictFst α β hα hβ δ V ∧ Psp.reduceFst α hα V ∈ T₁) ∨ (Psp.IsStrictSnd α β hα hβ δ V ∧ Psp.reduceSnd β hβ δ V ∈ T₂) := by
    intro V hV
    rcases hεpole V hV with ⟨i, rfl, -⟩ | ⟨j, rfl, -⟩
    · exact Or.inl ⟨hQ₁ i, (hT₁ _).mpr ⟨i, rfl⟩⟩
    · exact Or.inr ⟨hQ₂ j, (hT₂ _).mpr ⟨j, rfl⟩⟩
  have hεval : Qs.HasValue ε 0 := by
    have := HasValue.smul Qs hgval e
    rwa [mul_zero] at this
  set r₁ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := Rpd.R₁.residue ⟨ε, hε₁⟩ with hr₁_def
  set r₂ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := Rpd.R₂.residue ⟨ε, hε₂⟩ with hr₂_def

  have hεfix : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord ε := by
    intro v hv V hVv
    by_contra hlt; push Not at hlt
    exact reduceFst_ne_of_fixed hcomm hFrinj hv (hεstrict V hlt) hVv
  have hεcusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord ε < 0 → ¬ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) V ∧ ¬ JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V := by
    intro V hV
    have hab : JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) ∧ JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ V) := by
      apply affine_both_of_strict hA Psp δ hδ V
      rcases hεT V hV with ⟨hs, h⟩ | ⟨hs, h⟩
      exacts [Or.inl ⟨hs, hT₁aff _ h⟩, Or.inr ⟨hs, hT₂aff _ h⟩]
    exact not_side_of_affine hpM2 hA Psp hα hβ δ hδ hα_coe hβ_coe V hab.1 hab.2

  have hr₁v : (Psp.reduceFst α hα Qs).HasValue r₁ 0 := by
    obtain ⟨c, hcQ, hcv⟩ :=
      ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp
        p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit hcusp
        Qs hQs ε hε₁ (fun V hV hVv => by
          by_contra hlt; push Not at hlt
          rcases hεpole V hlt with ⟨i, rfl, -⟩ | ⟨j, rfl, -⟩
          · exact hQs' i hVv.symm
          · exact not_isStrictSnd_of_isStrictFst hV (hQ₂ j))
    have hc0 : c = 0 := by
      have h : ((c : (AlgebraicClosure ℚ))) = 0 := hcQ.unique hεval
      exact_mod_cast h
    rw [hc0, map_zero] at hcv
    exact hcv

  have hnode : ∀ s ∈ SS, ∃ c : (ResidueField ↥A), s.1.HasValue r₁ c ∧ s.2.HasValue r₂ c := by
    intro s hs
    exact hRL.2 ε hε₁ hε₂ s hs (hεfix s.1 (hSSfix s hs))

  have hunit : ∀ μ : ↥A, IsLocalRing.residue ↥A μ ≠ 0 → (∀ c : (ResidueField ↥A), r₂ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c → IsLocalRing.residue ↥A μ + c ≠ 0) →
      ∃ (hu₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε ∈ Rpd.R₁.integers) (hu₂ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨_, hu₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨_, hu₂⟩ ≠ 0 ∧
        Rpd.R₁.residue ⟨_, hu₁⟩ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A μ) + r₁ ∧ Rpd.R₂.residue ⟨_, hu₂⟩ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A μ) + r₂ ∧
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), 0 ≤ V.ord ε → 0 ≤ V.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε)) ∧
        ∃ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ∀ W, D W = W.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε) := by
    intro μ hμ0 hμκ
    have hu₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε ∈ Rpd.R₁.integers := add_mem (cst_mem₁ Rpd μ) hε₁
    have hu₂ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε ∈ Rpd.R₂.integers := add_mem (cst_mem₂ Rpd μ) hε₂
    have hresu₁ : Rpd.R₁.residue ⟨_, hu₁⟩ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A μ) + r₁ := by
      have : (⟨_, hu₁⟩ : Rpd.R₁.integers) = ⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)), cst_mem₁ Rpd μ⟩ + ⟨ε, hε₁⟩ := Subtype.ext rfl
      rw [this, map_add, residue₁_cst Rpd]
    have hresu₂ : Rpd.R₂.residue ⟨_, hu₂⟩ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A μ) + r₂ := by
      have : (⟨_, hu₂⟩ : Rpd.R₂.integers) = ⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)), cst_mem₂ Rpd μ⟩ + ⟨ε, hε₂⟩ := Subtype.ext rfl
      rw [this, map_add, residue₂_cst Rpd]
    have hordu : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), 0 ≤ V.ord ε → 0 ≤ V.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε) := fun V hV =>
      V.ord_nonneg_of_mem (add_mem (V.algebraMap_mem' _) (mem_of_ord_nonneg' V hV))
    refine ⟨hu₁, hu₂, ?_, ?_, hresu₁, hresu₂, hordu, ?_⟩
    · rw [hresu₁]
      have hval' : (Psp.reduceFst α hα Qs).HasValue (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A μ) + r₁) (IsLocalRing.residue ↥A μ + 0) :=
        HasValue.add _ ((Psp.reduceFst α hα Qs).hasValue_algebraMap _) hr₁v
      rw [add_zero] at hval'
      exact hval'.ne_zero hμ0
    · rw [hresu₂]
      intro h
      have : r₂ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (-IsLocalRing.residue ↥A μ) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_right h
      exact hμκ (-IsLocalRing.residue ↥A μ) this (by simp)
    · have hu0 : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε ≠ 0 := by
        have hval' : Qs.HasValue (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε) ((μ : (AlgebraicClosure ℚ)) + 0) :=
          HasValue.add Qs (Qs.hasValue_algebraMap _) hεval
        rw [add_zero] at hval'
        refine hval'.ne_zero ?_
        intro h; apply hμ0
        have : μ = 0 := Subtype.ext h
        rw [this, map_zero]
      exact exists_divisorH _ hu0

  have hreg_of_unit : ∀ (μ : ↥A) (hu₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε ∈ Rpd.R₁.integers) (hu₂ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨_, hu₁⟩ ≠ 0 → Rpd.R₂.residue ⟨_, hu₂⟩ ≠ 0 →
      Rpd.R₁.residue ⟨_, hu₁⟩ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A μ) + r₁ → Rpd.R₂.residue ⟨_, hu₂⟩ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A μ) + r₂ →
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), 0 ≤ V.ord ε → 0 ≤ V.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε)) →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε)) →
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ V → Psp.reduceFst α hα V = v → 0 ≤ V.ord ε) → 0 ≤ v.ord r₁) ∧
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ V → Psp.reduceSnd β hβ δ V = v → 0 ≤ V.ord ε) → 0 ≤ v.ord r₂) := by
    intro μ hu₁ hu₂ hur₁ hur₂ hresu₁ hresu₂ hordu D hD
    have hDnn : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), 0 ≤ V.ord ε → 0 ≤ D V := fun V hV => by rw [hD]; exact hordu V hV
    have hufix : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (μ : (AlgebraicClosure ℚ)) + ε) :=
      fun v hv V hVv => hordu V (hεfix v hv V hVv)
    constructor
    · intro v hvdisc
      refine ord_nonneg_of_ord_add_algebraMap_nonneg v (IsLocalRing.residue ↥A μ) ?_
      rw [← hresu₁]
      by_cases hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v
      · by_cases haff : JHPlaceSpecialization.IsAffinePlace p M H hpM A v
        · exact (hRL.1 _ hu₁ hu₂ v hv haff (hufix v hv)).1 hur₁
        · obtain ⟨c, hc, hcv⟩ := (hcusp v haff).1
          rw [← hcv, ← hmodel.2.2.1 _ hu₁ hu₂ hur₁ hur₂ D hD c hc]
          refine mapDomain_apply_nonneg _ _ _ fun V _ => ?_
          rw [Finsupp.filter_apply]
          split_ifs with hI
          · refine hDnn V ?_
            by_contra hlt; push Not at hlt
            exact (hεcusp V hlt).1 hI
          · exact le_rfl
      · rw [← hmodel.1 _ hu₁ hu₂ hur₁ hur₂ D hD v hv]
        refine mapDomain_apply_nonneg _ _ _ fun V hVv => ?_
        simp only [JHPlaceSpecialization.fstDiv, Finsupp.filter_apply]
        split_ifs with hI
        · exact hDnn V (hvdisc V hI hVv)
        · exact le_rfl
    · intro v hvdisc
      refine ord_nonneg_of_ord_add_algebraMap_nonneg v (IsLocalRing.residue ↥A μ) ?_
      rw [← hresu₂]
      by_cases hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v
      · by_cases haff : JHPlaceSpecialization.IsAffinePlace p M H hpM A v
        ·
          have hv' : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) := fixed_frob hcomm hv
          have haff' : JHPlaceSpecialization.IsAffinePlace p M H hpM A (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) := affine_frob hA v haff
          have hδv : δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) = v := delta_frob_frob_eq_of_fixed hcomm hv
          have := (hRL.1 _ hu₁ hu₂ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) hv' haff' (hufix (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) hv')).2 hur₂
          rwa [hδv] at this
        · obtain ⟨c, hc, hcv⟩ := (hcusp v haff).2
          rw [← hcv, ← hmodel.2.2.2 _ hu₁ hu₂ hur₁ hur₂ D hD c hc]
          refine mapDomain_apply_nonneg _ _ _ fun V _ => ?_
          rw [Finsupp.filter_apply]
          split_ifs with hI
          · refine hDnn V ?_
            by_contra hlt; push Not at hlt
            exact (hεcusp V hlt).2 hI
          · exact le_rfl
      · rw [← hmodel.2.1 _ hu₁ hu₂ hur₁ hur₂ D hD v hv]
        refine mapDomain_apply_nonneg _ _ _ fun V hVv => ?_
        simp only [JHPlaceSpecialization.sndDiv, Finsupp.filter_apply]
        split_ifs with hI
        · exact hDnn V (hvdisc V hI hVv)
        · exact le_rfl

  have hoffT₁ : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ V → Psp.reduceFst α hα V = v → 0 ≤ V.ord ε := by
    intro v hv V hI hVv
    by_contra hlt; push Not at hlt
    rcases hεT V hlt with ⟨-, hT⟩ | ⟨hS, -⟩
    · exact hv (hVv ▸ hT)
    · exact not_isStrictSnd_of_isStrictFst hI hS
  have hoffT₂ : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ V → Psp.reduceSnd β hβ δ V = v → 0 ≤ V.ord ε := by
    intro v hv V hI hVv
    by_contra hlt; push Not at hlt
    rcases hεT V hlt with ⟨hF, -⟩ | ⟨-, hT⟩
    · exact not_isStrictSnd_of_isStrictFst hF hI
    · exact hv (hVv ▸ hT)

  have hε0 : ε ≠ 0 := fun h => by
    rcases hAB with hA' | hB'
    · apply hA'
      have : (⟨ε, hε₁⟩ : Rpd.R₁.integers) = 0 := Subtype.ext h
      rw [hr₁_def, this, map_zero]
    · apply hB'
      have : (⟨ε, hε₂⟩ : Rpd.R₂.integers) = 0 := Subtype.ext h
      rw [hr₂_def, this, map_zero]
  have hcst : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) e⁻¹ = g * ε⁻¹ := by
    rw [hεg, Algebra.smul_def, mul_inv, ← mul_assoc, mul_comm g, mul_assoc, mul_inv_cancel₀ (by
      intro h0; apply hε0; rw [hεg, Algebra.smul_def, h0, mul_zero]), mul_one, map_inv₀]
  have hgR₁ : g ∈ Rpd.R₁.integers := by rw [hg_def]; exact sub_mem hf₂₁ (one_mem _)
  have hgR₂ : g ∈ Rpd.R₂.integers := by rw [hg_def]; exact sub_mem hf₂₂ (one_mem _)
  have heA : e⁻¹ ∈ A := by
    rcases hAB with hA' | hB'
    · have hεinv : ε⁻¹ ∈ Rpd.R₁.integers := inv_mem_of_isUnit hε₁ (Rpd.R₁.isUnit_of_residue_ne_zero hA')
      exact (Rpd.R₁.algebraMap_mem_iff _).mp (hcst ▸ mul_mem hgR₁ hεinv)
    · have hεinv : ε⁻¹ ∈ Rpd.R₂.integers := inv_mem_of_isUnit hε₂ (Rpd.R₂.isUnit_of_residue_ne_zero hB')
      exact (Rpd.R₂.algebraMap_mem_iff _).mp (hcst ▸ mul_mem hgR₂ hεinv)
  have hgε : f₂ = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((⟨e⁻¹, heA⟩ : ↥A) : (AlgebraicClosure ℚ)) * ε := by
    show f₂ = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) e⁻¹ * ε
    rw [hεg, hg_def, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one]
    ring

  have hsimple₁ : Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ V → Psp.reduceFst α hα V = v → 0 ≤ V.ord ε) → 0 ≤ v.ord r₁) →
      ∀ v ∈ T₁, -1 ≤ v.ord r₁ := by
    intro hA' hreg v hv
    obtain ⟨i, rfl⟩ := (hT₁ v).mp hv
    by_cases hii : Q₁' i = Q₁ i
    · have h0 : 0 ≤ (Psp.reduceFst α hα (Q₁ i)).ord r₁ := by
        refine hreg _ fun V hV hVv => ?_
        by_contra hlt; push Not at hlt
        rcases hεpole V hlt with ⟨l, rfl, hl⟩ | ⟨j, rfl, -⟩
        · have hli : l = i := hinj₁ (by exact hVv)
          subst hli; exact hl hii
        · exact not_isStrictSnd_of_isStrictFst hV (hQ₂ j)
      omega
    · exact hLFst (Q₁ i) (Q₁' i) (hQ₁ i) (hQ₁' i) (hred₁ i) hii (hT₁aff _ hv) n hn f₂ hf₂₁ hres₁f₂'
        (hpQ₁ i hii).1 (hpQ₁ i hii).2 (hg0₁ i) ⟨e⁻¹, heA⟩ ε hε₁ hA' hgε
  have hsimple₂ : Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ V → Psp.reduceSnd β hβ δ V = v → 0 ≤ V.ord ε) → 0 ≤ v.ord r₂) →
      ∀ v ∈ T₂, -1 ≤ v.ord r₂ := by
    intro hB' hreg v hv
    obtain ⟨j, rfl⟩ := (hT₂ v).mp hv
    by_cases hjj : Q₂' j = Q₂ j
    · have h0 : 0 ≤ (Psp.reduceSnd β hβ δ (Q₂ j)).ord r₂ := by
        refine hreg _ fun V hV hVv => ?_
        by_contra hlt; push Not at hlt
        rcases hεpole V hlt with ⟨i, rfl, -⟩ | ⟨l, rfl, hl⟩
        · exact not_isStrictSnd_of_isStrictFst (hQ₁ i) hV
        · have hlj : l = j := hinj₂ (by exact hVv)
          subst hlj; exact hl hjj
      omega
    · exact hLSnd (Q₂ j) (Q₂' j) (hQ₂ j) (hQ₂' j) (hred₂ j) hjj (hT₂aff _ hv) n hn f₂ hf₂₂ hres₂f₂'
        (hpQ₂ j hjj).1 (hpQ₂ j hjj).2 (hg0₂ j) ⟨e⁻¹, heA⟩ ε hε₂ hB' hgε

  have hr₂const : ∃ c : (ResidueField ↥A), r₂ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c := by
    by_cases hB' : Rpd.R₂.residue ⟨ε, hε₂⟩ = 0
    · exact ⟨0, by rw [map_zero]; exact hB'⟩
    · by_contra hnc
      push Not at hnc
      obtain ⟨hu₁, hu₂, hur₁, hur₂, hresu₁, hresu₂, hordu, D, hD⟩ :=
        hunit 1 (by rw [map_one]; exact one_ne_zero) (fun c hc _ => (hnc c hc).elim)
      obtain ⟨-, hreg₂⟩ := hreg_of_unit 1 hu₁ hu₂ hur₁ hur₂ hresu₁ hresu₂ hordu D hD
      obtain ⟨c, hc⟩ := hgp₂ r₂ (fun v hv => hreg₂ v (hoffT₂ v hv)) (hsimple₂ hB' hreg₂)
      exact hnc c hc
  obtain ⟨κ', hκ'⟩ := hr₂const

  have hvalW : ∀ s ∈ SS, s.1.HasValue r₁ κ' := by
    intro s hs
    obtain ⟨c, hc₁, hc₂⟩ := hnode s hs
    rw [hκ'] at hc₂
    rwa [eq_of_hasValue_algebraMap _ hc₂] at hc₁

  obtain ⟨μ, hμ0, hμκ⟩ := exists_mu (A := A) (-κ')
  obtain ⟨hu₁, hu₂, hur₁, hur₂, hresu₁, hresu₂, hordu, D, hD⟩ := hunit μ hμ0 (fun c hc h => by
    have hcc : c = κ' := (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).injective (hc.symm.trans hκ')
    apply hμκ; rw [← hcc]; exact eq_neg_of_add_eq_zero_left h)
  obtain ⟨hreg₁, -⟩ := hreg_of_unit μ hu₁ hu₂ hur₁ hur₂ hresu₁ hresu₂ hordu D hD
  by_cases hA' : Rpd.R₁.residue ⟨ε, hε₁⟩ = 0
  ·
    have hr₁0 : r₁ = 0 := hA'
    have hB' : Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 := by
      rcases hAB with h | h
      exacts [absurd hA' h, h]
    have hκ0 : κ' = 0 := by
      have h := hvalW s₀ hs₀
      rw [hr₁0] at h
      exact h.unique (hasValue_zero _)
    apply hB'
    show r₂ = 0
    rw [hκ', hκ0, map_zero]
  ·

    have h1 : r₁ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) κ' := by
      by_cases h10 : r₁ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) κ' = 0
      · exact sub_eq_zero.mp h10
      · exfalso; apply h10
        refine hgp₁ (r₁ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) κ') (fun v hv => ?_) (fun v hv => ?_) (fun w hw => ?_)
        · exact v.ord_nonneg_of_mem (sub_mem (mem_of_ord_nonneg' v (hreg₁ v (hoffT₁ v hv))) (v.algebraMap_mem' _))
        · exact le_ord_sub_algebraMap v κ' (by norm_num) (hsimple₁ hA' hreg₁ v hv) h10
        · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
          have := HasValue.add s.1 (hvalW s hs) (s.1.hasValue_algebraMap (-κ'))
          rw [add_neg_cancel, map_neg, ← sub_eq_add_neg] at this
          exact this
    rw [h1] at hr₁v
    have hκ0 : κ' = 0 := (eq_of_hasValue_algebraMap _ hr₁v).symm
    apply hA'
    show r₁ = 0
    rw [h1, hκ0, map_zero]

end Key
end Ws25.RigB

section Main
open Ws25.RigB

set_option hygiene false in
local notation "QQ" => AlgebraicClosure ℚ
set_option hygiene false in
local notation "κ" => ResidueField ↥A
set_option hygiene false in
local notation "FM" => ↥(xHFunctionFieldBar M H)
set_option hygiene false in
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
set_option hygiene false in
local notation "Fr" => qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
set_option hygiene false in
local notation "InftyH" => JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)
set_option hygiene false in
local notation "ZeroH" => JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)
set_option hygiene false in
local notation "AffH" => JHPlaceSpecialization.IsAffinePlace p M H hpM A
set_option hygiene false in
local notation "FixdH" => JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))

    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁ : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁ i)) (hQ₂ : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂ j))
    (hinj₁ : Function.Injective fun i => Psp.reduceFst α hα (Q₁ i))
    (hinj₂ : Function.Injective fun j => Psp.reduceSnd β hβ δ (Q₂ j))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁' : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁' i)) (hQ₂' : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂' j))
    (hred₁ : ∀ i, Psp.reduceFst α hα (Q₁' i) = Psp.reduceFst α hα (Q₁ i))
    (hred₂ : ∀ j, Psp.reduceSnd β hβ δ (Q₂' j) = Psp.reduceSnd β hβ δ (Q₂ j))
    {T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁ i) = v) (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, Psp.reduceSnd β hβ δ (Q₂ j) = v)
    (hT₁W : Disjoint T₁ (SS.image Prod.fst))
    (hT₁aff : ∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hT₂aff : ∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
    (hgp₁ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ (SS.image Prod.fst), w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : (ResidueField ↥A), h = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c)
    (Qs : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQs : Psp.IsStrictFst α β hα hβ δ Qs) (hQs' : ∀ i, Psp.reduceFst α hα Qs ≠ Psp.reduceFst α hα (Q₁ i))
    (n : ℕ) (hn : (n : (ResidueField ↥A)) ≠ 0)

    (f₂ : ↥(xHFunctionFieldBar M H)) (h₁ : f₂ ∈ Rpd.R₁.integers) (h₂ : f₂ ∈ Rpd.R₂.integers)
    (hres₁ : Rpd.R₁.residue ⟨f₂, h₁⟩ = 1) (hres₂ : Rpd.R₂.residue ⟨f₂, h₂⟩ = 1)
    (hval : Qs.HasValue f₂ (1 : AlgebraicClosure ℚ))
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord f₂ = (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V)) :
    (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  set E₁ : Divisor QQ FM := ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) with hE₁
  set E₁' : Divisor QQ FM := ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) with hE₁'
  set E₂ : Divisor QQ FM := ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₂
  set E₂' : Divisor QQ FM := ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) with hE₂'
  set E : Divisor QQ FM := E₁' + E₂' with hE
  set E₀ : Divisor QQ FM := E₁ + E₂ with hE₀
  set D : Divisor QQ FM := (n : ℤ) • (E - E₀) with hD_def
  have hD : ∀ V, D V = V.ord f₂ := fun V => by
    rw [hdiv V, hD_def, Finsupp.smul_apply, smul_eq_mul]

  have hQ₁inj : Function.Injective Q₁ := fun i j h => hinj₁ (by show Psp.reduceFst α hα (Q₁ i) = Psp.reduceFst α hα (Q₁ j); rw [h])
  have hQ₂inj : Function.Injective Q₂ := fun i j h => hinj₂ (by show Psp.reduceSnd β hβ δ (Q₂ i) = Psp.reduceSnd β hβ δ (Q₂ j); rw [h])
  have hQ₁'inj : Function.Injective Q₁' := fun i j h =>
    hinj₁ (by show Psp.reduceFst α hα (Q₁ i) = Psp.reduceFst α hα (Q₁ j); rw [← hred₁ i, ← hred₁ j, h])
  have hQ₂'inj : Function.Injective Q₂' := fun i j h =>
    hinj₂ (by show Psp.reduceSnd β hβ δ (Q₂ i) = Psp.reduceSnd β hβ δ (Q₂ j); rw [← hred₂ i, ← hred₂ j, h])

  have h12 : ∀ i j, Q₁ i ≠ Q₂ j := fun i j h => not_isStrictSnd_of_isStrictFst (hQ₁ i) (h ▸ hQ₂ j)
  have h12' : ∀ i j, Q₁' i ≠ Q₂' j := fun i j h => not_isStrictSnd_of_isStrictFst (hQ₁' i) (h ▸ hQ₂' j)
  have h1'2 : ∀ i j, Q₁' i ≠ Q₂ j := fun i j h => not_isStrictSnd_of_isStrictFst (hQ₁' i) (h ▸ hQ₂ j)
  have h12'' : ∀ i j, Q₁ i ≠ Q₂' j := fun i j h => not_isStrictSnd_of_isStrictFst (hQ₁ i) (h ▸ hQ₂' j)

  have hE₁_apply : ∀ V, E₁ V = ∑ i, if Q₁ i = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₁, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hE₁'_apply : ∀ V, E₁' V = ∑ i, if Q₁' i = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₁', Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hE₂_apply : ∀ V, E₂ V = ∑ j, if Q₂ j = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₂, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hE₂'_apply : ∀ V, E₂' V = ∑ j, if Q₂' j = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₂', Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hD_apply : ∀ V, D V = (n : ℤ) * ((E₁' V + E₂' V) - (E₁ V + E₂ V)) := fun V => by
    rw [hD_def, Finsupp.smul_apply, Finsupp.sub_apply, hE, hE₀, Finsupp.add_apply, Finsupp.add_apply, smul_eq_mul]

  have hE₁_off : ∀ V, (∀ i, V ≠ Q₁ i) → E₁ V = 0 := fun V h => by
    rw [hE₁_apply]; exact Finset.sum_eq_zero fun i _ => if_neg fun h' => h i h'.symm
  have hE₁'_off : ∀ V, (∀ i, V ≠ Q₁' i) → E₁' V = 0 := fun V h => by
    rw [hE₁'_apply]; exact Finset.sum_eq_zero fun i _ => if_neg fun h' => h i h'.symm
  have hE₂_off : ∀ V, (∀ j, V ≠ Q₂ j) → E₂ V = 0 := fun V h => by
    rw [hE₂_apply]; exact Finset.sum_eq_zero fun j _ => if_neg fun h' => h j h'.symm
  have hE₂'_off : ∀ V, (∀ j, V ≠ Q₂' j) → E₂' V = 0 := fun V h => by
    rw [hE₂'_apply]; exact Finset.sum_eq_zero fun j _ => if_neg fun h' => h j h'.symm

  have hsupp : ∀ V, D V ≠ 0 → ((∃ i, V = Q₁ i) ∨ (∃ i, V = Q₁' i)) ∨ ((∃ j, V = Q₂ j) ∨ (∃ j, V = Q₂' j)) := by
    intro V hV
    by_contra h; push Not at h
    apply hV
    rw [hD_apply, hE₁_off V h.1.1, hE₁'_off V h.1.2, hE₂_off V h.2.1, hE₂'_off V h.2.2]
    simp
  have htype : ∀ V, D V ≠ 0 → Psp.IsStrictFst α β hα hβ δ V ∨ Psp.IsStrictSnd α β hα hβ δ V := by
    intro V hV
    rcases hsupp V hV with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
    exacts [Or.inl (hQ₁ i), Or.inl (hQ₁' i), Or.inr (hQ₂ j), Or.inr (hQ₂' j)]

  have hE₂_fst : ∀ V, Psp.IsStrictFst α β hα hβ δ V → E₂ V = 0 := fun V hV =>
    hE₂_off V fun j h => not_isStrictSnd_of_isStrictFst hV (h ▸ hQ₂ j)
  have hE₂'_fst : ∀ V, Psp.IsStrictFst α β hα hβ δ V → E₂' V = 0 := fun V hV =>
    hE₂'_off V fun j h => not_isStrictSnd_of_isStrictFst hV (h ▸ hQ₂' j)
  have hE₁_snd : ∀ V, Psp.IsStrictSnd α β hα hβ δ V → E₁ V = 0 := fun V hV =>
    hE₁_off V fun i h => not_isStrictSnd_of_isStrictFst (h ▸ hQ₁ i) hV
  have hE₁'_snd : ∀ V, Psp.IsStrictSnd α β hα hβ δ V → E₁' V = 0 := fun V hV =>
    hE₁'_off V fun i h => not_isStrictSnd_of_isStrictFst (h ▸ hQ₁' i) hV
  have hE₁_nfst : ∀ V, ¬ Psp.IsStrictFst α β hα hβ δ V → E₁ V = 0 := fun V hV =>
    hE₁_off V fun i h => hV (h ▸ hQ₁ i)
  have hE₁'_nfst : ∀ V, ¬ Psp.IsStrictFst α β hα hβ δ V → E₁' V = 0 := fun V hV =>
    hE₁'_off V fun i h => hV (h ▸ hQ₁' i)
  have hE₂_nsnd : ∀ V, ¬ Psp.IsStrictSnd α β hα hβ δ V → E₂ V = 0 := fun V hV =>
    hE₂_off V fun j h => hV (h ▸ hQ₂ j)
  have hE₂'_nsnd : ∀ V, ¬ Psp.IsStrictSnd α β hα hβ δ V → E₂' V = 0 := fun V hV =>
    hE₂'_off V fun j h => hV (h ▸ hQ₂' j)

  have hsum₁ : ∀ i, (∑ l, if Q₁ l = Q₁ i then (1 : ℤ) else 0) = 1 := fun i => by
    rw [Finset.sum_eq_single i (fun l _ hl => if_neg (fun h => hl (hQ₁inj h))) (fun h => (h (Finset.mem_univ _)).elim)]
    simp
  have hsum₁' : ∀ i, (∑ l, if Q₁' l = Q₁' i then (1 : ℤ) else 0) = 1 := fun i => by
    rw [Finset.sum_eq_single i (fun l _ hl => if_neg (fun h => hl (hQ₁'inj h))) (fun h => (h (Finset.mem_univ _)).elim)]
    simp
  have hsum₂ : ∀ j, (∑ l, if Q₂ l = Q₂ j then (1 : ℤ) else 0) = 1 := fun j => by
    rw [Finset.sum_eq_single j (fun l _ hl => if_neg (fun h => hl (hQ₂inj h))) (fun h => (h (Finset.mem_univ _)).elim)]
    simp
  have hsum₂' : ∀ j, (∑ l, if Q₂' l = Q₂' j then (1 : ℤ) else 0) = 1 := fun j => by
    rw [Finset.sum_eq_single j (fun l _ hl => if_neg (fun h => hl (hQ₂'inj h))) (fun h => (h (Finset.mem_univ _)).elim)]
    simp
  have hE₁Q₁ : ∀ i, E₁ (Q₁ i) = 1 := fun i => by rw [hE₁_apply, hsum₁]
  have hE₁'Q₁' : ∀ i, E₁' (Q₁' i) = 1 := fun i => by rw [hE₁'_apply, hsum₁']
  have hE₂Q₂ : ∀ j, E₂ (Q₂ j) = 1 := fun j => by rw [hE₂_apply, hsum₂]
  have hE₂'Q₂' : ∀ j, E₂' (Q₂' j) = 1 := fun j => by rw [hE₂'_apply, hsum₂']
  have hE₁'Q₁ : ∀ i, E₁' (Q₁ i) = if Q₁' i = Q₁ i then 1 else 0 := fun i => by
    rw [hE₁'_apply]
    by_cases h : Q₁' i = Q₁ i
    · rw [if_pos h, ← h, hsum₁']
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun l _ => if_neg fun hl => ?_
      have : l = i := hinj₁ (by show Psp.reduceFst α hα (Q₁ l) = Psp.reduceFst α hα (Q₁ i); rw [← hred₁ l, hl])
      subst this; exact h hl
  have hE₁Q₁' : ∀ i, E₁ (Q₁' i) = if Q₁' i = Q₁ i then 1 else 0 := fun i => by
    rw [hE₁_apply]
    by_cases h : Q₁' i = Q₁ i
    · rw [if_pos h, h, hsum₁]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun l _ => if_neg fun hl => ?_
      have : l = i := hinj₁ (by show Psp.reduceFst α hα (Q₁ l) = Psp.reduceFst α hα (Q₁ i); rw [hl, hred₁ i])
      subst this; exact h hl.symm
  have hE₂'Q₂ : ∀ j, E₂' (Q₂ j) = if Q₂' j = Q₂ j then 1 else 0 := fun j => by
    rw [hE₂'_apply]
    by_cases h : Q₂' j = Q₂ j
    · rw [if_pos h, ← h, hsum₂']
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun l _ => if_neg fun hl => ?_
      have : l = j := hinj₂ (by show Psp.reduceSnd β hβ δ (Q₂ l) = Psp.reduceSnd β hβ δ (Q₂ j); rw [← hred₂ l, hl])
      subst this; exact h hl
  have hE₂Q₂' : ∀ j, E₂ (Q₂' j) = if Q₂' j = Q₂ j then 1 else 0 := fun j => by
    rw [hE₂_apply]
    by_cases h : Q₂' j = Q₂ j
    · rw [if_pos h, h, hsum₂]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun l _ => if_neg fun hl => ?_
      have : l = j := hinj₂ (by show Psp.reduceSnd β hβ δ (Q₂ l) = Psp.reduceSnd β hβ δ (Q₂ j); rw [hl, hred₂ j])
      subst this; exact h hl.symm
  have hDQ₁ : ∀ i, D (Q₁ i) = if Q₁' i = Q₁ i then 0 else -(n : ℤ) := fun i => by
    rw [hD_apply, hE₂_fst _ (hQ₁ i), hE₂'_fst _ (hQ₁ i), hE₁Q₁, hE₁'Q₁]; split_ifs <;> ring
  have hDQ₁' : ∀ i, D (Q₁' i) = if Q₁' i = Q₁ i then 0 else (n : ℤ) := fun i => by
    rw [hD_apply, hE₂_fst _ (hQ₁' i), hE₂'_fst _ (hQ₁' i), hE₁'Q₁', hE₁Q₁']; split_ifs <;> ring
  have hDQ₂ : ∀ j, D (Q₂ j) = if Q₂' j = Q₂ j then 0 else -(n : ℤ) := fun j => by
    rw [hD_apply, hE₁_snd _ (hQ₂ j), hE₁'_snd _ (hQ₂ j), hE₂Q₂, hE₂'Q₂]; split_ifs <;> ring
  have hDQ₂' : ∀ j, D (Q₂' j) = if Q₂' j = Q₂ j then 0 else (n : ℤ) := fun j => by
    rw [hD_apply, hE₁_snd _ (hQ₂' j), hE₁'_snd _ (hQ₂' j), hE₂'Q₂', hE₂Q₂']; split_ifs <;> ring

  have hordf₂ : ∀ V : Place QQ FM, V.ord f₂ = D V := fun V => (hD V).symm

  have hncusp : ∀ V : Place QQ FM, D V ≠ 0 → ¬ InftyH V ∧ ¬ ZeroH V := by
    intro V hV
    refine (fun h => not_side_of_affine hpM2 hA Psp hα hβ δ hδ hα_coe hβ_coe V h.1 h.2) (affine_both_of_strict hA Psp δ hδ V ?_)
    rcases hsupp V hV with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨hQ₁ i, hT₁aff _ ((hT₁ _).mpr ⟨i, rfl⟩)⟩
    · exact Or.inl ⟨hQ₁' i, hT₁aff _ ((hT₁ _).mpr ⟨i, (hred₁ i).symm⟩)⟩
    · exact Or.inr ⟨hQ₂ j, hT₂aff _ ((hT₂ _).mpr ⟨j, rfl⟩)⟩
    · exact Or.inr ⟨hQ₂' j, hT₂aff _ ((hT₂ _).mpr ⟨j, (hred₂ j).symm⟩)⟩

  have hcomm : ∀ w, Fr (δ w) = δ (Fr w) := frob_delta_comm hpM2 δ hδ
  have hFrinj : Function.Injective Fr := frob_injective
  have hδinj : Function.Injective δ := delta_injective δ hδ

  by_cases hg : f₂ - 1 = 0
  · have hf₂1 : f₂ = 1 := sub_eq_zero.mp hg
    have hD0 : D = 0 := by
      ext V; rw [← hordf₂, hf₂1, Place.ord_one, Finsupp.zero_apply]
    have : E - E₀ = 0 := by
      rw [hD_def] at hD0
      rcases smul_eq_zero.mp hD0 with h | h
      · exact absurd (by exact_mod_cast h : n = 0) hn0
      · exact h
    exact sub_eq_zero.mp this
  · exfalso

    have hn0' : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    set g : FM := f₂ - 1 with hg_def
    obtain ⟨e₁, he₁m, he₁r⟩ := Rpd.R₁.exists_smul_mem g hg
    obtain ⟨e₂, he₂m, he₂r⟩ := Rpd.R₂.exists_smul_mem g hg
    have he₁0 : e₁ ≠ 0 := Rpd.R₁.smul_const_ne_zero he₁m he₁r
    have he₂0 : e₂ ≠ 0 := Rpd.R₂.smul_const_ne_zero he₂m he₂r
    have hf₂0 : f₂ ≠ 0 := hval.ne_zero one_ne_zero

    have hpf : ∀ V : Place QQ FM, V.ord f₂ ≠ 0 →
        ((∃ i, V = Q₁ i) ∨ (∃ i, V = Q₁' i)) ∨ ((∃ j, V = Q₂ j) ∨ (∃ j, V = Q₂' j)) :=
      fun V hV => hsupp V (by rwa [← hordf₂])
    have hpQ₁ : ∀ i, Q₁' i ≠ Q₁ i → (Q₁ i).ord f₂ = -(n : ℤ) ∧ (Q₁' i).ord f₂ = n := fun i hi => by
      rw [hordf₂, hordf₂, hDQ₁, hDQ₁', if_neg hi, if_neg hi]; exact ⟨rfl, rfl⟩
    have hpQ₁eq : ∀ i, Q₁' i = Q₁ i → (Q₁ i).ord f₂ = 0 := fun i hi => by rw [hordf₂, hDQ₁, if_pos hi]
    have hpQ₂ : ∀ j, Q₂' j ≠ Q₂ j → (Q₂ j).ord f₂ = -(n : ℤ) ∧ (Q₂' j).ord f₂ = n := fun j hj => by
      rw [hordf₂, hordf₂, hDQ₂, hDQ₂', if_neg hj, if_neg hj]; exact ⟨rfl, rfl⟩
    have hpQ₂eq : ∀ j, Q₂' j = Q₂ j → (Q₂ j).ord f₂ = 0 := fun j hj => by rw [hordf₂, hDQ₂, if_pos hj]
    have hordf₂_nonneg : ∀ V : Place QQ FM, (∀ i, V = Q₁ i → Q₁' i = Q₁ i) → (∀ j, V = Q₂ j → Q₂' j = Q₂ j) →
        0 ≤ V.ord f₂ := by
      intro V h1 h2
      by_contra hlt; push Not at hlt
      rcases hpf V hlt.ne with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · rw [hpQ₁eq i (h1 i rfl)] at hlt; exact lt_irrefl _ hlt
      · by_cases hii : Q₁' i = Q₁ i
        · rw [hii, hpQ₁eq i hii] at hlt; exact lt_irrefl _ hlt
        · rw [(hpQ₁ i hii).2] at hlt; exact absurd hlt (not_lt.mpr hn0'.le)
      · rw [hpQ₂eq j (h2 j rfl)] at hlt; exact lt_irrefl _ hlt
      · by_cases hjj : Q₂' j = Q₂ j
        · rw [hjj, hpQ₂eq j hjj] at hlt; exact lt_irrefl _ hlt
        · rw [(hpQ₂ j hjj).2] at hlt; exact absurd hlt (not_lt.mpr hn0'.le)
    have hordg_of_nonneg : ∀ V : Place QQ FM, 0 ≤ V.ord f₂ → 0 ≤ V.ord g := fun V hV =>
      V.ord_nonneg_of_mem (sub_mem (V.mem_of_ord_nonneg hf₂0 hV) (one_mem _))
    have hgpole : ∀ V : Place QQ FM, V.ord g < 0 →
        (∃ i, V = Q₁ i ∧ Q₁' i ≠ Q₁ i) ∨ (∃ j, V = Q₂ j ∧ Q₂' j ≠ Q₂ j) := by
      intro V hV
      by_contra h; push Not at h
      exact absurd (hordg_of_nonneg V (hordf₂_nonneg V h.1 h.2)) (not_le.mpr hV)
    have hgval : Qs.HasValue g 0 := by
      have := HasValue.add Qs hval (Qs.hasValue_algebraMap (-1 : QQ))
      simpa [hg_def, sub_eq_add_neg] using this
    have hres₁f₂' : Rpd.R₁.residue ⟨f₂, h₁⟩ ≠ 0 := by rw [hres₁]; exact one_ne_zero
    have hres₂f₂' : Rpd.R₂.residue ⟨f₂, h₂⟩ ≠ 0 := by rw [hres₂]; exact one_ne_zero
    have hg0₁ : ∀ i, ∀ V : Place QQ FM, Psp.IsStrictFst α β hα hβ δ V → Psp.reduceFst α hα V = Psp.reduceFst α hα (Q₁ i) → V ≠ Q₁ i →
        V ≠ Q₁' i → V.ord f₂ = 0 := by
      intro i V hV hVv h1 h2
      by_contra h
      rcases hpf V h with (⟨l, rfl⟩ | ⟨l, rfl⟩) | (⟨l, rfl⟩ | ⟨l, rfl⟩)
      · have hli : l = i := hinj₁ (by exact hVv)
        exact h1 (by rw [hli])
      · have hli : l = i := hinj₁ (by show Psp.reduceFst α hα (Q₁ l) = Psp.reduceFst α hα (Q₁ i); rw [← hred₁ l]; exact hVv)
        exact h2 (by rw [hli])
      · exact not_isStrictSnd_of_isStrictFst hV (hQ₂ l)
      · exact not_isStrictSnd_of_isStrictFst hV (hQ₂' l)
    have hg0₂ : ∀ j, ∀ V : Place QQ FM, Psp.IsStrictSnd α β hα hβ δ V → Psp.reduceSnd β hβ δ V = Psp.reduceSnd β hβ δ (Q₂ j) → V ≠ Q₂ j →
        V ≠ Q₂' j → V.ord f₂ = 0 := by
      intro j V hV hVv h1 h2
      by_contra h
      rcases hpf V h with (⟨l, rfl⟩ | ⟨l, rfl⟩) | (⟨l, rfl⟩ | ⟨l, rfl⟩)
      · exact not_isStrictSnd_of_isStrictFst (hQ₁ l) hV
      · exact not_isStrictSnd_of_isStrictFst (hQ₁' l) hV
      · have hlj : l = j := hinj₂ (by exact hVv)
        exact h1 (by rw [hlj])
      · have hlj : l = j := hinj₂ (by show Psp.reduceSnd β hβ δ (Q₂ l) = Psp.reduceSnd β hβ δ (Q₂ j); rw [← hred₂ l]; exact hVv)
        exact h2 (by rw [hlj])

    have hSSne : SS.Nonempty := by
      by_contra hSSe
      rw [Finset.not_nonempty_iff_eq_empty] at hSSe
      have := hgp₁ 1 (fun v _ => by rw [Place.ord_one]) (fun v _ => by rw [Place.ord_one]; norm_num) (by simp [hSSe])
      exact one_ne_zero this
    obtain ⟨s₀, hs₀⟩ := hSSne

    have key : ∀ (e : QQ), e ≠ 0 → ∀ (hε₁ : e • g ∈ Rpd.R₁.integers) (hε₂ : e • g ∈ Rpd.R₂.integers),
        (Rpd.R₁.residue ⟨e • g, hε₁⟩ ≠ 0 ∨ Rpd.R₂.residue ⟨e • g, hε₂⟩ ≠ 0) → False :=
      fun e he hε₁ hε₂ hAB => Ws25.RigB.key_noPrimitivePart p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit hcusp Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ Q₁' Q₂' hQ₁' hQ₂' hred₁ hred₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hgp₁ hgp₂ Qs hQs hQs' n hn f₂ h₁ h₂ hres₁ hres₂ hval hdiv
        hcomm hFrinj hδinj s₀ hs₀ g hg_def e he hε₁ hε₂ hAB hgpole hgval hpQ₁ hpQ₂ hg0₁ hg0₂

    rcases A.mem_or_inv_mem (e₁ / e₂) with h | h
    · have hε₂ : e₁ • g ∈ Rpd.R₂.integers := by
        have : e₁ • g = ((⟨e₁ / e₂, h⟩ : A) : QQ) • (e₂ • g) := by
          rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
          congr 2
          show e₁ = e₁ / e₂ * e₂
          field_simp
        rw [this]; exact smul_mem₂ Rpd he₂m _
      exact key e₁ he₁0 he₁m hε₂ (Or.inl he₁r)
    · have h' : e₂ / e₁ ∈ A := by rwa [inv_div] at h
      have hε₁ : e₂ • g ∈ Rpd.R₁.integers := by
        have : e₂ • g = ((⟨e₂ / e₁, h'⟩ : A) : QQ) • (e₁ • g) := by
          rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
          congr 2
          show e₂ = e₂ / e₁ * e₁
          field_simp
        rw [this]; exact smul_mem₁ Rpd he₁m _
      exact key e₂ he₂0 hε₁ he₂m (Or.inr he₂r)

end Main

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp (solution)
