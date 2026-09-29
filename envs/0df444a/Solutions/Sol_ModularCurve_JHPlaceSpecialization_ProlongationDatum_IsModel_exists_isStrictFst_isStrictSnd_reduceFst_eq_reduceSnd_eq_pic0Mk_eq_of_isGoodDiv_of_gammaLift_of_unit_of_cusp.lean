-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/113f871b-e904-5b3c-b6f2-5fcb9d4ef3be

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Pic0_exists_ord_eq_mul_of_nsmul_mk_eq_zero
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField

import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_ModularCurve_QAdicPlace

import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp.AlgebraicCurve IsLocalRing ModularCurve"
open scoped MatrixGroups

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic0 Pic0.mk Pic0.mk_surjective SemilinearAut SemilinearAut.ofAlgAut Place.hasValue_algebraMap GluingData GluingData.admissible GluingData.IsGluedPrincipal GluedPic0 GluedPic0.mk GluedPic0.mk_eq_zero_iff IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.deg_eq_one_of_isAlgClosed mem_riemannRochSpace_iff genusFF LSpace ell ConstantsAreBase exists_weilCanonical_riemannRoch constantsAreBase_of_deg_eq_one isCurveOver_of_transcendental_of_perfectField"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_zero ord_mul ord_inv ord_coe_irreducible toValuationSubring mk HasValue hasValue_algebraMap ord_nonneg_of_mem mem_of_ord_nonneg"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mem ne_zero unique ord_eq_zero" end HasValue
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.sub' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have hx : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [hx, map_sub, hr, hr', map_sub]

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.sub'"
theorem ord_sub_nonneg_of_mem {f g : F} (hf : 0 ≤ v.ord f) (hg : g ∈ v.toValuationSubring) :
    0 ≤ v.ord (f - g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_sub]
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [neg_zero, ord_zero]
    · exact v.ord_nonneg_of_mem (neg_mem hg)
  · exact v.ord_nonneg_of_mem (sub_mem (v.mem_of_ord_nonneg hf0 hf) hg)

theorem neg_one_le_ord_sub_of_mem {f g : F} (hf : -1 ≤ v.ord f) (hg : g ∈ v.toValuationSubring) :
    -1 ≤ v.ord (f - g) := by
  classical
  rcases eq_or_ne (f - g) 0 with h0 | h0
  · rw [h0, ord_zero]; norm_num
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : ((π : v.toValuationSubring) : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπ1 : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hmem : (f - g) * (π : F) ∈ v.toValuationSubring := by
    rw [sub_mul]
    refine sub_mem ?_ (mul_mem hg (SetLike.coe_mem _))
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [zero_mul]; exact zero_mem _
    · apply v.mem_of_ord_nonneg (mul_ne_zero hf0 hπ0)
      rw [v.ord_mul hf0 hπ0, hπ1]; omega
  have h := v.ord_nonneg_of_mem hmem
  rw [v.ord_mul h0 hπ0, hπ1] at h
  omega

end Place
end AlgebraicCurve

theorem gpcH
    {k F : Type*} [Field k] [Field F] [Algebra k F] [DecidableEq (Place k F)]
    (SS : Finset (Place k F × Place k F)) (E₁ E₂ : Finset (Place k F))
    (hgp₁ : ∀ h : F, (∀ v, v ∉ E₁ → 0 ≤ v.ord h) → (∀ v ∈ E₁, -1 ≤ v.ord h) → (∀ w ∈ SS.image Prod.fst, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : F, (∀ v, v ∉ E₂ → 0 ≤ v.ord h) → (∀ v ∈ E₂, -1 ≤ v.ord h) → ∃ c : k, h = algebraMap k F c)
    (h₁ h₂ : F)
    (hh₁ : ∀ v, v ∉ E₁ → 0 ≤ v.ord h₁) (hh₁' : ∀ v ∈ E₁, -1 ≤ v.ord h₁)
    (hh₂ : ∀ v, v ∉ E₂ → 0 ≤ v.ord h₂) (hh₂' : ∀ v ∈ E₂, -1 ≤ v.ord h₂)
    (hval : ∀ s ∈ SS, ∃ c : k, s.1.HasValue h₁ c ∧ s.2.HasValue h₂ c) :
    ∃ c : k, h₁ = algebraMap k F c ∧ h₂ = algebraMap k F c := by
  obtain ⟨c, hc⟩ := hgp₂ h₂ hh₂ hh₂'
  refine ⟨c, ?_, hc⟩
  have hCmem : ∀ v : Place k F, algebraMap k F c ∈ v.toValuationSubring := fun v => (Place.hasValue_algebraMap v c).mem
  have hzero : h₁ - algebraMap k F c = 0 := by
    apply hgp₁ (h₁ - algebraMap k F c)
    · intro v hv; exact Place.ord_sub_nonneg_of_mem v (hh₁ v hv) (hCmem v)
    · intro v hv; exact Place.neg_one_le_ord_sub_of_mem v (hh₁' v hv) (hCmem v)
    · intro w hw
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨c', hc₁, hc₂⟩ := hval s hs
      have hc₂' : s.2.HasValue h₂ c := by rw [hc]; exact Place.hasValue_algebraMap _ c
      have hcc : c' = c := hc₂.unique hc₂'
      have := hc₁.sub' s.1 (Place.hasValue_algebraMap s.1 c)
      rwa [hcc, sub_self] at this
  exact sub_eq_zero.mp hzero

namespace EffH

scoped instance finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem essFiniteType_of_finiteDimensional_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) : Algebra.EssFiniteType K F := by
  haveI : Algebra.EssFiniteType K (IntermediateField.adjoin K ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  haveI : Module.Finite (IntermediateField.adjoin K ({x} : Set F)) F := hfd
  exact Algebra.EssFiniteType.comp K (IntermediateField.adjoin K ({x} : Set F)) F

theorem jqModC_mem_bar (M : ℕ) (H : Subgroup (ZMod M)ˣ) : jqModC (AlgebraicClosure ℚ) ∈ xHFunctionFieldBar M H := by
  have h := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (F₀ := xHFunctionField M H)
    (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H) (jqModC_mem_intFormRatiosC ℚ _))
  rwa [show coeffEmb (AlgebraicClosure ℚ) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) from rfl, coeffMap_jqModC] at h

end EffH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp.EffH"

open EffH in

theorem effH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (E₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hg : (genusFF (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) : ℤ) ≤ E₀.degree) (x : JH M H) :
    ∃ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), 0 ≤ E ∧ E.degree = E₀.degree ∧
      ∃ hdeg : E - E₀ ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)), Pic0.mk ⟨E - E₀, hdeg⟩ = x := by
  classical

  obtain ⟨t, htr, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := essFiniteType_of_finiteDimensional_adjoin t hfd

  let vinf : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    qInftyPlaceBar (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) ⟨⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_bar M H⟩, order_jqModC_def (AlgebraicClosure ℚ)⟩
  have hC : ConstantsAreBase (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    AlgebraicCurve.constantsAreBase_of_deg_eq_one vinf (IsCurveOver.deg_eq_one_of_isAlgClosed vinf)
  obtain ⟨Kc, hRR⟩ := AlgebraicCurve.exists_weilCanonical_riemannRoch (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) hC
  have hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := IsCurveOver.hasPrincipalDivisors
  obtain ⟨⟨D, hD0⟩, rfl⟩ := Pic0.mk_surjective x
  have hD0' : D.degree = 0 := hD0
  have hdegDE : (D + E₀).degree = E₀.degree := by rw [map_add, hD0', zero_add]

  have hell : (1 : ℤ) ≤ (ell (D + E₀) : ℤ) := by
    have h := hRR (D + E₀)
    have h0 : (0 : ℤ) ≤ (ell (Kc - (D + E₀)) : ℤ) := Int.natCast_nonneg _
    rw [hdegDE] at h
    linarith
  have hpos : 0 < Module.finrank (AlgebraicClosure ℚ) ↥(LSpace (D + E₀)) := by exact_mod_cast hell
  haveI : Nontrivial ↥(LSpace (D + E₀)) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨u, hu0⟩ := exists_ne (0 : ↥(LSpace (D + E₀)))
  have hu0' : (u : ↥(xHFunctionFieldBar M H)) ≠ 0 := fun h0 => hu0 (Subtype.ext h0)
  have hf : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), 0 ≤ (D + E₀) v + v.ord (u : ↥(xHFunctionFieldBar M H)) := by
    intro v
    have := ((mem_riemannRochSpace_iff.mp u.2) v).resolve_left hu0'
    linarith
  obtain ⟨Pf, hPf, hPfdeg⟩ := hPD.exists_divisor (u : ↥(xHFunctionFieldBar M H)) hu0'
  refine ⟨Pf + D + E₀, ?_, ?_, ?_⟩
  · intro v
    have hv := hf v
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply, hPf v] at hv ⊢
    omega
  · rw [map_add, map_add, hPfdeg, hD0', zero_add, zero_add]
  · have hdeg : Pf + D + E₀ - E₀ ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
      rw [add_sub_cancel_right, Divisor.mem_degZero, map_add, hPfdeg, hD0', zero_add]
    refine ⟨hdeg, ?_⟩
    apply (QuotientAddGroup.eq).mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨(u : ↥(xHFunctionFieldBar M H))⁻¹, inv_ne_zero hu0', fun v => ?_⟩
    simp [hPf v, v.ord_inv]

namespace CanonRepH

section A
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p]
  (Psp : JHPlaceSpecialization p M H hpM A)
  (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

theorem not_isStrictFst_of_isStrictSnd {W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)}
    (h2 : (Psp.IsStrictSnd α β hα hβ δ) W) : ¬ (Psp.IsStrictFst α β hα hβ δ) W := by
  intro h1
  apply h1.2
  show qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα W))) = Psp.reduceFst α hα W
  rw [h1.1]
  exact h2.1.symm

theorem degree_eq_sum (hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    D.degree = D.sum (fun _ n => n) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun W _ => ?_
  simp [hdeg1 W]

theorem fstDiv_nonneg {E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (hE : 0 ≤ E) :
    0 ≤ (Psp.fstDiv α β hα hβ δ) E := by
  intro W
  simp only [JHPlaceSpecialization.fstDiv, Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

theorem sndDiv_nonneg {E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (hE : 0 ≤ E) :
    0 ≤ (Psp.sndDiv α β hα hβ δ) E := by
  intro W
  simp only [JHPlaceSpecialization.sndDiv, Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

theorem exists_eq_fstDiv_add_sndDiv_add {E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)}
    (hE : 0 ≤ E) :
    ∃ E₃ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), 0 ≤ E₃ ∧
      E = (Psp.fstDiv α β hα hβ δ) E + (Psp.sndDiv α β hα hβ δ) E + E₃ ∧ ∀ W ∈ E₃.support, ¬ (Psp.IsStrictFst α β hα hβ δ) W ∧ ¬ (Psp.IsStrictSnd α β hα hβ δ) W := by
  classical
  refine ⟨(E.filter fun W => ¬ (Psp.IsStrictFst α β hα hβ δ) W).filter fun W => ¬ (Psp.IsStrictSnd α β hα hβ δ) W, ?_, ?_, ?_⟩
  · intro W
    simp only [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs <;> first | exact hE W | exact le_rfl
  · ext W
    simp only [JHPlaceSpecialization.fstDiv, JHPlaceSpecialization.sndDiv, Finsupp.coe_add, Pi.add_apply, Finsupp.filter_apply]
    by_cases h1 : (Psp.IsStrictFst α β hα hβ δ) W
    · have h2 : ¬ (Psp.IsStrictSnd α β hα hβ δ) W := fun h2 => (not_isStrictFst_of_isStrictSnd Psp α β hα hβ δ) h2 h1
      simp [h1, h2]
    · by_cases h2 : (Psp.IsStrictSnd α β hα hβ δ) W
      · simp [h1, h2]
      · simp [h1, h2]
  · intro W hW
    rw [Finsupp.mem_support_iff] at hW
    simp only [Finsupp.filter_apply] at hW
    by_cases h2 : ¬ (Psp.IsStrictSnd α β hα hβ δ) W
    · rw [if_pos h2] at hW
      by_cases h1 : ¬ (Psp.IsStrictFst α β hα hβ δ) W
      · exact ⟨h1, h2⟩
      · rw [if_neg h1] at hW; exact absurd rfl hW
    · rw [if_neg h2] at hW; exact absurd rfl hW

theorem exists_eq_sum_add_sum_of_mapDomain_fstDiv_sndDiv
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE : 0 ≤ E)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hinj₁ : Function.Injective fun i => (Psp.reduceFst α hα) (Q₁ i))
    (hinj₂ : Function.Injective fun j => (Psp.reduceSnd β hβ δ) (Q₂ j))
    (h₁ : Finsupp.mapDomain (Psp.reduceFst α hα) ((Psp.fstDiv α β hα hβ δ) E) = ∑ i, Finsupp.single ((Psp.reduceFst α hα) (Q₁ i)) (1 : ℤ))
    (h₂ : Finsupp.mapDomain (Psp.reduceSnd β hβ δ) ((Psp.sndDiv α β hα hβ δ) E) = ∑ j, Finsupp.single ((Psp.reduceSnd β hβ δ) (Q₂ j)) (1 : ℤ))
    (hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1) (hdeg : E.degree = (d₁ + d₂ : ℕ)) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
      (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ i, (Psp.IsStrictFst α β hα hβ δ) (Q₁' i)) ∧ (∀ j, (Psp.IsStrictSnd α β hα hβ δ) (Q₂' j)) ∧
      (∀ i, (Psp.reduceFst α hα) (Q₁' i) = (Psp.reduceFst α hα) (Q₁ i)) ∧
      (∀ j, (Psp.reduceSnd β hβ δ) (Q₂' j) = (Psp.reduceSnd β hβ δ) (Q₂ j)) ∧
      E = ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) := by
  classical
  obtain ⟨Q₁', hE₁, hred₁⟩ := Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single (Psp.reduceFst α hα) ((Psp.fstDiv α β hα hβ δ) E)
    (fstDiv_nonneg Psp α β hα hβ δ hE) (fun i => (Psp.reduceFst α hα) (Q₁ i)) hinj₁ h₁
  obtain ⟨Q₂', hE₂, hred₂⟩ := Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single (Psp.reduceSnd β hβ δ) ((Psp.sndDiv α β hα hβ δ) E)
    (sndDiv_nonneg Psp α β hα hβ δ hE) (fun j => (Psp.reduceSnd β hβ δ) (Q₂ j)) hinj₂ h₂

  have mem₁ : ∀ i, Q₁' i ∈ ((Psp.fstDiv α β hα hβ δ) E).support := by
    intro i
    rw [hE₁, Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro j _; rw [Finsupp.single_apply]; split_ifs <;> omega
    · exact ⟨i, Finset.mem_univ _, by simp⟩
  have mem₂ : ∀ j, Q₂' j ∈ ((Psp.sndDiv α β hα hβ δ) E).support := by
    intro j
    rw [hE₂, Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro i _; rw [Finsupp.single_apply]; split_ifs <;> omega
    · exact ⟨j, Finset.mem_univ _, by simp⟩
  have hQ₁' : ∀ i, (Psp.IsStrictFst α β hα hβ δ) (Q₁' i) := fun i => by
    have := mem₁ i
    rw [JHPlaceSpecialization.fstDiv, Finsupp.support_filter, Finset.mem_filter] at this
    exact this.2
  have hQ₂' : ∀ j, (Psp.IsStrictSnd α β hα hβ δ) (Q₂' j) := fun j => by
    have := mem₂ j
    rw [JHPlaceSpecialization.sndDiv, Finsupp.support_filter, Finset.mem_filter] at this
    exact this.2
  refine ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, ?_⟩

  obtain ⟨E₃, hE₃, hsplit, -⟩ := exists_eq_fstDiv_add_sndDiv_add Psp α β hα hβ δ hE
  have hmass : E₃.sum (fun _ n => n) = 0 := by
    have h := congrArg (fun D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) =>
      D.sum (fun _ n => n)) hsplit
    beta_reduce at h
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ← degree_eq_sum hdeg1, hdeg, hE₁, hE₂,
      ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl),
      ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)] at h
    simp only [Finsupp.sum_single_index, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, nsmul_eq_mul, mul_one] at h
    push_cast at h
    omega
  have hE₃0 : E₃ = 0 := by
    by_contra hne
    obtain ⟨W, hW⟩ : ∃ W, E₃ W ≠ 0 := by
      by_contra h'; push Not at h'; exact hne (Finsupp.ext h')
    have hpos : 0 < E₃.sum (fun _ n => n) := by
      rw [Finsupp.sum]
      exact Finset.sum_pos' (fun b _ => hE₃ b)
        ⟨W, Finsupp.mem_support_iff.mpr hW, lt_of_le_of_ne (hE₃ W) (Ne.symm hW)⟩
    omega
  rw [hsplit, hE₃0, add_zero, hE₁, hE₂]

end A
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp.EffH"

theorem exists_smul_mem_integers_both {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
    {Psp : JHPlaceSpecialization p M H hpM A} (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    {f : ↥(xHFunctionFieldBar M H)} (hf : f ≠ 0) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ ∃ (h₁ : c • f ∈ Rpd.R₁.integers) (h₂ : c • f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∨ Rpd.R₂.residue ⟨c • f, h₂⟩ ≠ 0 := by
  obtain ⟨c₁, hc₁, hr₁⟩ := Rpd.R₁.exists_smul_mem f hf
  obtain ⟨c₂, hc₂, hr₂⟩ := Rpd.R₂.exists_smul_mem f hf
  have hc₁0 : c₁ ≠ 0 := Rpd.R₁.smul_const_ne_zero hc₁ hr₁
  have hc₂0 : c₂ ≠ 0 := Rpd.R₂.smul_const_ne_zero hc₂ hr₂
  rcases A.mem_or_inv_mem (c₁ / c₂) with h | h
  · have hmem : c₁ • f ∈ Rpd.R₂.integers := by
      have e : c₁ • f = algebraMap (AlgebraicClosure ℚ) _ (c₁ / c₂) * (c₂ • f) := by
        rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hc₂0]
      rw [e]
      exact mul_mem ((Rpd.R₂.algebraMap_mem_iff _).mpr h) hc₂
    exact ⟨c₁, hc₁0, hc₁, hmem, Or.inl hr₁⟩
  · have hmem : c₂ • f ∈ Rpd.R₁.integers := by
      have e : c₂ • f = algebraMap (AlgebraicClosure ℚ) _ (c₂ / c₁) * (c₁ • f) := by
        rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hc₁0]
      rw [inv_div] at h
      rw [e]
      exact mul_mem ((Rpd.R₁.algebraMap_mem_iff _).mpr h) hc₁
    exact ⟨c₂, hc₂0, hmem, hc₂, Or.inr hr₂⟩

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (g : α → β) (D : α →₀ ℤ) (v : β) :
    Finsupp.mapDomain g D v = ∑ W ∈ D.support, if g W = v then D W else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.single_apply]

set_option maxHeartbeats 12800000 in
open Classical in
theorem mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
    {Psp : JHPlaceSpecialization p M H hpM A} {Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ}
    {α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)} {hα : α.IsIntegral} {hβ : β.IsIntegral}
    {δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))}
    {SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hRL : Rpd.RegularityLaw α β hα hβ δ SS)
    (hSPB : ∀ {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
      (hQ₁ : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁ i)) (hQ₂ : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂ j))
      (hinj₁ : Function.Injective fun i => Psp.reduceFst α hα (Q₁ i))
      (hinj₂ : Function.Injective fun j => Psp.reduceSnd β hβ δ (Q₂ j))
      {T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
      (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁ i) = v) (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, Psp.reduceSnd β hβ δ (Q₂ j) = v)
      (hT₁W : Disjoint T₁ (SS.image Prod.fst))
      (hT₁aff : ∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hT₂aff : ∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
      (E D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE : 0 ≤ E) (hD : Psp.IsGoodDiv α β hα hβ δ D)
      (G : ↥(xHFunctionFieldBar M H)) (h₁ : G ∈ Rpd.R₁.integers) (h₂ : G ∈ Rpd.R₂.integers)
      (hdiv : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V = V.ord G)
      (hb₁ hb₂ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hb₁0 : hb₁ ≠ 0) (hb₂0 : hb₂ ≠ 0)
      (hdiv₁ : ∀ v, Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) v = v.ord hb₁)
      (hdiv₂ : ∀ v, Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) v = v.ord hb₂)
      (hvals : ∀ s ∈ SS, ∃ c : (ResidueField ↥A), c ≠ 0 ∧ s.1.HasValue hb₁ c ∧ s.2.HasValue hb₂ c),
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord ((Rpd.R₁.residue ⟨G, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁)) ∧
    (∀ v ∈ T₁, -1 ≤ v.ord ((Rpd.R₁.residue ⟨G, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁)) ∧
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord ((Rpd.R₂.residue ⟨G, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂)) ∧
    (∀ v ∈ T₂, -1 ≤ v.ord ((Rpd.R₂.residue ⟨G, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂)) ∧
    (∀ s ∈ SS, ∃ c : (ResidueField ↥A), s.1.HasValue ((Rpd.R₁.residue ⟨G, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁) c ∧ s.2.HasValue ((Rpd.R₂.residue ⟨G, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂) c) )
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁ : ∀ i, (Psp.IsStrictFst α β hα hβ δ) (Q₁ i)) (hQ₂ : ∀ j, (Psp.IsStrictSnd α β hα hβ δ) (Q₂ j))
    (hinj₁ : Function.Injective fun i => (Psp.reduceFst α hα) (Q₁ i))
    (hinj₂ : Function.Injective fun j => (Psp.reduceSnd β hβ δ) (Q₂ j))
    {T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, (Psp.reduceFst α hα) (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, (Psp.reduceSnd β hβ δ) (Q₂ j) = v)
    (hT₁W : Disjoint T₁ (SS.image Prod.fst))
    (hT₁aff : ∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hT₂aff : ∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
    (hgp₁ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ SS.image Prod.fst, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : (ResidueField ↥A), h = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c)

    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE0 : 0 ≤ E)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hDgood : (Psp.IsGoodDiv α β hα hβ δ) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
    (hadm : (Psp.glueData α β hα hβ δ SS) D ∈
      GluingData.admissible (SS))
    (hmk : GluedPic0.mk (SS)
      ⟨(Psp.glueData α β hα hβ δ SS) D, hadm⟩ = 0)
    (f : ↥(xHFunctionFieldBar M H)) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) V = V.ord f) :
    Finsupp.mapDomain (Psp.reduceFst α hα) ((Psp.fstDiv α β hα hβ δ) E) = ∑ i, Finsupp.single ((Psp.reduceFst α hα) (Q₁ i)) (1 : ℤ) ∧
    Finsupp.mapDomain (Psp.reduceSnd β hβ δ) ((Psp.sndDiv α β hα hβ δ) E) = ∑ j, Finsupp.single ((Psp.reduceSnd β hβ δ) (Q₂ j)) (1 : ℤ) := by
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), φ = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := ⟨_, rfl⟩

  have hgp : GluingData.IsGluedPrincipal (SS)
      ((Psp.glueData α β hα hβ δ SS) D) :=
    (GluedPic0.mk_eq_zero_iff (SS) ⟨_, hadm⟩).mp hmk
  obtain ⟨hb₁, hb₂, av, bv, hb₁0, hb₂0, hdiv₁, hdiv₂, hvals, hratio⟩ := hgp
  have hab : ∀ s, av s = bv s := by
    intro s
    have h0 : ((Psp.glueData α β hα hβ δ SS) D).2.2 = 0 := rfl
    rw [h0] at hratio
    have hs := congrFun hratio s
    simp only [Pi.zero_apply] at hs
    have : av s / bv s = 1 := ofMul_eq_zero.mp hs.symm
    exact div_eq_one.mp this
  have hvalsW : ∀ s ∈ SS, ∃ c : (ResidueField ↥A), c ≠ 0 ∧ s.1.HasValue hb₁ c ∧ s.2.HasValue hb₂ c := by
    intro s hs
    refine ⟨av ⟨s, hs⟩, (av ⟨s, hs⟩).ne_zero, (hvals ⟨s, hs⟩).1, ?_⟩
    rw [hab ⟨s, hs⟩]
    exact (hvals ⟨s, hs⟩).2
  have hdiv₁' : ∀ v, Finsupp.mapDomain (Psp.reduceFst α hα) ((Psp.fstDiv α β hα hβ δ) D) v = v.ord hb₁ := hdiv₁
  have hdiv₂' : ∀ v, Finsupp.mapDomain (Psp.reduceSnd β hβ δ) ((Psp.sndDiv α β hα hβ δ) D) v = v.ord hb₂ := hdiv₂

  obtain ⟨c, hc0, hG₁, hG₂, hres⟩ := exists_smul_mem_integers_both Rpd hf0
  have hdivG : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
        - (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) V = V.ord (c • f) := by
    intro V
    rw [hdivf V, Algebra.smul_def, V.ord_mul ((map_ne_zero _).mpr hc0) hf0,
      (V.hasValue_algebraMap c).ord_eq_zero hc0, zero_add]

  obtain ⟨hA₁, hB₁, hA₂, hB₂, hC⟩ := hSPB Q₁ Q₂ hQ₁ hQ₂
    hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff E D hE0 hDgood (c • f) hG₁ hG₂ hdivG hb₁ hb₂ hb₁0 hb₂0
    hdiv₁' hdiv₂' hvalsW
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), u₁ = (Rpd.R₁.residue ⟨c • f, hG₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁ := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), u₂ = (Rpd.R₂.residue ⟨c • f, hG₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂ := ⟨_, rfl⟩
  rw [← hu₁] at hA₁ hB₁ hC
  rw [← hu₂] at hA₂ hB₂ hC
  obtain ⟨c', hu₁c, hu₂c⟩ := gpcH SS T₁ T₂ hgp₁ hgp₂ u₁ u₂ hA₁ hB₁ hA₂ hB₂ hC
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hu₁c hu₂c
    rcases hres with h | h
    · apply h
      have : Rpd.R₁.residue ⟨c • f, hG₁⟩ = 0 := by
        rw [hu₁] at hu₁c
        rcases mul_eq_zero.mp hu₁c with h' | h'
        · exact h'
        · exact absurd h' hb₁0
      exact this
    · apply h
      have : Rpd.R₂.residue ⟨c • f, hG₂⟩ = 0 := by
        rw [hu₂] at hu₂c
        rcases mul_eq_zero.mp hu₂c with h' | h'
        · exact h'
        · exact absurd h' hb₂0
      exact this
  have hres₁ : Rpd.R₁.residue ⟨c • f, hG₁⟩ ≠ 0 := by
    intro h; apply hc'0
    have : u₁ = 0 := by rw [hu₁, h, zero_mul]
    rw [this] at hu₁c
    exact ((map_eq_zero_iff _ (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).injective).mp hu₁c.symm)
  have hres₂ : Rpd.R₂.residue ⟨c • f, hG₂⟩ ≠ 0 := by
    intro h; apply hc'0
    have : u₂ = 0 := by rw [hu₂, h, zero_mul]
    rw [this] at hu₂c
    exact ((map_eq_zero_iff _ (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).injective).mp hu₂c.symm)
  have hordu₁ : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v.ord u₁ = 0 := by
    intro v; rw [hu₁c]; exact (v.hasValue_algebraMap c').ord_eq_zero hc'0
  have hordu₂ : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v.ord u₂ = 0 := by
    intro v; rw [hu₂c]; exact (v.hasValue_algebraMap c').ord_eq_zero hc'0

  have hQ₁inj : Function.Injective Q₁ := fun i j h => hinj₁ (by simp [h])
  have hQ₂inj : Function.Injective Q₂ := fun i j h => hinj₂ (by simp [h])
  have hE₁T : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).filter (Psp.IsStrictFst α β hα hβ δ) =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) := by
    rw [Finsupp.filter_eq_self_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply] at hV
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
    rw [Finsupp.single_apply] at hi
    split_ifs at hi with h
    · rw [← h]; exact hQ₁ i
    · exact absurd rfl hi
  have hE₂T : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).filter (Psp.IsStrictFst α β hα hβ δ) = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact (not_isStrictFst_of_isStrictSnd Psp α β hα hβ δ) (hQ₂ j) hV
  have hE₁T' : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).filter (Psp.IsStrictSnd α β hα hβ δ) = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact (not_isStrictFst_of_isStrictSnd Psp α β hα hβ δ) hV (hQ₁ i)
  have hE₂T' : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).filter (Psp.IsStrictSnd α β hα hβ δ) =
      ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by
    rw [Finsupp.filter_eq_self_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply] at hV
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
    rw [Finsupp.single_apply] at hj
    split_ifs at hj with h
    · rw [← h]; exact hQ₂ j
    · exact absurd rfl hj
  have hbase₁ : Finsupp.mapDomain (Psp.reduceFst α hα) (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      ∑ i, Finsupp.single ((Psp.reduceFst α hα) (Q₁ i)) (1 : ℤ) := by
    rw [Finsupp.mapDomain_finset_sum]; simp only [Finsupp.mapDomain_single]
  have hbase₂ : Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      ∑ j, Finsupp.single ((Psp.reduceSnd β hβ δ) (Q₂ j)) (1 : ℤ) := by
    rw [Finsupp.mapDomain_finset_sum]; simp only [Finsupp.mapDomain_single]
  have hDfst : (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).filter (Psp.IsStrictFst α β hα hβ δ)
      = (Psp.fstDiv α β hα hβ δ) D := rfl
  have hDsnd : (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).filter (Psp.IsStrictSnd α β hα hβ δ)
      = (Psp.sndDiv α β hα hβ δ) D := rfl
  refine ⟨?_, ?_⟩
  ·
    ext v
    by_cases hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v
    · have lhs : Finsupp.mapDomain (Psp.reduceFst α hα) ((Psp.fstDiv α β hα hβ δ) E) v = 0 := by
        rw [mapDomain_apply_eq_sum]
        refine Finset.sum_eq_zero fun V hV => ?_
        rw [if_neg]
        rintro rfl
        rw [JHPlaceSpecialization.fstDiv, Finsupp.support_filter, Finset.mem_filter] at hV
        exact hV.2.2 hv
      have rhs : (∑ i, Finsupp.single ((Psp.reduceFst α hα) (Q₁ i)) (1 : ℤ)) v = 0 := by
        rw [Finsupp.finset_sum_apply]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact (hQ₁ i).2 hv
      rw [lhs, rhs]
    · have hlaw := hmodel.1 (c • f) hG₁ hG₂ hres₁ hres₂ _ hdivG v hv
      have hfilt : (Psp.fstDiv α β hα hβ δ) (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
          - (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) =
          (Psp.fstDiv α β hα hβ δ) E - ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) - (Psp.fstDiv α β hα hβ δ) D := by
        show Finsupp.filter (Psp.IsStrictFst α β hα hβ δ) _ = _
        rw [sub_eq_add_neg, sub_eq_add_neg, Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_neg,
          Finsupp.filter_neg, Finsupp.filter_add, hE₁T, hE₂T, add_zero, ← hDfst, ← sub_eq_add_neg,
          ← sub_eq_add_neg]
        rfl
      rw [hfilt, Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
        hdiv₁' v, hbase₁] at hlaw
      have h0 : v.ord (Rpd.R₁.residue ⟨c • f, hG₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) + v.ord hb₁ = 0 := by
        rw [← v.ord_mul hres₁ hb₁0, ← hu₁]
        exact hordu₁ v
      omega
  ·
    ext v
    by_cases hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v
    · have lhs : Finsupp.mapDomain (Psp.reduceSnd β hβ δ) ((Psp.sndDiv α β hα hβ δ) E) v = 0 := by
        rw [mapDomain_apply_eq_sum]
        refine Finset.sum_eq_zero fun V hV => ?_
        rw [if_neg]
        rintro rfl
        rw [JHPlaceSpecialization.sndDiv, Finsupp.support_filter, Finset.mem_filter] at hV
        exact hV.2.2 hv
      have rhs : (∑ j, Finsupp.single ((Psp.reduceSnd β hβ δ) (Q₂ j)) (1 : ℤ)) v = 0 := by
        rw [Finsupp.finset_sum_apply]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact (hQ₂ j).2 hv
      rw [lhs, rhs]
    · have hlaw := hmodel.2.1 (c • f) hG₁ hG₂ hres₁ hres₂ _ hdivG v hv
      have hfilt : (Psp.sndDiv α β hα hβ δ) (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
          - (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) =
          (Psp.sndDiv α β hα hβ δ) E - ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) - (Psp.sndDiv α β hα hβ δ) D := by
        show Finsupp.filter (Psp.IsStrictSnd α β hα hβ δ) _ = _
        rw [sub_eq_add_neg, sub_eq_add_neg, Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_neg,
          Finsupp.filter_neg, Finsupp.filter_add, hE₁T', hE₂T', zero_add, ← hDsnd, ← sub_eq_add_neg,
          ← sub_eq_add_neg]
        rfl
      rw [hfilt, Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
        hdiv₂' v, hbase₂] at hlaw
      have h0 : v.ord (Rpd.R₂.residue ⟨c • f, hG₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) + v.ord hb₂ = 0 := by
        rw [← v.ord_mul hres₂ hb₂0, ← hu₂]
        exact hordu₂ v
      omega

end CanonRepH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp.EffH"

open CanonRepH in
open Classical in
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
    {T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁ i) = v) (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, Psp.reduceSnd β hβ δ (Q₂ j) = v)
    (hT₁W : Disjoint T₁ (SS.image Prod.fst))
    (hT₁aff : ∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hT₂aff : ∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
    (hgp₁ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ (SS.image Prod.fst), w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : (ResidueField ↥A), h = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hgood : Psp.IsGoodDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
    (hadm : Psp.glueData α β hα hβ δ SS (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS)
    (hmk : GluedPic0.mk SS ⟨Psp.glueData α β hα hβ δ SS (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁' i)) ∧ (∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂' j)) ∧
      (∀ i, Psp.reduceFst α hα (Q₁' i) = Psp.reduceFst α hα (Q₁ i)) ∧
      (∀ j, Psp.reduceSnd β hβ δ (Q₂' j) = Psp.reduceSnd β hβ δ (Q₂ j)) ∧
      ∃ hdeg0 : ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        Pic0.mk ⟨_, hdeg0⟩ = Pic0.mk D := by
  classical

  obtain ⟨tj, htr, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v

  have hE₀deg : Divisor.degree (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))
      (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) = ((d₁ + d₂ : ℕ) : ℤ) := by
    rw [map_add, map_sum, map_sum]
    simp only [Divisor.degree_single, hdeg1, Nat.cast_one,
      mul_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring

  obtain ⟨E, hE0, hEdeg, hEdz, hEx⟩ :=
    effH M H
      (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      (by rw [hE₀deg]; exact_mod_cast hdeg.ge) (Pic0.mk D)

  have hprin : (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) ∈
      Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
    have h := hEx
    rw [Pic0.mk, Pic0.mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have h' : -(E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)))
        + (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈
        Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := h
    have := neg_mem h'
    convert this using 1
    abel
  obtain ⟨f, hf0, hdivf⟩ := hprin

  have hSPB := fun {d₁ d₂ : ℕ} => @ModularCurve.JHPlaceSpecialization.ProlongationDatum.sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp
    p M _ _ H hpM hpM2 hHp _ A hA _ _ θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit hcusp d₁ d₂
  obtain ⟨hpush₁, hpush₂⟩ := mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq hSS hTD hmodel hRL hSPB Q₁ Q₂ hQ₁ hQ₂
    hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hgp₁ hgp₂ E hE0 D hgood hadm hmk f hf0 hdivf

  have hEdeg' : Divisor.degree (K := AlgebraicClosure ℚ) E = ((d₁ + d₂ : ℕ) : ℤ) := hEdeg.trans hE₀deg
  obtain ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, hEQ⟩ :=
    exists_eq_sum_add_sum_of_mapDomain_fstDiv_sndDiv Psp α β hα hβ δ E hE0 Q₁ Q₂ hinj₁ hinj₂ hpush₁ hpush₂ hdeg1 hEdeg'
  refine ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, ?_⟩
  have hdeg0 : (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
      - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
      Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈
        Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) := by
    rw [← hEQ]; exact hEdz
  refine ⟨hdeg0, ?_⟩
  have heq : (⟨_, hdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
      = ⟨E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)), hEdz⟩ := by
    apply Subtype.ext
    simp [hEQ]
  rw [heq]
  exact hEx

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp (solution)
