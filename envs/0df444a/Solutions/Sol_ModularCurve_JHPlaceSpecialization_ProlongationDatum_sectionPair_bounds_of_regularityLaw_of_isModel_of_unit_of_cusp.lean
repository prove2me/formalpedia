-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9396a034-6f65-52c2-be03-32bfd74ea98a

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

import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_oneSidedDivisorLaw_and_oneSidedCuspLaw_of_isModel_of_unit
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_fixed_of_mem_ssPlacesQExp
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp
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
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

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
    (E D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE : 0 ≤ E) (hD : Psp.IsGoodDiv α β hα hβ δ D)
    (G : ↥(xHFunctionFieldBar M H)) (h₁ : G ∈ Rpd.R₁.integers) (h₂ : G ∈ Rpd.R₂.integers)
    (hdiv : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V = V.ord G)
    (hb₁ hb₂ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hb₁0 : hb₁ ≠ 0) (hb₂0 : hb₂ ≠ 0)
    (hdiv₁ : ∀ v, Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) v = v.ord hb₁)
    (hdiv₂ : ∀ v, Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) v = v.ord hb₂)
    (hvals : ∀ s ∈ SS, ∃ c : (ResidueField ↥A), c ≠ 0 ∧ s.1.HasValue hb₁ c ∧ s.2.HasValue hb₂ c) :
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord ((Rpd.R₁.residue ⟨G, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁)) ∧
    (∀ v ∈ T₁, -1 ≤ v.ord ((Rpd.R₁.residue ⟨G, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁)) ∧
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord ((Rpd.R₂.residue ⟨G, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂)) ∧
    (∀ v ∈ T₂, -1 ≤ v.ord ((Rpd.R₂.residue ⟨G, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂)) ∧
    (∀ s ∈ SS, ∃ c : (ResidueField ↥A), s.1.HasValue ((Rpd.R₁.residue ⟨G, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁) c ∧ s.2.HasValue ((Rpd.R₂.residue ⟨G, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂) c) := by
  classical

  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), E₁ = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), E₂ = ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := ⟨_, rfl⟩
  rw [show (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = E₁ + E₂ by rw [hE₁, hE₂]] at hdiv
  have hE' : ∀ W, 0 ≤ E W := fun W => by simpa using Finsupp.le_def.mp hE W
  obtain ⟨φ, hφ⟩ : ∃ φ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), φ = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := ⟨_, rfl⟩
  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hc] at this
    rw [← this]; ring
  have hφinj : Function.Injective φ := by
    intro a b hab
    rw [hφ, qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul, qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul] at hab
    exact smul_left_cancel _ hab
  have hδinj : Function.Injective δ := by
    intro a b hab
    rw [hδ, hδ] at hab
    exact smul_left_cancel _ hab
  have hcomm : ∀ x, δ (φ x) = φ (δ x) := fun x => by
    rw [hδ, hδ, hφ]
    exact (qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) x).symm
  have hFixed_iff : ∀ x, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ x ↔ φ (δ (φ x)) = x := fun x => by rw [hφ]; exact Iff.rfl

  have hssFix : ∀ s ∈ SS, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ s.1 ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ s.2 := by
    intro s hs
    have hmem := (hSS s).mp hs
    rw [mem_ssNodePairsQExp_iff] at hmem
    have h1 : s.1 ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := by
      rw [hmem.2, ← ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)]
      exact Set.mem_image_of_mem _ hmem.1
    exact ⟨JHPlaceSpecialization.fixed_of_mem_ssPlacesQExp p M H hpM hpM2 A pb hpb δ hδ _ h1,
      JHPlaceSpecialization.fixed_of_mem_ssPlacesQExp p M H hpM hpM2 A pb hpb δ hδ _ hmem.1⟩

  have hnf₁ : ∀ V, (Psp.IsStrictFst α β hα hβ δ) V ∨ (Psp.IsStrictSnd α β hα hβ δ) V → ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((Psp.reduceFst α hα) V) := by
    rintro V (hV | hV)
    · exact hV.2
    · intro hfix
      apply hV.2
      rw [hFixed_iff] at hfix ⊢
      have h1 : Psp.reduceFst α hα V = φ (Psp.reduceSnd β hβ δ V) := by rw [hφ]; exact hV.1
      rw [h1] at hfix
      have h2 := hφinj hfix
      rwa [hcomm] at h2
  have hnf₂ : ∀ V, (Psp.IsStrictFst α β hα hβ δ) V ∨ (Psp.IsStrictSnd α β hα hβ δ) V → ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((Psp.reduceSnd β hβ δ) V) := by
    rintro V (hV | hV)
    · intro hfix
      apply hV.2
      rw [hFixed_iff] at hfix ⊢
      have h1 : Psp.reduceSnd β hβ δ V = δ (φ (Psp.reduceFst α hα V)) := by rw [hφ]; exact hV.1.symm
      rw [h1] at hfix

      simp only [hcomm] at hfix
      have h2 := hφinj hfix
      rw [← hcomm, ← hcomm] at h2
      have h3 := hδinj h2
      simp only [hcomm]
      exact h3
    · exact hV.2
  have hexcl : ∀ V, (Psp.IsStrictFst α β hα hβ δ) V → (Psp.IsStrictSnd α β hα hβ δ) V → False := by
    intro V h1 h2
    apply h1.2
    show qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V))) = Psp.reduceFst α hα V
    rw [h1.1]
    exact h2.1.symm

  have hE₁apply : ∀ V, E₁ V = ∑ i, if Q₁ i = V then (1 : ℤ) else 0 := fun V => by
    rw [hE₁, Finsupp.finset_sum_apply]; simp only [Finsupp.single_apply]
  have hE₂apply : ∀ V, E₂ V = ∑ j, if Q₂ j = V then (1 : ℤ) else 0 := fun V => by
    rw [hE₂, Finsupp.finset_sum_apply]; simp only [Finsupp.single_apply]
  have hE₁zero : ∀ V, (∀ i, Q₁ i ≠ V) → E₁ V = 0 := fun V h => by
    rw [hE₁apply]; exact Finset.sum_eq_zero fun i _ => if_neg (h i)
  have hE₂zero : ∀ V, (∀ j, Q₂ j ≠ V) → E₂ V = 0 := fun V h => by
    rw [hE₂apply]; exact Finset.sum_eq_zero fun j _ => if_neg (h j)
  have hE₁strict : ∀ V, E₁ V ≠ 0 → (Psp.IsStrictFst α β hα hβ δ) V := fun V hV => by
    by_contra h; exact hV (hE₁zero V fun i hi => h (hi ▸ hQ₁ i))
  have hE₂strict : ∀ V, E₂ V ≠ 0 → (Psp.IsStrictSnd α β hα hβ δ) V := fun V hV => by
    by_contra h; exact hV (hE₂zero V fun j hj => h (hj ▸ hQ₂ j))
  have hE₀strict : ∀ V, (E₁ + E₂) V ≠ 0 → (Psp.IsStrictFst α β hα hβ δ) V ∨ (Psp.IsStrictSnd α β hα hβ δ) V := by
    intro V hV
    rw [Finsupp.add_apply] at hV
    by_cases h1 : E₁ V = 0
    · rw [h1, zero_add] at hV; exact Or.inr (hE₂strict V hV)
    · exact Or.inl (hE₁strict V h1)
  have hDstrict : ∀ V, D V ≠ 0 → (Psp.IsStrictFst α β hα hβ δ) V ∨ (Psp.IsStrictSnd α β hα hβ δ) V :=
    fun V hV => hD V (Finsupp.mem_support_iff.mpr hV)
  have hE₁T1 : E₁.filter (Psp.IsStrictFst α β hα hβ δ) = E₁ := by
    rw [Finsupp.filter_eq_self_iff]; exact hE₁strict
  have hE₂T2 : E₂.filter (Psp.IsStrictSnd α β hα hβ δ) = E₂ := by
    rw [Finsupp.filter_eq_self_iff]; exact hE₂strict
  have hE₂T1 : E₂.filter (Psp.IsStrictFst α β hα hβ δ) = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV; by_contra h; exact hexcl V hV (hE₂strict V h)
  have hE₁T2 : E₁.filter (Psp.IsStrictSnd α β hα hβ δ) = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV; by_contra h; exact hexcl V (hE₁strict V h) hV

  have hfix₁ : ∀ V, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((Psp.reduceFst α hα) V) → (E₁ + E₂) V = 0 ∧ D V = 0 := by
    intro V hV
    exact ⟨by_contra fun h => hnf₁ V (hE₀strict V h) hV, by_contra fun h => hnf₁ V (hDstrict V h) hV⟩
  have hfix₂ : ∀ V, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((Psp.reduceSnd β hβ δ) V) → (E₁ + E₂) V = 0 ∧ D V = 0 := by
    intro V hV
    exact ⟨by_contra fun h => hnf₂ V (hE₀strict V h) hV, by_contra fun h => hnf₂ V (hDstrict V h) hV⟩
  have hGreg₁ : ∀ V, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((Psp.reduceFst α hα) V) → 0 ≤ V.ord G := by
    intro V hV
    rw [← hdiv V, Finsupp.sub_apply, Finsupp.sub_apply, (hfix₁ V hV).1, (hfix₁ V hV).2,
      sub_zero, sub_zero]
    exact hE' V

  have mapDomain_nonneg : ∀ (g : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →
        Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
      (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), (∀ V, 0 ≤ X V) →
      ∀ v, 0 ≤ Finsupp.mapDomain g X v := by
    intro g X hX v
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    exact Finset.sum_nonneg fun V _ => by
      simp only [Finsupp.single_apply]
      split_ifs
      · exact hX V
      · exact le_rfl
  have mapDomain_eq_zero : ∀ (g : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →
        Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
      (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
      (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      (∀ V, X V ≠ 0 → g V ≠ v) → Finsupp.mapDomain g X v = 0 := by
    intro g X v h
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    exact Finset.sum_eq_zero fun V hV => by
      simp only [Finsupp.single_apply]
      exact if_neg (h V (Finsupp.mem_support_iff.mp hV))
  have hfilter_nonneg : ∀ (p : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → Prop)
      [DecidablePred p] (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      0 ≤ (E.filter p) V := by
    intro p _ V
    rw [Finsupp.filter_apply]
    split_ifs
    · exact hE' V
    · exact le_rfl
  have filter_ne_zero : ∀ (p : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → Prop)
      [DecidablePred p] (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (V),
      (X.filter p) V ≠ 0 → X V ≠ 0 := by
    intro p _ X V h hX
    apply h
    rw [Finsupp.filter_apply, hX, ite_self]

  have hEbar₁ : ∀ v, Finsupp.mapDomain (Psp.reduceFst α hα) E₁ v =
      ∑ i, if (Psp.reduceFst α hα) (Q₁ i) = v then (1 : ℤ) else 0 := by
    intro v
    rw [hE₁, Finsupp.mapDomain_finset_sum, Finsupp.finset_sum_apply]
    simp only [Finsupp.mapDomain_single, Finsupp.single_apply]
  have hEbar₂ : ∀ v, Finsupp.mapDomain (Psp.reduceSnd β hβ δ) E₂ v =
      ∑ j, if (Psp.reduceSnd β hβ δ) (Q₂ j) = v then (1 : ℤ) else 0 := by
    intro v
    rw [hE₂, Finsupp.mapDomain_finset_sum, Finsupp.finset_sum_apply]
    simp only [Finsupp.mapDomain_single, Finsupp.single_apply]
  have hEbar₁_nn : ∀ v, 0 ≤ Finsupp.mapDomain (Psp.reduceFst α hα) E₁ v := fun v => by
    rw [hEbar₁]; exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hEbar₂_nn : ∀ v, 0 ≤ Finsupp.mapDomain (Psp.reduceSnd β hβ δ) E₂ v := fun v => by
    rw [hEbar₂]; exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  have hEbar₁_off : ∀ v, v ∉ T₁ → Finsupp.mapDomain (Psp.reduceFst α hα) E₁ v = 0 := fun v hv => by
    rw [hEbar₁]; exact Finset.sum_eq_zero fun i _ => if_neg fun h => hv ((hT₁ v).mpr ⟨i, h⟩)
  have hEbar₂_off : ∀ v, v ∉ T₂ → Finsupp.mapDomain (Psp.reduceSnd β hβ δ) E₂ v = 0 := fun v hv => by
    rw [hEbar₂]; exact Finset.sum_eq_zero fun j _ => if_neg fun h => hv ((hT₂ v).mpr ⟨j, h⟩)
  have hEbar₁_le : ∀ v, Finsupp.mapDomain (Psp.reduceFst α hα) E₁ v ≤ 1 := by
    intro v
    rw [hEbar₁]
    by_cases hv : ∃ i, (Psp.reduceFst α hα) (Q₁ i) = v
    · obtain ⟨i, hi⟩ := hv
      rw [Finset.sum_eq_single i (fun j _ hji => if_neg fun h => hji (hinj₁ (h.trans hi.symm)))
        (fun h => absurd (Finset.mem_univ i) h), if_pos hi]
    · push Not at hv
      rw [Finset.sum_eq_zero fun i _ => if_neg (hv i)]; norm_num
  have hEbar₂_le : ∀ v, Finsupp.mapDomain (Psp.reduceSnd β hβ δ) E₂ v ≤ 1 := by
    intro v
    rw [hEbar₂]
    by_cases hv : ∃ j, (Psp.reduceSnd β hβ δ) (Q₂ j) = v
    · obtain ⟨j, hj⟩ := hv
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg fun h => hij (hinj₂ (h.trans hj.symm)))
        (fun h => absurd (Finset.mem_univ j) h), if_pos hj]
    · push Not at hv
      rw [Finset.sum_eq_zero fun j _ => if_neg (hv j)]; norm_num

  have hfst0 : ∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → Finsupp.mapDomain (Psp.reduceFst α hα) ((Psp.fstDiv α β hα hβ δ) D) v = 0 := by
    intro v hv
    apply mapDomain_eq_zero
    intro V hV hVv
    rw [JHPlaceSpecialization.fstDiv, Finsupp.filter_apply] at hV
    split_ifs at hV with hT
    · exact hT.2 (by rw [hVv]; exact hv)
    · exact hV rfl
  have hsnd0 : ∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → Finsupp.mapDomain (Psp.reduceSnd β hβ δ) ((Psp.sndDiv α β hα hβ δ) D) v = 0 := by
    intro v hv
    apply mapDomain_eq_zero
    intro V hV hVv
    rw [JHPlaceSpecialization.sndDiv, Finsupp.filter_apply] at hV
    split_ifs at hV with hT
    · exact hT.2 (by rw [hVv]; exact hv)
    · exact hV rfl

  obtain ⟨hDF, hDS, hCI, hCZ⟩ := ModularCurve.JHPlaceSpecialization.ProlongationDatum.oneSidedDivisorLaw_and_oneSidedCuspLaw_of_isModel_of_unit
    p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hUnit

  have hdiv' : ∀ V, (E - (E₁ + E₂) - D) V = V.ord G := hdiv

  have key₁ : Rpd.R₁.residue ⟨G, h₁⟩ ≠ 0 → ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      -Finsupp.mapDomain (Psp.reduceFst α hα) E₁ v ≤ v.ord (Rpd.R₁.residue ⟨G, h₁⟩ * hb₁) := by
    intro hr v
    rw [v.ord_mul hr hb₁0, ← hdiv₁ v]
    by_cases hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v
    ·
      rw [hfst0 v hv, add_zero]
      refine le_trans (neg_nonpos.mpr (hEbar₁_nn v)) ?_
      by_cases haff : JHPlaceSpecialization.IsAffinePlace p M H hpM A v
      ·
        exact (hRL.1 G h₁ h₂ v hv haff (fun V hV => hGreg₁ V (by rw [hV]; exact hv))).1 hr
      ·
        obtain ⟨⟨C, hC, hCv⟩, -⟩ := hcusp v haff
        have hlaw := hCI G h₁ hr (E - (E₁ + E₂) - D) hdiv' C hC
        rw [hCv] at hlaw
        rw [← hlaw, Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.mapDomain_sub,
          Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
          mapDomain_eq_zero (Psp.reduceFst α hα) ((E₁ + E₂).filter _) v
            (fun V hV hVv => hnf₁ V (hE₀strict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          mapDomain_eq_zero (Psp.reduceFst α hα) (D.filter _) v
            (fun V hV hVv => hnf₁ V (hDstrict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          sub_zero, sub_zero]
        exact mapDomain_nonneg _ _ (hfilter_nonneg _) _
    ·
      have hlaw := hDF G h₁ hr (E - (E₁ + E₂) - D) hdiv' v hv
      rw [← hlaw]
      simp only [JHPlaceSpecialization.fstDiv]
      rw [← Finsupp.add_apply,
        ← Finsupp.mapDomain_add, ← Finsupp.filter_add, sub_add_cancel, Finsupp.filter_sub,
        Finsupp.filter_add, hE₁T1, hE₂T1, add_zero, Finsupp.mapDomain_sub, Finsupp.sub_apply]
      linarith [mapDomain_nonneg (Psp.reduceFst α hα) (E.filter (Psp.IsStrictFst α β hα hβ δ)) (hfilter_nonneg _) v]

  have key₂ : Rpd.R₂.residue ⟨G, h₂⟩ ≠ 0 → ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      -Finsupp.mapDomain (Psp.reduceSnd β hβ δ) E₂ v ≤ v.ord (Rpd.R₂.residue ⟨G, h₂⟩ * hb₂) := by
    intro hr v
    rw [v.ord_mul hr hb₂0, ← hdiv₂ v]
    by_cases hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v
    · rw [hsnd0 v hv, add_zero]
      refine le_trans (neg_nonpos.mpr (hEbar₂_nn v)) ?_
      by_cases haff : JHPlaceSpecialization.IsAffinePlace p M H hpM A v
      ·
        have hv' : δ (φ (φ v)) = v := by
          have := (hFixed_iff v).mp hv
          rwa [← hcomm] at this
        have hu : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (φ v) := by
          rw [hFixed_iff, hv']
        have huaff : JHPlaceSpecialization.IsAffinePlace p M H hpM A (φ v) := by
          rw [hφ]; exact (JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL p M H hpM A hA).1 v haff
        have h := (hRL.1 G h₁ h₂ (φ v) hu huaff (fun V hV => hGreg₁ V (by rw [hV]; exact hu))).2 hr
        have e : qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (φ v) = φ (φ v) := by rw [hφ]
        rwa [e, hv'] at h
      ·
        obtain ⟨-, ⟨C, hC, hCv⟩⟩ := hcusp v haff
        have hlaw := hCZ G h₂ hr (E - (E₁ + E₂) - D) hdiv' C hC
        rw [hCv] at hlaw
        rw [← hlaw, Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.mapDomain_sub,
          Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
          mapDomain_eq_zero (Psp.reduceSnd β hβ δ) ((E₁ + E₂).filter _) v
            (fun V hV hVv => hnf₂ V (hE₀strict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          mapDomain_eq_zero (Psp.reduceSnd β hβ δ) (D.filter _) v
            (fun V hV hVv => hnf₂ V (hDstrict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          sub_zero, sub_zero]
        exact mapDomain_nonneg _ _ (hfilter_nonneg _) _
    · have hlaw := hDS G h₂ hr (E - (E₁ + E₂) - D) hdiv' v hv
      rw [← hlaw]
      simp only [JHPlaceSpecialization.sndDiv]
      rw [← Finsupp.add_apply,
        ← Finsupp.mapDomain_add, ← Finsupp.filter_add, sub_add_cancel, Finsupp.filter_sub,
        Finsupp.filter_add, hE₁T2, hE₂T2, zero_add, Finsupp.mapDomain_sub, Finsupp.sub_apply]
      linarith [mapDomain_nonneg (Psp.reduceSnd β hβ δ) (E.filter (Psp.IsStrictSnd α β hα hβ δ)) (hfilter_nonneg _) v]

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    by_cases hr : Rpd.R₁.residue ⟨G, h₁⟩ = 0
    · simp only [hr, zero_mul, Place.ord_zero, le_refl]
    · have h := key₁ hr v
      rw [hEbar₁_off v hv, neg_zero] at h
      exact h
  · intro v hv
    by_cases hr : Rpd.R₁.residue ⟨G, h₁⟩ = 0
    · simp only [hr, zero_mul, Place.ord_zero]; norm_num
    · exact le_trans (by linarith [hEbar₁_le v]) (key₁ hr v)
  · intro v hv
    by_cases hr : Rpd.R₂.residue ⟨G, h₂⟩ = 0
    · simp only [hr, zero_mul, Place.ord_zero, le_refl]
    · have h := key₂ hr v
      rw [hEbar₂_off v hv, neg_zero] at h
      exact h
  · intro v hv
    by_cases hr : Rpd.R₂.residue ⟨G, h₂⟩ = 0
    · simp only [hr, zero_mul, Place.ord_zero]; norm_num
    · exact le_trans (by linarith [hEbar₂_le v]) (key₂ hr v)
  ·
    intro s hs
    obtain ⟨c, hc₁, hc₂⟩ := hRL.2 G h₁ h₂ s hs (fun V hV => hGreg₁ V (by rw [hV]; exact (hssFix s hs).1))
    obtain ⟨c', -, hw₁, hw₂⟩ := hvals s hs
    exact ⟨c * c', hc₁.mul hw₁, hc₂.mul hw₂⟩

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp (solution)
