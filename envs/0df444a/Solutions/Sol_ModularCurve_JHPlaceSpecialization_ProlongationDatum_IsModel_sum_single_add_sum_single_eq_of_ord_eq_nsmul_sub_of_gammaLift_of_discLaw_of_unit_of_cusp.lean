-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/57b2190e-88be-5846-b4de-963e7f1f6f1a

import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_fixed_of_mem_ssPlacesQExp
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_smul_mem_integers_residue_ne_zero_of_isGoodDiv_of_admissible_of_unit_of_cusp
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.XHDRModelAtP.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

set_option quotPrecheck false
set_option hygiene false in
local notation "κ" => ResidueField ↥A
set_option hygiene false in
local notation "FM" => ↥(xHFunctionFieldBar M H)
set_option hygiene false in
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
set_option hygiene false in
local notation "Φ" => qExpFrobeniusPlaceModL (ResidueField ↥A) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) p
set_option hygiene false in
local notation "FixedH" => JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A)
set_option hygiene false in
local notation "AffH" => JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)

namespace RigidityH

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

theorem ord_smul {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Algebra.smul_def, v.ord_mul ((_root_.map_ne_zero _).mpr hc) hx, ord_algebraMap' v hc, zero_add]

theorem HasValue.smul {g : F} {a : K} (h : v.HasValue g a) (c : K) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]; exact (v.hasValue_algebraMap c).mul h

theorem eq_of_hasValue_algebraMap {c a : K} (h : v.HasValue (algebraMap K F c) a) : a = c :=
  h.unique (v.hasValue_algebraMap c)

theorem mapDomain_apply_eq_zero {ι ι' : Type*} (f : ι → ι') (D : ι →₀ ℤ) (w : ι')
    (h : ∀ i, f i = w → D i = 0) : Finsupp.mapDomain f D w = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Finsupp.single_apply]
  split_ifs with hi
  · exact h i hi
  · rfl

end PlaceHelpers

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

theorem fixed_frob_iff (δ : Place κ Fb → Place κ Fb)
    (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hΦ : Function.Injective Φ) (v : Place κ Fb) :
    FixedH δ (Φ v) ↔ FixedH δ v := by
  unfold JHPlaceSpecialization.Fixed
  rw [← hcomm (Φ v)]
  exact hΦ.eq_iff

theorem fixed_delta_iff (δ : Place κ Fb → Place κ Fb)
    (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hδ : Function.Injective δ) (v : Place κ Fb) :
    FixedH δ (δ v) ↔ FixedH δ v := by
  unfold JHPlaceSpecialization.Fixed
  rw [hcomm v, hcomm (δ (Φ v))]
  exact hδ.eq_iff

section Frame

variable {Psp : JHPlaceSpecialization p M H hpM A} {θ : FM ≃ₐ[AlgebraicClosure ℚ] FM}
  {α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] FM}
  {hα : α.IsIntegral} {hβ : β.IsIntegral} {δ : Place κ Fb → Place κ Fb}

theorem not_isStrictSnd_of_isStrictFst (hcomm : ∀ v, Φ (δ v) = δ (Φ v))
    {W : Place (AlgebraicClosure ℚ) FM} (h : Psp.IsStrictFst α β hα hβ δ W) : ¬ Psp.IsStrictSnd α β hα hβ δ W := by
  rintro ⟨h1, h2⟩
  apply h2
  show Φ (δ (Φ (Psp.reduceSnd β hβ δ W))) = Psp.reduceSnd β hβ δ W
  rw [hcomm, ← h1]
  exact h.1

theorem good_apply_eq_zero_of_fixed_fst (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hΦ : Function.Injective Φ)
    (D : Divisor (AlgebraicClosure ℚ) FM) (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (V' : Place (AlgebraicClosure ℚ) FM) (hfix : FixedH δ (Psp.reduceFst α hα V')) : D V' = 0 := by
  by_contra hne
  rcases hgood V' (Finsupp.mem_support_iff.mpr hne) with hst | hst
  · exact hst.2 hfix
  · rw [hst.1, fixed_frob_iff δ hcomm hΦ] at hfix
    exact hst.2 hfix

theorem good_apply_eq_zero_of_fixed_snd (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hΦ : Function.Injective Φ)
    (hδi : Function.Injective δ)
    (D : Divisor (AlgebraicClosure ℚ) FM) (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (V' : Place (AlgebraicClosure ℚ) FM) (hfix : FixedH δ (Psp.reduceSnd β hβ δ V')) : D V' = 0 := by
  by_contra hne
  rcases hgood V' (Finsupp.mem_support_iff.mpr hne) with hst | hst
  · rw [← hst.1, fixed_delta_iff δ hcomm hδi, fixed_frob_iff δ hcomm hΦ] at hfix
    exact hst.2 hfix
  · exact hst.2 hfix

theorem bookkeeping (hcomm : ∀ v, Φ (δ v) = δ (Φ v))
    {d₁ d₂ : ℕ} (Q₁ Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) FM) (Q₂ Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) FM)
    (hQ₁ : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁ i)) (hQ₁' : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁' i))
    (hQ₂ : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂ j)) (hQ₂' : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂' j))
    (hred₁ : ∀ i, Psp.reduceFst α hα (Q₁' i) = Psp.reduceFst α hα (Q₁ i))
    (hred₂ : ∀ j, Psp.reduceSnd β hβ δ (Q₂' j) = Psp.reduceSnd β hβ δ (Q₂ j))
    (n : ℕ) (D : Divisor (AlgebraicClosure ℚ) FM)
    (hD : D = (n : ℤ) • ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)))) :
    (∀ V, D V ≠ 0 → ((∃ i, V = Q₁ i) ∨ (∃ i, V = Q₁' i)) ∨ ((∃ j, V = Q₂ j) ∨ (∃ j, V = Q₂' j))) ∧
    Psp.IsGoodDiv α β hα hβ δ D ∧
    Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) = 0 ∧
    Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) = 0 := by
  obtain ⟨E₁, hE₁⟩ : ∃ E : Divisor (AlgebraicClosure ℚ) FM, E = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) := ⟨_, rfl⟩
  obtain ⟨E₁', hE₁'⟩ : ∃ E : Divisor (AlgebraicClosure ℚ) FM, E = ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E : Divisor (AlgebraicClosure ℚ) FM, E = ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := ⟨_, rfl⟩
  obtain ⟨E₂', hE₂'⟩ : ∃ E : Divisor (AlgebraicClosure ℚ) FM, E = ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) := ⟨_, rfl⟩
  have hDE : D = (n : ℤ) • ((E₁' + E₂') - (E₁ + E₂)) := by rw [hD, hE₁, hE₁', hE₂, hE₂']
  have hE₁_apply : ∀ V, E₁ V = ∑ i, if Q₁ i = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₁, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hE₁'_apply : ∀ V, E₁' V = ∑ i, if Q₁' i = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₁', Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hE₂_apply : ∀ V, E₂ V = ∑ j, if Q₂ j = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₂, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hE₂'_apply : ∀ V, E₂' V = ∑ j, if Q₂' j = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₂', Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hD_apply : ∀ V, D V = (n : ℤ) * ((E₁' V + E₂' V) - (E₁ V + E₂ V)) := fun V => by
    rw [hDE, Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.add_apply, smul_eq_mul]
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
  have hgood : Psp.IsGoodDiv α β hα hβ δ D := fun V hV => htype V (Finsupp.mem_support_iff.mp hV)
  have hE₂_fst : ∀ V, Psp.IsStrictFst α β hα hβ δ V → E₂ V = 0 := fun V hV =>
    hE₂_off V fun j h => not_isStrictSnd_of_isStrictFst hcomm hV (h ▸ hQ₂ j)
  have hE₂'_fst : ∀ V, Psp.IsStrictFst α β hα hβ δ V → E₂' V = 0 := fun V hV =>
    hE₂'_off V fun j h => not_isStrictSnd_of_isStrictFst hcomm hV (h ▸ hQ₂' j)
  have hE₁_snd : ∀ V, Psp.IsStrictSnd α β hα hβ δ V → E₁ V = 0 := fun V hV =>
    hE₁_off V fun i h => not_isStrictSnd_of_isStrictFst hcomm (h ▸ hQ₁ i) hV
  have hE₁'_snd : ∀ V, Psp.IsStrictSnd α β hα hβ δ V → E₁' V = 0 := fun V hV =>
    hE₁'_off V fun i h => not_isStrictSnd_of_isStrictFst hcomm (h ▸ hQ₁' i) hV
  have hE₁_nfst : ∀ V, ¬ Psp.IsStrictFst α β hα hβ δ V → E₁ V = 0 := fun V hV =>
    hE₁_off V fun i h => hV (h ▸ hQ₁ i)
  have hE₁'_nfst : ∀ V, ¬ Psp.IsStrictFst α β hα hβ δ V → E₁' V = 0 := fun V hV =>
    hE₁'_off V fun i h => hV (h ▸ hQ₁' i)
  have hE₂_nsnd : ∀ V, ¬ Psp.IsStrictSnd α β hα hβ δ V → E₂ V = 0 := fun V hV =>
    hE₂_off V fun j h => hV (h ▸ hQ₂ j)
  have hE₂'_nsnd : ∀ V, ¬ Psp.IsStrictSnd α β hα hβ δ V → E₂' V = 0 := fun V hV =>
    hE₂'_off V fun j h => hV (h ▸ hQ₂' j)
  have hfst : Psp.fstDiv α β hα hβ δ D = (n : ℤ) • (E₁' - E₁) := by
    ext V
    show (D.filter (Psp.IsStrictFst α β hα hβ δ)) V = ((n : ℤ) • (E₁' - E₁)) V
    rw [Finsupp.filter_apply]
    by_cases hV : Psp.IsStrictFst α β hα hβ δ V
    · rw [if_pos hV, hD_apply, hE₂_fst V hV, hE₂'_fst V hV]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]; ring
    · rw [if_neg hV]
      simp [Finsupp.smul_apply, Finsupp.sub_apply, hE₁_nfst V hV, hE₁'_nfst V hV]
  have hsnd : Psp.sndDiv α β hα hβ δ D = (n : ℤ) • (E₂' - E₂) := by
    ext V
    show (D.filter (Psp.IsStrictSnd α β hα hβ δ)) V = ((n : ℤ) • (E₂' - E₂)) V
    rw [Finsupp.filter_apply]
    by_cases hV : Psp.IsStrictSnd α β hα hβ δ V
    · rw [if_pos hV, hD_apply, hE₁_snd V hV, hE₁'_snd V hV]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]; ring
    · rw [if_neg hV]
      simp [Finsupp.smul_apply, Finsupp.sub_apply, hE₂_nsnd V hV, hE₂'_nsnd V hV]
  have hmapE₁ : Finsupp.mapDomain (Psp.reduceFst α hα) E₁' = Finsupp.mapDomain (Psp.reduceFst α hα) E₁ := by
    show Finsupp.mapDomain.addMonoidHom (Psp.reduceFst α hα) E₁' = Finsupp.mapDomain.addMonoidHom (Psp.reduceFst α hα) E₁
    rw [hE₁', hE₁, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, hred₁ i]
  have hmapE₂ : Finsupp.mapDomain (Psp.reduceSnd β hβ δ) E₂' = Finsupp.mapDomain (Psp.reduceSnd β hβ δ) E₂ := by
    show Finsupp.mapDomain.addMonoidHom (Psp.reduceSnd β hβ δ) E₂' = Finsupp.mapDomain.addMonoidHom (Psp.reduceSnd β hβ δ) E₂
    rw [hE₂', hE₂, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, hred₂ j]
  refine ⟨hsupp, hgood, ?_, ?_⟩
  · rw [hfst, Finsupp.mapDomain_smul, Finsupp.mapDomain_sub, hmapE₁, sub_self, smul_zero]
  · rw [hsnd, Finsupp.mapDomain_smul, Finsupp.mapDomain_sub, hmapE₂, sub_self, smul_zero]

theorem residues_regular (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hΦ : Function.Injective Φ) (hδi : Function.Injective δ)
    (haffΦ : ∀ v : Place κ Fb, AffH v → AffH (Φ v))
    (SS : Finset (Place κ Fb × Place κ Fb)) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hRL : Rpd.RegularityLaw α β hα hβ δ SS)
    (hcusp : ∀ w : Place κ Fb, ¬ AffH w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))
    (D : Divisor (AlgebraicClosure ℚ) FM) (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (hmapFst : Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) = 0)
    (hmapSnd : Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) = 0)
    (f₁ : FM) (h₁ : f₁ ∈ Rpd.R₁.integers) (h₂ : f₁ ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨f₁, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨f₁, h₂⟩ ≠ 0)
    (hDf₁ : ∀ V, D V = V.ord f₁) :
    (∀ v : Place κ Fb, 0 ≤ v.ord (Rpd.R₁.residue ⟨f₁, h₁⟩ : Fb)) ∧
    (∀ v : Place κ Fb, 0 ≤ v.ord (Rpd.R₂.residue ⟨f₁, h₂⟩ : Fb)) := by
  have hnopole₁ : ∀ v : Place κ Fb, FixedH δ v → ∀ V : Place (AlgebraicClosure ℚ) FM, Psp.reduceFst α hα V = v → 0 ≤ V.ord f₁ := by
    intro v hv V hVv
    have h0 := good_apply_eq_zero_of_fixed_fst hcomm hΦ D hgood V (by rw [hVv]; exact hv)
    rw [hDf₁] at h0
    exact le_of_eq h0.symm
  constructor
  · intro v
    by_cases hv : FixedH δ v
    · by_cases haff : AffH v
      · exact (hRL.1 f₁ h₁ h₂ v hv haff (hnopole₁ v hv)).1 hr₁
      · obtain ⟨C, hC, hCv⟩ := (hcusp v haff).1
        have key := hmodel.2.2.1 f₁ h₁ h₂ hr₁ hr₂ D hDf₁ C hC
        rw [hCv] at key
        have hz : Finsupp.mapDomain (Psp.reduceFst α hα)
            (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) v = 0 :=
          mapDomain_apply_eq_zero _ _ _ fun V hV => by
            rw [Finsupp.filter_apply]
            split_ifs
            · exact good_apply_eq_zero_of_fixed_fst hcomm hΦ D hgood V (by rw [hV]; exact hv)
            · rfl
        rw [← key, hz]
    · have key := hmodel.1 f₁ h₁ h₂ hr₁ hr₂ D hDf₁ v hv
      rw [hmapFst, Finsupp.zero_apply] at key
      exact le_of_eq key
  · intro v
    by_cases hv : FixedH δ v
    · by_cases haff : AffH v
      · have hvfix' : FixedH δ (Φ v) := (fixed_frob_iff δ hcomm hΦ v).mpr hv
        have hvw : δ (Φ (Φ v)) = v := by
          rw [← hcomm (Φ v)]
          exact hv
        have key := (hRL.1 f₁ h₁ h₂ (Φ v) hvfix' (haffΦ v haff) (hnopole₁ (Φ v) hvfix')).2 hr₂
        rwa [hvw] at key
      · obtain ⟨C, hC, hCv⟩ := (hcusp v haff).2
        have key := hmodel.2.2.2 f₁ h₁ h₂ hr₁ hr₂ D hDf₁ C hC
        rw [hCv] at key
        have hz : Finsupp.mapDomain (Psp.reduceSnd β hβ δ)
            (D.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) v = 0 :=
          mapDomain_apply_eq_zero _ _ _ fun V hV => by
            rw [Finsupp.filter_apply]
            split_ifs
            · exact good_apply_eq_zero_of_fixed_snd hcomm hΦ hδi D hgood V (by rw [hV]; exact hv)
            · rfl
        rw [← key, hz]
    · have key := hmodel.2.1 f₁ h₁ h₂ hr₁ hr₂ D hDf₁ v hv
      rw [hmapSnd, Finsupp.zero_apply] at key
      exact le_of_eq key

end Frame

end RigidityH

open RigidityH in
set_option maxHeartbeats 3200000 in

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
    (n : ℕ) (hn : (n : (ResidueField ↥A)) ≠ 0) (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord f = (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V)) :
    (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by

  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hk] at this
    rw [← this]; ring
  have hcomm : ∀ v, Φ (δ v) = δ (Φ v) := by
    intro v
    rw [hδ v, hδ (Φ v)]
    exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
      (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) v
  have hδi : Function.Injective δ := fun v w hvw => by
    rw [hδ v, hδ w] at hvw
    exact MulAction.injective _ hvw
  have hΦ : Function.Injective Φ :=
    (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1
  have haffΦ := (JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    p M H hpM A hA).1
  have hssfix : ∀ y, y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p → FixedH δ y :=
    fun y hy => ModularCurve.JHPlaceSpecialization.fixed_of_mem_ssPlacesQExp p M H hpM hpM2 A pb hpb δ hδ y hy

  obtain ⟨D, hD_def⟩ : ∃ D : Divisor (AlgebraicClosure ℚ) FM, D =
    (n : ℤ) • ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
      - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))) := ⟨_, rfl⟩
  have hD : ∀ V, D V = V.ord f := fun V => by rw [hdiv V, hD_def, Finsupp.smul_apply, smul_eq_mul]
  obtain ⟨hsupp, hgood, hmapFst, hmapSnd⟩ :=
    bookkeeping hcomm Q₁ Q₁' Q₂ Q₂' hQ₁ hQ₁' hQ₂ hQ₂' hred₁ hred₂ n D hD_def
  have hadm : Psp.glueData α β hα hβ δ SS D ∈ GluingData.admissible SS := by
    have h0 : Psp.glueData α β hα hβ δ SS D = 0 := by
      unfold JHPlaceSpecialization.glueData
      rw [hmapFst, hmapSnd]; rfl
    rw [h0]; exact zero_mem _

  obtain ⟨c, hc0, hf₁₁, hf₁₂, hr₁, hr₂⟩ := ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_smul_mem_integers_residue_ne_zero_of_isGoodDiv_of_admissible_of_unit_of_cusp p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hUnit hcusp f hf D hD hgood hadm
  have hDf₁ : ∀ V, D V = V.ord (c • f) := fun V => by rw [ord_smul V hc0, hD]

  obtain ⟨hreg₁, hreg₂⟩ := residues_regular hcomm hΦ hδi haffΦ SS Rpd hmodel hRL hcusp D hgood hmapFst hmapSnd
    (c • f) hf₁₁ hf₁₂ hr₁ hr₂ hDf₁
  obtain ⟨κ₁, hκ₁⟩ := hgp₂ (Rpd.R₁.residue ⟨c • f, hf₁₁⟩ : Fb) (fun v _ => hreg₁ v)
    (fun v _ => le_trans (by norm_num) (hreg₁ v))
  obtain ⟨κ₂, hκ₂⟩ := hgp₂ (Rpd.R₂.residue ⟨c • f, hf₁₂⟩ : Fb) (fun v _ => hreg₂ v)
    (fun v _ => le_trans (by norm_num) (hreg₂ v))
  have hκ₁0 : κ₁ ≠ 0 := by
    intro h; apply hr₁; rw [hκ₁, h, map_zero]

  have hSSne : SS.Nonempty := by
    by_contra hSe
    rw [Finset.not_nonempty_iff_eq_empty] at hSe
    have h1 := hgp₁ 1 (fun v _ => by rw [Place.ord_one]) (fun v _ => by rw [Place.ord_one]; norm_num) (by simp [hSe])
    exact one_ne_zero h1
  obtain ⟨s, hs⟩ := hSSne
  have hκ : κ₂ = κ₁ := by
    obtain ⟨hy, hs1⟩ := (mem_ssNodePairsQExp_iff s).mp ((hSS s).mp hs)
    have hfix1 : FixedH δ s.1 := by
      rw [hs1]
      exact (fixed_frob_iff δ hcomm hΦ _).mpr (hssfix _ hy)
    have havoid : ∀ V : Place (AlgebraicClosure ℚ) FM, V.ord (c • f) ≠ 0 →
        ¬ (Psp.reduceFst α hα V = s.1 ∧ Psp.reduceSnd β hβ δ V = s.2) := by
      rintro V hV ⟨hV1, -⟩
      apply hV
      rw [← hDf₁]
      exact good_apply_eq_zero_of_fixed_fst hcomm hΦ D hgood V (by rw [hV1]; exact hfix1)
    obtain ⟨cc, -, hcc₁, hcc₂⟩ := hNV (c • f) hf₁₁ hf₁₂ hr₁ hr₂ s hs havoid
    rw [hκ₁] at hcc₁
    rw [hκ₂] at hcc₂
    rw [← eq_of_hasValue_algebraMap _ hcc₁, ← eq_of_hasValue_algebraMap _ hcc₂]

  have hdisc : ∀ V : Place (AlgebraicClosure ℚ) FM, Psp.IsStrictFst α β hα hβ δ V →
      Psp.reduceFst α hα V = Psp.reduceFst α hα Qs → 0 ≤ V.ord (c • f) := by
    intro V hV hVv
    by_contra hlt
    have hne : D V ≠ 0 := by
      rw [hDf₁]; intro h0; exact hlt (le_of_eq h0.symm)
    rcases hsupp V hne with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hQs' i hVv.symm
    · exact hQs' i (by rw [← hred₁ i]; exact hVv.symm)
    · exact not_isStrictSnd_of_isStrictFst hcomm hV (hQ₂ j)
    · exact not_isStrictSnd_of_isStrictFst hcomm hV (hQ₂' j)
  obtain ⟨c₁, hc₁Q, hc₁v⟩ := ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit hcusp Qs hQs (c • f) hf₁₁ hdisc
  rw [hκ₁] at hc₁v
  have hredc₁ : IsLocalRing.residue ↥A c₁ = κ₁ := eq_of_hasValue_algebraMap _ hc₁v
  have hc₁u : IsUnit c₁ := (IsLocalRing.residue_ne_zero_iff_isUnit c₁).mp (by rw [hredc₁]; exact hκ₁0)
  obtain ⟨b, hb⟩ := hc₁u.exists_left_inv
  have hb0 : (b : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have hb' : b = 0 := Subtype.ext h
    rw [hb', zero_mul] at hb
    exact zero_ne_one hb
  have hredb : IsLocalRing.residue ↥A b * κ₁ = 1 := by rw [← hredc₁, ← map_mul, hb, map_one]

  have hbmem₁ : algebraMap (AlgebraicClosure ℚ) FM (b : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers :=
    (Rpd.R₁.algebraMap_mem_iff _).mpr b.2
  have hbmem₂ : algebraMap (AlgebraicClosure ℚ) FM (b : AlgebraicClosure ℚ) ∈ Rpd.R₂.integers :=
    (Rpd.R₂.algebraMap_mem_iff _).mpr b.2
  have hf₂₁ : (b : AlgebraicClosure ℚ) • (c • f) ∈ Rpd.R₁.integers := by
    rw [Algebra.smul_def]; exact mul_mem hbmem₁ hf₁₁
  have hf₂₂ : (b : AlgebraicClosure ℚ) • (c • f) ∈ Rpd.R₂.integers := by
    rw [Algebra.smul_def]; exact mul_mem hbmem₂ hf₁₂
  have hres₁ : Rpd.R₁.residue ⟨(b : AlgebraicClosure ℚ) • (c • f), hf₂₁⟩ = 1 := by
    have e : (⟨(b : AlgebraicClosure ℚ) • (c • f), hf₂₁⟩ : Rpd.R₁.integers) = ⟨_, hbmem₁⟩ * ⟨c • f, hf₁₁⟩ :=
      Subtype.ext (Algebra.smul_def _ _)
    rw [e, map_mul, Rpd.R₁.residue_algebraMap b, hκ₁, ← map_mul, hredb, map_one]
  have hres₂ : Rpd.R₂.residue ⟨(b : AlgebraicClosure ℚ) • (c • f), hf₂₂⟩ = 1 := by
    have e : (⟨(b : AlgebraicClosure ℚ) • (c • f), hf₂₂⟩ : Rpd.R₂.integers) = ⟨_, hbmem₂⟩ * ⟨c • f, hf₁₂⟩ :=
      Subtype.ext (Algebra.smul_def _ _)
    rw [e, map_mul, Rpd.R₂.residue_algebraMap b, hκ₂, hκ, ← map_mul, hredb, map_one]
  have hval : Qs.HasValue ((b : AlgebraicClosure ℚ) • (c • f)) (1 : AlgebraicClosure ℚ) := by
    have hbc : (b : AlgebraicClosure ℚ) * (c₁ : AlgebraicClosure ℚ) = 1 := by exact_mod_cast congrArg Subtype.val hb
    have h := HasValue.smul Qs hc₁Q (b : AlgebraicClosure ℚ)
    rwa [hbc] at h
  have hdiv₂ : ∀ V : Place (AlgebraicClosure ℚ) FM, V.ord ((b : AlgebraicClosure ℚ) • (c • f)) =
      (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
        - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) : Divisor (AlgebraicClosure ℚ) FM) V) :=
    fun V => by rw [ord_smul V hb0, ord_smul V hc0, hdiv V]

  exact ModularCurve.JHPlaceSpecialization.ProlongationDatum.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit hcusp Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ Q₁' Q₂' hQ₁' hQ₂' hred₁ hred₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hgp₁ hgp₂ Qs hQs hQs' n hn _ hf₂₁ hf₂₂ hres₁ hres₂ hval hdiv₂

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp (solution)
