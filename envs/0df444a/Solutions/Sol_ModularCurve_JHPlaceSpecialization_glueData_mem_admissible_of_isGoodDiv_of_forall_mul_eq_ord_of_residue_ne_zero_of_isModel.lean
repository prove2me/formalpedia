-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.glueData_mem_admissible_of_isGoodDiv_of_forall_mul_eq_ord_of_residue_ne_zero_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/3fd87295-653a-5a04-9113-58fe8fd8aa61

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul
import Theorems.Thm_ModularCurve_diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_glueData_mem_admissible_of_isGoodDiv_of_forall_mul_eq_ord_of_residue_ne_zero_of_isModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace BidegSol

section Finsupp

variable {X Y : Type*}

theorem mapDomain_apply_eq_zero_of_forall_ne [DecidableEq Y] (r : X → Y) (D : X →₀ ℤ) (y : Y)
    (h : ∀ x ∈ D.support, r x ≠ y) : Finsupp.mapDomain r D y = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finsupp.single_apply, if_neg (h x hx)]

theorem sum_mapDomain_id (r : X → Y) (D : X →₀ ℤ) :
    ((Finsupp.mapDomain r D).sum fun _ m => m) = D.sum fun _ m => m :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

end Finsupp

section Degree

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum_of_forall_deg_eq_one (hdeg : ∀ v : Place K F, v.deg = 1) (E : Divisor K F) :
    Divisor.degree E = E.sum fun _ m => m := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [AddMonoidHom.mulRight_apply, hdeg v, Nat.cast_one, mul_one]

end Degree

section Fixed

variable {p M : ℕ} [Fact p.Prime] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p]

theorem fixed_frob_iff
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hcomm : ∀ v, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ v) =
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v))
    (hinj : Function.Injective (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p))
    (u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) :
    JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ
        (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p u) ↔
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ u := by
  unfold JHPlaceSpecialization.Fixed
  constructor
  · intro h

    have h1 : δ (qExpFrobeniusPlaceModL _ _ p (qExpFrobeniusPlaceModL _ _ p u)) = u := hinj h
    rw [← hcomm] at h1
    exact h1
  · intro h
    show qExpFrobeniusPlaceModL _ _ p (δ (qExpFrobeniusPlaceModL _ _ p (qExpFrobeniusPlaceModL _ _ p u))) =
      qExpFrobeniusPlaceModL _ _ p u
    rw [← hcomm (qExpFrobeniusPlaceModL _ _ p u), h]

end Fixed

end BidegSol

open BidegSol

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
    (Psp : JHPlaceSpecialization p M H hpM A)
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS)

    (hcusp₁ : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) w →
        ∃ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) c ∧ Psp.reduceFst α hα c = w)

    (n : ℕ) (hn : 0 < n)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hD : Psp.IsGoodDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
    (f : ↥(xHFunctionFieldBar M H))
    (h₁ : f ∈ Rpd.R₁.integers) (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (h₂ : f ∈ Rpd.R₂.integers) (hr₂ : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (hf : ∀ W, (n : ℤ) * (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) W = W.ord f) :
    Psp.glueData α β hα hβ δ SS (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS := by
  classical

  set DD : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) with hDD
  set φ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p with hφ
  set g₁ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) := Rpd.R₁.residue ⟨f, h₁⟩ with hg₁
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'

  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨k, hk⟩ := h
    have hM : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
    refine ⟨k, ?_⟩
    rw [hM, hk]; ring

  have hcomm : ∀ v, φ (δ v) = δ (φ v) := by
    intro v
    rw [hδ v, hδ (φ v)]
    exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
      (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) v
  have hinj : Function.Injective φ :=
    (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1
  have hfixφ : ∀ u, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (φ u) ↔
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ u :=
    fun u => fixed_frob_iff δ hcomm hinj u

  have hnotfix₁ : ∀ V, V ∈ DD.support →
      ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) := by
    intro V hV
    rcases hD V hV with hs | hs
    · exact hs.2
    ·
      obtain ⟨hr, hnf⟩ := hs
      rw [hr]
      exact fun h => hnf ((hfixφ _).mp h)
  have hnotfix₂ : ∀ V, Psp.IsStrictSnd α β hα hβ δ V →
      ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd β hβ δ V) :=
    fun V hs => hs.2

  have hDzero_of_fixed : ∀ V (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
      Psp.reduceFst α hα V = v → DD V = 0 := by
    intro V v hv hVv
    by_contra hne
    exact hnotfix₁ V (Finsupp.mem_support_iff.mpr hne) (hVv ▸ hv)

  set nD : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := (n : ℤ) • DD with hnD
  have hnD_apply : ∀ W, nD W = W.ord f := by
    intro W
    rw [hnD, Finsupp.smul_apply, smul_eq_mul]
    exact hf W
  have hnD_support : nD.support ⊆ DD.support := by
    rw [hnD]; exact Finsupp.support_smul

  obtain ⟨hHPD, -, hsurjκ⟩ :=
    ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2
      (ResidueField ↥A)
  haveI := hHPD
  obtain ⟨Dg, hDg, hDgdeg⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField ↥A) g₁ hr₁

  set X₁ : Divisor (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ DD) with hX₁

  have hkey : Dg = (n : ℤ) • X₁ := by
    refine Finsupp.ext fun v => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, hDg v]
    by_cases hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v
    ·
      have hX0 : X₁ v = 0 := by
        rw [hX₁]
        refine mapDomain_apply_eq_zero_of_forall_ne _ _ v fun W hW => ?_
        have hW' : W ∈ (Psp.fstDiv α β hα hβ δ DD).support := hW
        unfold JHPlaceSpecialization.fstDiv at hW'
        rw [Finsupp.support_filter, Finset.mem_filter] at hW'
        intro hWv
        exact hW'.2.2 (hWv ▸ hv)
      rw [hX0, mul_zero]
      by_cases haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v
      ·
        have hmass : Finsupp.mapDomain (Psp.reduceFst α hα) nD v = 0 := by
          refine mapDomain_apply_eq_zero_of_forall_ne _ _ v fun W hW hWv => ?_
          exact Finsupp.mem_support_iff.mp (hnD_support hW) (hDzero_of_fixed W v hv hWv)
        have hord := hO f h₁ h₂ hr₁ hr₂ nD hnD_apply v hv haff
        rw [hmass] at hord
        have hpos : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord f := by
          intro V hVv
          rw [← hf V, hDzero_of_fixed V v hv hVv, mul_zero]
        obtain ⟨hreg₁, hreg₂⟩ := hRL.1 f h₁ h₂ v hv haff hpos
        have h1 := hreg₁ hr₁
        have h2 := hreg₂ hr₂
        show v.ord g₁ = 0
        rw [hg₁]
        omega
      ·
        obtain ⟨c, hc, hcv⟩ := hcusp₁ v haff
        have hcusp := hmodel.2.2.1 f h₁ h₂ hr₁ hr₂ nD hnD_apply c hc
        rw [hcv] at hcusp
        have hmass : Finsupp.mapDomain (Psp.reduceFst α hα)
            (nD.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) v = 0 := by
          refine mapDomain_apply_eq_zero_of_forall_ne _ _ v fun W hW hWv => ?_
          rw [Finsupp.support_filter, Finset.mem_filter] at hW
          exact Finsupp.mem_support_iff.mp (hnD_support hW.1) (hDzero_of_fixed W v hv hWv)
        rw [hmass] at hcusp
        show v.ord g₁ = 0
        rw [hg₁]
        exact hcusp.symm
    ·
      have hlaw := hmodel.1 f h₁ h₂ hr₁ hr₂ nD hnD_apply v hv
      have hfst : Psp.fstDiv α β hα hβ δ nD = (n : ℤ) • Psp.fstDiv α β hα hβ δ DD := by
        unfold JHPlaceSpecialization.fstDiv
        rw [hnD, Finsupp.filter_smul]
      rw [hfst, Finsupp.mapDomain_smul, Finsupp.smul_apply, smul_eq_mul] at hlaw
      show v.ord g₁ = (n : ℤ) * X₁ v
      rw [hg₁, ← hlaw]

  have hdegκ : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v.deg = 1 := fun v =>
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr (hsurjκ v)
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  have hdegQ : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed

  have hX₁deg : Divisor.degree X₁ = 0 := by
    have h := hDgdeg
    rw [hkey, map_zsmul, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hn0

  set X₂ : Divisor (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ DD) with hX₂
  have hexcl : ∀ V, ¬ (Psp.IsStrictFst α β hα hβ δ V ∧ Psp.IsStrictSnd α β hα hβ δ V) := by
    rintro V ⟨⟨h1, hnf⟩, ⟨h2, -⟩⟩
    apply hnf
    show φ (δ (φ (Psp.reduceFst α hα V))) = Psp.reduceFst α hα V
    have h1' : δ (φ (Psp.reduceFst α hα V)) = Psp.reduceSnd β hβ δ V := h1
    have h2' : Psp.reduceFst α hα V = φ (Psp.reduceSnd β hβ δ V) := h2
    rw [h1', ← h2']
  have hsplit : Psp.fstDiv α β hα hβ δ DD + Psp.sndDiv α β hα hβ δ DD = DD := by
    refine Finsupp.ext fun V => ?_
    unfold JHPlaceSpecialization.fstDiv JHPlaceSpecialization.sndDiv
    rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hV : DD V = 0
    · simp [hV]
    · rcases hD V (Finsupp.mem_support_iff.mpr hV) with hs | hs
      · rw [if_pos hs, if_neg (fun h => hexcl V ⟨hs, h⟩), add_zero]
      · rw [if_neg (fun h => hexcl V ⟨h, hs⟩), if_pos hs, zero_add]
  have hX₂deg : Divisor.degree X₂ = 0 := by
    have hDdeg : Divisor.degree DD = 0 := D.2
    rw [← hsplit, map_add] at hDdeg

    have e1 : Divisor.degree (Psp.fstDiv α β hα hβ δ DD) = Divisor.degree X₁ := by
      rw [degree_eq_sum_of_forall_deg_eq_one hdegQ, degree_eq_sum_of_forall_deg_eq_one hdegκ, hX₁, sum_mapDomain_id]
    have e2 : Divisor.degree (Psp.sndDiv α β hα hβ δ DD) = Divisor.degree X₂ := by
      rw [degree_eq_sum_of_forall_deg_eq_one hdegQ, degree_eq_sum_of_forall_deg_eq_one hdegκ, hX₂, sum_mapDomain_id]
    rw [e1, e2, hX₁deg, zero_add] at hDdeg
    exact hDdeg

  obtain ⟨-, hφφ⟩ :=
    ModularCurve.diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul
      (ResidueField ↥A) p (M / p) hpN (infSubgroup p M H hpM)
  obtain ⟨-, -, -, -, -, -, hcancel⟩ :=
    ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul (ResidueField ↥A) (M / p)
      (infSubgroup p M H hpM)
  have he : (((pb⁻¹ : (ZMod (M / p))ˣ) : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 := by
    rw [← hpb, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hfix_ss : ∀ y, y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p →
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ y := by
    intro y hy
    show φ (δ (φ y)) = y
    rw [hcomm (φ y)]
    have h2 : φ (φ y) = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb⁻¹)) • y := hφφ pb⁻¹ he y hy
    rw [h2, hδ]
    exact (hcancel _ y pb).1
  have hfix_s : ∀ s ∈ SS,
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ s.1 ∧
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ s.2 := by
    intro s hs
    obtain ⟨hy, hs1⟩ := (mem_ssNodePairsQExp_iff s).mp ((hSS s).mp hs)
    have h2 := hfix_ss s.2 hy
    refine ⟨?_, h2⟩
    rw [hs1]
    exact (hfixφ s.2).mpr h2

  refine (GluingData.mem_admissible SS).mpr ⟨?_, ?_, fun s hs => ⟨?_, ?_⟩⟩
  · exact (Divisor.mem_degZero).mpr hX₁deg
  · exact (Divisor.mem_degZero).mpr hX₂deg
  ·
    show X₁ s.1 = 0
    rw [hX₁]
    refine mapDomain_apply_eq_zero_of_forall_ne _ _ _ fun W hW hWs => ?_
    have hW' : W ∈ (Psp.fstDiv α β hα hβ δ DD).support := hW
    unfold JHPlaceSpecialization.fstDiv at hW'
    rw [Finsupp.support_filter, Finset.mem_filter] at hW'
    exact hW'.2.2 (hWs ▸ (hfix_s s hs).1)
  ·
    show X₂ s.2 = 0
    rw [hX₂]
    refine mapDomain_apply_eq_zero_of_forall_ne _ _ _ fun W hW hWs => ?_
    have hW' : W ∈ (Psp.sndDiv α β hα hβ δ DD).support := hW
    unfold JHPlaceSpecialization.sndDiv at hW'
    rw [Finsupp.support_filter, Finset.mem_filter] at hW'
    exact hnotfix₂ W hW'.2 (hWs ▸ (hfix_s s hs).2)

end S_ModularCurve_JHPlaceSpecialization_glueData_mem_admissible_of_isGoodDiv_of_forall_mul_eq_ord_of_residue_ne_zero_of_isModel
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_glueData_mem_admissible_of_isGoodDiv_of_forall_mul_eq_ord_of_residue_ne_zero_of_isModel (solution)
