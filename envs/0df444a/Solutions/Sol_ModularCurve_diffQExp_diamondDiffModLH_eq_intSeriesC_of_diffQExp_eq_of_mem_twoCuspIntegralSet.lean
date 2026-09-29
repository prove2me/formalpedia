-- Prove2me | solution 1 for ModularCurve.diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9cb24e3f-5b98-5faa-8c19-64e61fb3d533

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_IsDiamondPullbackModL_coe_apply_eq_of_mem_Gamma0_of_level_mul
import Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed
import Theorems.Thm_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut"
p2m_attr_erase "simp" "ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk"
p2m_attr_erase "simp" "ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open ModularCurve ModularForm UpperHalfPlane EisensteinSeries HahnSeries CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups ModularForm

namespace L3Sol

section LevelOne

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

theorem isIntegralQExp_E6 : IsIntegralQExp (E₆ : ℍ → ℂ) eisenstein6 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein6, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

variable (Γ : Subgroup SL(2, ℤ))

def e4cube : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) ((E₄.pow 3).mcast (by norm_num))

def delta : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

def e4sqe6neg : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 14 :=
  restrictForm (Subgroup.map_le_range _ Γ) ((-((E₄.pow 2).mul E₆)).mcast (by norm_num))

theorem isIntegralQExp_e4cube : IsIntegralQExp (e4cube Γ : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, e4cube, coe_restrictForm, map_pow, isIntegralQExp_E4,
    ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem coe_delta : (delta Γ : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem isIntegralQExp_delta :
    IsIntegralQExp (delta Γ : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) := by
  rw [IsIntegralQExp, coe_delta]
  exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem isIntegralQExp_e4sqe6neg :
    IsIntegralQExp (e4sqe6neg Γ : ℍ → ℂ) (-(eisenstein4 ^ 2 * eisenstein6)) := by
  rw [IsIntegralQExp, e4sqe6neg, coe_restrictForm, ModularForm.qExpansion_mcast, map_neg, map_mul, map_pow,
    isIntegralQExp_E4, isIntegralQExp_E6,
    ModularForm.coe_neg, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_SL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem slash_eq_of_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k) (hle : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ)
    (γ : SL(2, ℤ)) :
    ((⇑(restrictForm hle F) : ℍ → ℂ) ∣[k] γ) = ⇑(restrictForm hle F) := by
  rw [coe_restrictForm, ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq F _ ⟨γ, rfl⟩

theorem e4cube_slash (γ : SL(2, ℤ)) : ((⇑(e4cube Γ) : ℍ → ℂ) ∣[(12 : ℤ)] γ) = ⇑(e4cube Γ) :=
  slash_eq_of_levelOne Γ _ _ γ

theorem delta_slash (γ : SL(2, ℤ)) : ((⇑(delta Γ) : ℍ → ℂ) ∣[(12 : ℤ)] γ) = ⇑(delta Γ) :=
  slash_eq_of_levelOne Γ _ _ γ

theorem e4sqe6neg_slash (γ : SL(2, ℤ)) : ((⇑(e4sqe6neg Γ) : ℍ → ℂ) ∣[(14 : ℤ)] γ) = ⇑(e4sqe6neg Γ) :=
  slash_eq_of_levelOne Γ _ _ γ

end LevelOne

section Series

variable (K : Type*) [Field K]

theorem intSeriesC_delta_ne_zero : intSeriesC K (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem intSeriesC_neg (q : PowerSeries ℤ) : intSeriesC K (-q) = -intSeriesC K q := by
  simp [intSeriesC]

theorem intSeriesC_pow (q : PowerSeries ℤ) (n : ℕ) : intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  simp [intSeriesC]

theorem jqModC_mul_delta :
    jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

theorem intSeriesC_eisenstein4_ne_zero : intSeriesC K eisenstein4 ≠ 0 := by
  intro h
  have h1 : (intSeriesC K eisenstein4).coeff 0 = (0 : LaurentSeries K).coeff 0 :=
    congrArg (fun z : LaurentSeries K => z.coeff 0) h
  rw [intSeriesC, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, HahnSeries.coeff_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, eisenstein4, PowerSeries.coeff_mk] at h1
  simp at h1

theorem thetaL_coeff (f : LaurentSeries K) (n : ℤ) : (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, LaurentSeries.derivative_apply, HahnSeries.coeff_single_mul, one_mul,
    LaurentSeries.hasseDeriv_coeff, show n - 1 + ((1 : ℕ) : ℤ) = n by push_cast; ring,
    Ring.choose_one_right, zsmul_eq_mul]

theorem thetaL_map {R S : Type*} [Field R] [Field S] (g : R →+* S) (f : LaurentSeries R) :
    (thetaL R f).map g = thetaL S (f.map g) := by
  ext n
  simp only [HahnSeries.map_coeff, thetaL_coeff, map_mul, map_intCast]

theorem qEuler_eq_thetaL (f : LaurentSeries K) : qEuler K f = thetaL K f := by
  ext n
  rw [qEuler_coeff, thetaL_coeff]

theorem qEuler_map {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (f : LaurentSeries R) :
    (qEuler R f).map g = qEuler S (f.map g) := by
  ext n
  simp only [HahnSeries.map_coeff, qEuler_coeff, map_mul, map_intCast]

theorem intSeriesC_eq_map (L : Type*) [Field L] (q : PowerSeries ℤ) :
    intSeriesC L q = (HahnSeries.ofPowerSeries ℤ ℤ q).map (Int.castRingHom L) := by
  ext n
  rw [HahnSeries.map_coeff, intSeriesC]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      eq_intCast]
  · have h1 : (HahnSeries.ofPowerSeries ℤ L (q.map (Int.castRingHom L))).coeff n = 0 := by
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
      rintro ⟨m, hm⟩; exact hn (hm ▸ Int.natCast_nonneg m)
    have h2 : (HahnSeries.ofPowerSeries ℤ ℤ q).coeff n = 0 := by
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
      rintro ⟨m, hm⟩; exact hn (hm ▸ Int.natCast_nonneg m)
    rw [h1, h2, map_zero]

theorem map_mul_laurent {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (x y : LaurentSeries R) :
    (x * y).map g = x.map g * y.map g :=
  HahnSeries.map_mul g.toNonUnitalRingHom

theorem thetaL_jq_mul_delta_rat :
    thetaL ℚ (jqModC ℚ) * intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit) =
      intSeriesC ℚ (-(eisenstein4 ^ 2 * eisenstein6)) := by
  have hR := ModularCurve.thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6
  have hE4 : intSeriesC ℚ eisenstein4 ≠ 0 := intSeriesC_eisenstein4_ne_zero ℚ
  apply mul_right_cancel₀ hE4
  have e1 : HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein4) = intSeriesC ℚ eisenstein4 := rfl
  have e2 : HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein6) = intSeriesC ℚ eisenstein6 := rfl
  rw [e1, e2] at hR
  calc thetaL ℚ (jqModC ℚ) * intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit) * intSeriesC ℚ eisenstein4
      = (thetaL ℚ jq * intSeriesC ℚ eisenstein4) * intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit) := by
        rw [jqModC_rat]; ring
    _ = -(jq * intSeriesC ℚ eisenstein6) * intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit) := by rw [hR]
    _ = -((jqModC ℚ * intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit)) * intSeriesC ℚ eisenstein6) := by
        rw [← jqModC_rat]; ring
    _ = -(intSeriesC ℚ (eisenstein4 ^ 3) * intSeriesC ℚ eisenstein6) := by rw [jqModC_mul_delta]
    _ = intSeriesC ℚ (-(eisenstein4 ^ 2 * eisenstein6)) * intSeriesC ℚ eisenstein4 := by
        rw [intSeriesC_neg, intSeriesC_mul, intSeriesC_pow, intSeriesC_pow]; ring

theorem qEuler_jqModC_mul_delta_int :
    qEuler ℤ (jqModC ℤ) * HahnSeries.ofPowerSeries ℤ ℤ (PowerSeries.X * dedekindEtaUnit) =
      HahnSeries.ofPowerSeries ℤ ℤ (-(eisenstein4 ^ 2 * eisenstein6)) := by
  have hinj : Function.Injective (fun x : LaurentSeries ℤ => x.map (Int.castRingHom ℚ)) := by
    intro x y h
    ext n
    have := congrArg (fun s : LaurentSeries ℚ => s.coeff n) h
    simp only [HahnSeries.map_coeff, eq_intCast, Int.cast_inj] at this
    exact this
  apply hinj
  show (qEuler ℤ (jqModC ℤ) * HahnSeries.ofPowerSeries ℤ ℤ (PowerSeries.X * dedekindEtaUnit)).map (Int.castRingHom ℚ) =
    (HahnSeries.ofPowerSeries ℤ ℤ (-(eisenstein4 ^ 2 * eisenstein6))).map (Int.castRingHom ℚ)
  rw [map_mul_laurent, qEuler_map, ← jqModC_eq_map_intCast ℚ, ← intSeriesC_eq_map, ← intSeriesC_eq_map,
    qEuler_eq_thetaL, thetaL_jq_mul_delta_rat]

theorem thetaL_jqModC_mul_delta :
    thetaL K (jqModC K) * intSeriesC K (PowerSeries.X * dedekindEtaUnit) =
      intSeriesC K (-(eisenstein4 ^ 2 * eisenstein6)) := by
  rw [← qEuler_eq_thetaL, intSeriesC_eq_map, intSeriesC_eq_map, jqModC_eq_map_intCast K, ← qEuler_map,
    ← map_mul_laurent, qEuler_jqModC_mul_delta_int]

end Series

end L3Sol

namespace L3Sol

section Diff

variable (K : Type*) [Field K] [IsAlgClosed K] (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

theorem exists_eq_smul_D_j (hT : ModularGroup.T ∈ Γ) :
    ∃ jb : qExpFunctionFieldC K Γ, (jb : LaurentSeries K) = jqModC K ∧
      ∀ ω : Ω[qExpFunctionFieldC K Γ⁄K], ∃ c : qExpFunctionFieldC K Γ,
        ω = c • KaehlerDifferential.D K (qExpFunctionFieldC K Γ) jb := by
  let F : IntermediateField K (LaurentSeries K) := qExpFunctionFieldC K Γ
  obtain ⟨x, hxj, hxt, hfd⟩ :
      ∃ x : F, (x : LaurentSeries K) = jqModC K ∧ Transcendental K x ∧
        FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : IsCurveOver K F := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxt hfd
  have hrank : Module.finrank F Ω[F⁄K] = 1 := AlgebraicCurve.IsCurveOver.finrank_kaehler (K := K) (F := F)
  have hD : diffQExp F (KaehlerDifferential.D K F x) ≠ 0 := by
    rw [diffQExp_D, hxj]
    intro h
    have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h
    have hc : (jqModC K).coeff (-1) = 1 := by
      have hZ : (jqModC ℤ).coeff (-1) = 1 := by
        have h := congrArg (fun s : LaurentSeries ℚ => s.coeff (-1)) (jqModC_eq_map_intCast ℚ)
        simp only [HahnSeries.map_coeff, jqModC_rat, coeff_jq_neg_one, eq_intCast] at h
        exact_mod_cast h.symm
      rw [jqModC_eq_map_intCast K, HahnSeries.map_coeff, hZ, map_one]
    simp only [qEuler_coeff, hc, mul_one, Int.cast_neg, Int.cast_one, HahnSeries.coeff_zero,
      neg_eq_zero, one_ne_zero] at h1
  have hD0 : KaehlerDifferential.D K F x ≠ 0 := fun h => hD (by rw [h, map_zero])
  refine ⟨x, hxj, fun ω => ?_⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (KaehlerDifferential.D K F x) hD0).mp hrank ω
  exact ⟨c, hc.symm⟩

end Diff

section Small

theorem intSeriesC_coeff_zero (K : Type*) [Field K] (q : PowerSeries ℤ) :
    (intSeriesC K q).coeff 0 = ((PowerSeries.constantCoeff q : ℤ) : K) := by
  rw [intSeriesC, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, eq_intCast]

theorem constantCoeff_eisenstein4 : PowerSeries.constantCoeff eisenstein4 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, eisenstein4, PowerSeries.coeff_mk]; simp

theorem constantCoeff_eisenstein6 : PowerSeries.constantCoeff eisenstein6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, eisenstein6, PowerSeries.coeff_mk]; simp

theorem intSeriesC_e4sqe6neg_ne_zero (K : Type*) [Field K] :
    intSeriesC K (-(eisenstein4 ^ 2 * eisenstein6)) ≠ 0 := by
  intro h
  have h1 : (intSeriesC K (-(eisenstein4 ^ 2 * eisenstein6))).coeff 0 = (0 : LaurentSeries K).coeff 0 :=
    congrArg (fun z : LaurentSeries K => z.coeff 0) h
  rw [intSeriesC_coeff_zero, HahnSeries.coeff_zero, map_neg, map_mul, map_pow, constantCoeff_eisenstein4,
    constantCoeff_eisenstein6] at h1
  norm_num at h1

variable {M : ℕ}

theorem mem_Gamma0_of_dvd {N : ℕ} (hNM : N ∣ M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : γ ∈ Gamma0 N := by
  rw [Gamma0_mem] at hγ ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr hNM) hγ

def toMF {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k) : ModularForm Γ k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  bdd_at_cusps' hc := fun γ hγ => (f.zero_at_cusps' hc γ hγ).boundedAtFilter

@[scoped simp] theorem coe_toMF {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k) : (toMF f : ℍ → ℂ) = f := rfl

end Small

end L3Sol
p2m_reactivate "P2MW.S_ModularCurve_diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet.L3Sol"

open L3Sol in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp f pf)
    (d : (ZMod M)ˣ) (pdf : PowerSeries ℤ)
    (hpdf : ModularCurve.IsIntegralQExp (CuspForm.diamondLinH 2 d f) pdf)
    (ω : Ω[ModularCurve.qExpFunctionFieldC K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hω : ModularCurve.diffQExp
      (ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω =
        ModularCurve.intSeriesC K pf) :
    ModularCurve.diffQExp
        (ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        ((haveI : NeZero (M / p) := ModularCurve.neZero_div p M hpM;
          ModularCurve.diamondDiffModLH K (M / p) (ModularCurve.infSubgroup p M H hpM)
            (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)) ω) =
      ModularCurve.intSeriesC K pdf := by

  haveI hN : NeZero (M / p) := ModularCurve.neZero_div p M hpM
  let N : ℕ := M / p
  let H' : Subgroup (ZMod N)ˣ := ModularCurve.infSubgroup p M H hpM
  let Γ' : Subgroup SL(2, ℤ) := CohCarrier.GammaH N H'
  have hNK : ((N : ℕ) : K) ≠ 0 := by
    intro h0
    have hpN : p ∣ N := (CharP.cast_eq_zero_iff K p N).mp h0
    apply hpM2
    obtain ⟨c, hc⟩ := hpN
    refine ⟨c, ?_⟩
    have : M = p * N := (Nat.mul_div_cancel' hpM).symm
    rw [this, hc]; ring

  obtain ⟨ρ₁, hρ₁⟩ := ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed K N hNK H'
  have hρ : IsDiamondPullbackModL K N H' (diamondActionModL K N H') :=
    isDiamondPullbackModL_diamondActionModL ⟨ρ₁, hρ₁⟩
  let ρ := diamondActionModL K N H'

  let dbar : (ZMod N)ˣ := ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d
  have hσdN : ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)) ∈ Gamma0 N :=
    mem_Gamma0_of_dvd (Nat.div_dvd_of_dvd hpM) (CuspForm.gammaLift M d).2
  let σN : Gamma0 N := ⟨(CuspForm.gammaLift M d : SL(2, ℤ)), hσdN⟩
  have hunits : CohCarrier.gamma0Units N σN = dbar := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, show dbar = ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d from rfl,
      ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ← CuspForm.gamma0Units_gammaLift (M := M) d,
      CohCarrier.val_gamma0Units]
    show (((CuspForm.gammaLift M d : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) =
      ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod N) ((((CuspForm.gammaLift M d : SL(2, ℤ)) 1 1 : ℤ) : ZMod M))
    rw [map_intCast]
  have hρeq : ρ (CuspForm.gammaLift N dbar⁻¹) = ρ σN⁻¹ := by
    have hk : ρ (σN * CuspForm.gammaLift N dbar⁻¹) = 1 := by
      rw [ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem hρ, map_mul,
        CuspForm.gamma0Units_gammaLift, hunits, mul_inv_cancel]
      exact one_mem _
    calc ρ (CuspForm.gammaLift N dbar⁻¹)
        = ρ (σN⁻¹ * (σN * CuspForm.gammaLift N dbar⁻¹)) := by rw [inv_mul_cancel_left]
      _ = ρ σN⁻¹ * ρ (σN * CuspForm.gammaLift N dbar⁻¹) := map_mul _ _ _
      _ = ρ σN⁻¹ := by rw [hk, mul_one]

  show diffQExp (qExpFunctionFieldC K Γ')
      (Differential.pullbackAlong (ρ (CuspForm.gammaLift N dbar⁻¹)).toAlgHom ω) = intSeriesC K pdf
  rw [hρeq]
  let σ := ρ σN⁻¹

  obtain ⟨jb, hjb, hall⟩ := exists_eq_smul_D_j K Γ' (translation_mem_GammaH N H')
  obtain ⟨c, rfl⟩ := hall ω

  have hσj : σ jb = jb := by
    apply Subtype.ext
    have hx : (jb : LaurentSeries K) =
        intSeriesC K (eisenstein4 ^ 3) / intSeriesC K (PowerSeries.X * dedekindEtaUnit) := by
      rw [hjb, eq_div_iff (intSeriesC_delta_ne_zero K)]

      rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
        show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
          PowerSeries.X * eisenstein4 ^ 3 by
            rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
              mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
        map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
        HahnSeries.single_mul_single]
      simp
    have := hρ σN⁻¹ 12 (e4cube Γ') (delta Γ') (e4cube Γ') (delta Γ') (eisenstein4 ^ 3)
      (PowerSeries.X * dedekindEtaUnit) (eisenstein4 ^ 3) (PowerSeries.X * dedekindEtaUnit)
      (isIntegralQExp_e4cube Γ') (isIntegralQExp_delta Γ') (isIntegralQExp_e4cube Γ') (isIntegralQExp_delta Γ')
      (e4cube_slash Γ' _).symm (delta_slash Γ' _).symm (intSeriesC_delta_ne_zero K) jb hx
    rw [this, hx]

  rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_D, AlgEquiv.coe_algHom, hσj, diffQExp_smul_D, hjb]

  rw [diffQExp_smul_D, hjb] at hω

  have hΔ0 : intSeriesC K (PowerSeries.X * dedekindEtaUnit) ≠ 0 := intSeriesC_delta_ne_zero K
  have hE0 : intSeriesC K (-(eisenstein4 ^ 2 * eisenstein6)) ≠ 0 := intSeriesC_e4sqe6neg_ne_zero K
  have hc : (c : LaurentSeries K) =
      intSeriesC K (pf * (PowerSeries.X * dedekindEtaUnit)) / intSeriesC K (-(eisenstein4 ^ 2 * eisenstein6)) := by
    rw [eq_div_iff hE0, ← thetaL_jqModC_mul_delta K, ← qEuler_eq_thetaL, intSeriesC_mul, ← mul_assoc, hω,
      intSeriesC_mul, intSeriesC_mul]

  have hSD : CuspForm.StableD M H 2 := CuspForm.stableD M H 2
  have hσdM : ((σN⁻¹ : Gamma0 N) : SL(2, ℤ)) ∈ Gamma0 M := by
    show ((CuspForm.gammaLift M d : SL(2, ℤ)))⁻¹ ∈ Gamma0 M
    exact inv_mem (CuspForm.gammaLift M d).2

  let ΓM : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H
  have h1per : (1 : ℝ) ∈ ((ΓM : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
    exact AddSubgroup.mem_zmultiples _
  let h₁ : ModularForm (ΓM : Subgroup (GL (Fin 2) ℝ)) 14 := ((toMF f).mul (delta ΓM)).mcast (by norm_num)
  let h : ModularForm (ΓM : Subgroup (GL (Fin 2) ℝ)) 14 :=
    ((toMF (CuspForm.diamondLinH 2 d f)).mul (delta ΓM)).mcast (by norm_num)
  have hh₁ : IsIntegralQExp (h₁ : ℍ → ℂ) (pf * (PowerSeries.X * dedekindEtaUnit)) := by
    rw [IsIntegralQExp, map_mul, hpf, (isIntegralQExp_delta ΓM)]
    show _ = qExpansion 1 ⇑(((toMF f).mul (delta ΓM)).mcast _)
    rw [ModularForm.qExpansion_mcast, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos h1per, coe_toMF]
  have hh : IsIntegralQExp (h : ℍ → ℂ) (pdf * (PowerSeries.X * dedekindEtaUnit)) := by
    rw [IsIntegralQExp, map_mul, hpdf, (isIntegralQExp_delta ΓM)]
    show _ = qExpansion 1 ⇑(((toMF (CuspForm.diamondLinH 2 d f)).mul (delta ΓM)).mcast _)
    rw [ModularForm.qExpansion_mcast, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos h1per, coe_toMF]
  have hhs : (⇑h₁ : ℍ → ℂ) = ((⇑h : ℍ → ℂ) ∣[(14 : ℤ)] ((σN⁻¹ : Gamma0 N) : SL(2, ℤ))) := by
    show (⇑f * ⇑(delta ΓM) : ℍ → ℂ) =
      ((⇑(CuspForm.diamondLinH 2 d f) * ⇑(delta ΓM) : ℍ → ℂ) ∣[(14 : ℤ)] ((CuspForm.gammaLift M d : SL(2, ℤ)))⁻¹)
    rw [show (14 : ℤ) = 2 + 12 by norm_num, ModularForm.mul_slash_SL2, delta_slash,
      CuspForm.coe_diamondLinH_apply 2 hSD]
    show ⇑f * ⇑(delta ΓM) =
      ((⇑f ∣[(2 : ℤ)] (CuspForm.gammaLift M d : SL(2, ℤ))) ∣[(2 : ℤ)] ((CuspForm.gammaLift M d : SL(2, ℤ)))⁻¹) *
        ⇑(delta ΓM)
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  have hh's : (⇑(e4sqe6neg ΓM) : ℍ → ℂ) =
      ((⇑(e4sqe6neg ΓM) : ℍ → ℂ) ∣[(14 : ℤ)] ((σN⁻¹ : Gamma0 N) : SL(2, ℤ))) :=
    (e4sqe6neg_slash ΓM _).symm
  have key := ModularCurve.IsDiamondPullbackModL.coe_apply_eq_of_mem_Gamma0_of_level_mul p M hpM hpM2 H hHp K
    hρ σN⁻¹ hσdM 14 h (e4sqe6neg ΓM) h₁ (e4sqe6neg ΓM)
    (pdf * (PowerSeries.X * dedekindEtaUnit)) (-(eisenstein4 ^ 2 * eisenstein6))
    (pf * (PowerSeries.X * dedekindEtaUnit)) (-(eisenstein4 ^ 2 * eisenstein6))
    hh (isIntegralQExp_e4sqe6neg ΓM) hh₁ (isIntegralQExp_e4sqe6neg ΓM) hhs hh's hE0 c hc

  show ((ρ σN⁻¹ c : qExpFunctionFieldC K Γ') : LaurentSeries K) * qEuler K (jqModC K) = intSeriesC K pdf
  rw [key]
  have hθ : qEuler K (jqModC K) =
      intSeriesC K (-(eisenstein4 ^ 2 * eisenstein6)) / intSeriesC K (PowerSeries.X * dedekindEtaUnit) := by
    rw [eq_div_iff hΔ0, qEuler_eq_thetaL, thetaL_jqModC_mul_delta]
  rw [hθ, intSeriesC_mul]
  field_simp

end
end S_ModularCurve_diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet
end P2MW
export P2MW.S_ModularCurve_diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet (solution)
