-- Prove2me | solution 1 for ModularCurve.IsDiamondPullbackModL.coe_apply_eq_of_mem_Gamma0_of_level_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/222eb354-447e-5166-9d8d-c14728b4aaf7

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul
import Theorems.Thm_ModularCurve_mem_intFormRatiosC_of_coe_eq_intSeriesC_div
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsDiamondPullbackModL_coe_apply_eq_of_mem_Gamma0_of_level_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ"
p2m_attr_erase "simp" "ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open ModularCurve ModularForm UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Pointwise

namespace L3aSol

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev ΓH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ΓH M H ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • ΓH M H := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨δ, hδ⟩, by simp; rfl⟩

def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓH M H) k) :
    ModularForm (ΓH M H) k :=
  restrictForm (le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓH M H) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] γ := rfl

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (ΓH M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

theorem exists_integral_pair {k : ℤ} (a : ModularForm (ΓH M H) k) {pa : PowerSeries ℤ}
    (ha : IsIntegralQExp a pa) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ∃ (c : ℕ) (F F₁ : ModularForm (ΓH M H) k) (pF : PowerSeries ℤ),
      IsIntegralQExp F pF ∧ IsIntegralQExp F₁ ((PowerSeries.C ((M : ℤ) ^ c)) * pa) ∧
      (⇑F : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑a : ℍ → ℂ) ∣[k] γ⁻¹) ∧
      (⇑F₁ : ℍ → ℂ) = ((⇑F : ℍ → ℂ) ∣[k] γ) := by
  have hle : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ ΓH M H :=
    Subgroup.map_mono (Gamma1_le_GammaH M H)
  obtain ⟨c, f₁, p₁, hf₁, hf₁s⟩ :=
    ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 M (restrictForm hle a)
      (by rw [IsIntegralQExp, coe_restrictForm]; exact ha) γ⁻¹ (inv_mem hγ)
  have hF : (⇑(((M : ℂ) ^ c) • slashForm γ⁻¹ (inv_mem hγ) a) : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑a : ℍ → ℂ) ∣[k] γ⁻¹) := by
    rw [ModularForm.IsGLPos.coe_smul, coe_slashForm]
  have hF₁ : (⇑(((M : ℂ) ^ c) • a) : ℍ → ℂ) = ((M : ℂ) ^ c) • (⇑a : ℍ → ℂ) := ModularForm.IsGLPos.coe_smul _ _
  refine ⟨c, ((M : ℂ) ^ c) • slashForm γ⁻¹ (inv_mem hγ) a, ((M : ℂ) ^ c) • a, p₁, ?_, ?_, hF, ?_⟩
  ·
    have : (⇑(((M : ℂ) ^ c) • slashForm γ⁻¹ (inv_mem hγ) a) : ℍ → ℂ) = ⇑f₁ := by
      rw [hF, hf₁s, coe_restrictForm]
    rw [IsIntegralQExp, this]
    exact hf₁
  · rw [IsIntegralQExp, map_mul, PowerSeries.map_C, ha, hF₁, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods,
      PowerSeries.smul_eq_C_mul, eq_intCast, Int.cast_pow, Int.cast_natCast]
  · rw [hF₁, hF, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

theorem intSeriesC_ne_zero_of_pair (K : Type*) [Field K] (hM : (M : K) ≠ 0) {k : ℤ}
    (b : ModularForm (ΓH M H) k) {pb : PowerSeries ℤ} (hb : IsIntegralQExp b pb) (hb0 : intSeriesC K pb ≠ 0)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {c : ℕ} (G : ModularForm (ΓH M H) k) {pG : PowerSeries ℤ}
    (hG : IsIntegralQExp G pG) (hGs : (⇑G : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑b : ℍ → ℂ) ∣[k] γ⁻¹)) :
    intSeriesC K pG ≠ 0 := by
  intro h0

  have hcoef : ∀ n : ℕ, ((PowerSeries.coeff n pG : ℤ) : K) = 0 := by
    intro n
    have := congrArg (fun z : LaurentSeries K => z.coeff n) h0
    simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast,
      HahnSeries.coeff_zero] at this
    exact this
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K

  have hdvd : ∀ n : ℕ, (ℓ : ℤ) ∣ PowerSeries.coeff n pG := fun n =>
    (CharP.intCast_eq_zero_iff K ℓ _).mp (hcoef n)
  let q : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff n pG / ℓ
  have hq : pG = PowerSeries.C (ℓ : ℤ) * q := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    exact (Int.mul_ediv_cancel' (hdvd n)).symm
  rcases CharP.char_is_prime_or_zero K ℓ with hprime | hzero
  ·
    have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hprime.ne_zero
    let G' : ModularForm (ΓH M H) k := ((ℓ : ℂ)⁻¹) • G
    have hG' : IsIntegralQExp (⇑G') q := by
      rw [IsIntegralQExp, show (⇑G' : ℍ → ℂ) = ((ℓ : ℂ)⁻¹) • (⇑G : ℍ → ℂ) from ModularForm.IsGLPos.coe_smul _ _,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, ← hG, hq, map_mul, PowerSeries.map_C,
        eq_intCast, Int.cast_natCast, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hℓ0,
        map_one, one_mul]
    obtain ⟨c', F, F₁, pF, hF, -, hFs, -⟩ := exists_integral_pair G' hG' γ⁻¹ (inv_mem hγ)
    rw [inv_inv] at hFs

    have hfun : (ℓ : ℂ) • (⇑F : ℍ → ℂ) = ((M : ℂ) ^ (c + c')) • (⇑b : ℍ → ℂ) := by
      rw [hFs, show (⇑G' : ℍ → ℂ) = ((ℓ : ℂ)⁻¹) • (⇑G : ℍ → ℂ) from ModularForm.IsGLPos.coe_smul _ _, hGs,
        ModularForm.SL_smul_slash, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, inv_mul_cancel,
        SlashAction.slash_one, smul_smul, smul_smul, smul_smul, pow_add]
      congr 1
      field_simp

    have h1 : IsIntegralQExp ((ℓ : ℂ) • (⇑F : ℍ → ℂ)) (PowerSeries.C (ℓ : ℤ) * pF) := by
      rw [IsIntegralQExp, map_mul, PowerSeries.map_C, eq_intCast, Int.cast_natCast, hF,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, PowerSeries.smul_eq_C_mul]
    have h2 : IsIntegralQExp (((M : ℂ) ^ (c + c')) • (⇑b : ℍ → ℂ)) (PowerSeries.C ((M : ℤ) ^ (c + c')) * pb) := by
      rw [IsIntegralQExp, map_mul, PowerSeries.map_C, eq_intCast, Int.cast_pow, Int.cast_natCast, hb,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, PowerSeries.smul_eq_C_mul]
    rw [hfun] at h1
    have heq : PowerSeries.C (ℓ : ℤ) * pF = PowerSeries.C ((M : ℤ) ^ (c + c')) * pb := h1.unique h2

    have : intSeriesC K (PowerSeries.C ((M : ℤ) ^ (c + c')) * pb) = 0 := by
      rw [← heq, intSeriesC_mul]
      have : intSeriesC K (PowerSeries.C (ℓ : ℤ)) = 0 := by
        rw [intSeriesC, PowerSeries.map_C, eq_intCast, Int.cast_natCast, CharP.cast_eq_zero, map_zero, map_zero]
      rw [this, zero_mul]
    rw [intSeriesC_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · apply hM
      rw [intSeriesC, PowerSeries.map_C, eq_intCast, Int.cast_pow, Int.cast_natCast, HahnSeries.ofPowerSeries_C] at h
      by_contra hM'
      exact HahnSeries.C_ne_zero (pow_ne_zero _ hM') h
    · exact hb0 h
  ·
    subst hzero
    have hpG : pG = 0 := by
      ext n
      rw [map_zero]
      exact zero_dvd_iff.mp (hdvd n)
    have hG0 : (⇑G : ℍ → ℂ) = 0 := by
      have : UpperHalfPlane.qExpansion 1 ⇑G = 0 := by rw [← hG, hpG, map_zero]
      have hG00 : G = 0 := (ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods G).mp this
      rw [hG00]; rfl
    have hb00 : (⇑b : ℍ → ℂ) = 0 := by
      have hMc : ((M : ℂ) ^ c) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (NeZero.ne M))
      have h1 : ((⇑b : ℍ → ℂ) ∣[k] γ⁻¹) = 0 := by
        have := hGs.symm.trans hG0
        exact (smul_eq_zero.mp this).resolve_left hMc
      have h2 : (⇑b : ℍ → ℂ) = (((⇑b : ℍ → ℂ) ∣[k] γ⁻¹) ∣[k] γ) := by
        rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
      rw [h2, h1, SlashAction.zero_slash]
    apply hb0
    have : pb = 0 := by
      have hq0 : UpperHalfPlane.qExpansion 1 (⇑b : ℍ → ℂ) = 0 := by
        rw [hb00]; exact UpperHalfPlane.qExpansion_zero 1
      apply (PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective)
      rw [hb, hq0, map_zero]
    rw [this, intSeriesC_zero]

end L3aSol
p2m_reactivate "P2MW.S_ModularCurve_IsDiamondPullbackModL_coe_apply_eq_of_mem_Gamma0_of_level_mul.L3aSol"

namespace L3aSol

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem exists_integral_pair₂ {k : ℤ} (a b : ModularForm (ΓH M H) k) {pa pb : PowerSeries ℤ}
    (ha : IsIntegralQExp a pa) (hb : IsIntegralQExp b pb) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ∃ (c : ℕ) (F G F₁ G₁ : ModularForm (ΓH M H) k) (pF pG : PowerSeries ℤ),
      IsIntegralQExp F pF ∧ IsIntegralQExp G pG ∧
      IsIntegralQExp F₁ ((PowerSeries.C ((M : ℤ) ^ c)) * pa) ∧ IsIntegralQExp G₁ ((PowerSeries.C ((M : ℤ) ^ c)) * pb) ∧
      (⇑F : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑a : ℍ → ℂ) ∣[k] γ⁻¹) ∧
      (⇑G : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑b : ℍ → ℂ) ∣[k] γ⁻¹) ∧
      (⇑F₁ : ℍ → ℂ) = ((⇑F : ℍ → ℂ) ∣[k] γ) ∧ (⇑G₁ : ℍ → ℂ) = ((⇑G : ℍ → ℂ) ∣[k] γ) := by
  obtain ⟨c₁, F, F₁, pF, hF, hF₁, hFs, hF₁s⟩ := exists_integral_pair a ha γ hγ
  obtain ⟨c₂, G, G₁, pG, hG, hG₁, hGs, hG₁s⟩ := exists_integral_pair b hb γ hγ
  have sF : ∀ (e : ℕ) (X : ModularForm (ΓH M H) k), (⇑(((M : ℂ) ^ e) • X) : ℍ → ℂ) = ((M : ℂ) ^ e) • (⇑X : ℍ → ℂ) :=
    fun e X => ModularForm.IsGLPos.coe_smul _ _
  have iF : ∀ (e : ℕ) (X : ModularForm (ΓH M H) k) (q : PowerSeries ℤ), IsIntegralQExp X q →
      IsIntegralQExp (⇑(((M : ℂ) ^ e) • X)) (PowerSeries.C ((M : ℤ) ^ e) * q) := by
    intro e X q hX
    rw [IsIntegralQExp, map_mul, PowerSeries.map_C, eq_intCast, Int.cast_pow, Int.cast_natCast, hX, sF,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, PowerSeries.smul_eq_C_mul]
  refine ⟨c₁ + c₂, ((M : ℂ) ^ c₂) • F, ((M : ℂ) ^ c₁) • G, ((M : ℂ) ^ c₂) • F₁, ((M : ℂ) ^ c₁) • G₁,
    PowerSeries.C ((M : ℤ) ^ c₂) * pF, PowerSeries.C ((M : ℤ) ^ c₁) * pG, iF _ _ _ hF, iF _ _ _ hG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := iF c₂ F₁ _ hF₁
    rwa [← mul_assoc, ← map_mul, ← pow_add, add_comm] at this
  · have := iF c₁ G₁ _ hG₁
    rwa [← mul_assoc, ← map_mul, ← pow_add] at this
  · rw [sF, hFs, smul_smul, ← pow_add, add_comm]
  · rw [sF, hGs, smul_smul, ← pow_add]
  · rw [sF, sF, hF₁s, ModularForm.SL_smul_slash]
  · rw [sF, sF, hG₁s, ModularForm.SL_smul_slash]

theorem intSeriesC_sub (K : Type*) [Field K] (q q' : PowerSeries ℤ) :
    intSeriesC K (q - q') = intSeriesC K q - intSeriesC K q' := by
  simp [intSeriesC]

theorem intSeriesC_C (K : Type*) [Field K] (z : ℤ) : intSeriesC K (PowerSeries.C z) = HahnSeries.C (z : K) := by
  rw [intSeriesC, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C]

theorem gammaH_le_infSubgroup (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := by
  intro γ hγ
  rw [CohCarrier.mem_GammaH_iff] at hγ ⊢
  obtain ⟨h0, hu⟩ := hγ
  have h0' : γ ∈ Gamma0 (M / p) := by
    rw [Gamma0_mem] at h0 ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.div_dvd_of_dvd hpM)) h0
  refine ⟨h0', ?_⟩
  have : CohCarrier.gamma0Units (M / p) ⟨γ, h0'⟩ =
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨γ, h0⟩) := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units]
    show ((γ 1 1 : ℤ) : ZMod (M / p)) = ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p)) ((γ 1 1 : ℤ) : ZMod M)
    rw [map_intCast]
  rw [this]
  exact unitsMap_mem_infSubgroup p M H hpM hu

end L3aSol
p2m_reactivate "P2MW.S_ModularCurve_IsDiamondPullbackModL_coe_apply_eq_of_mem_Gamma0_of_level_mul.L3aSol"

open L3aSol in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    {ρ : CongruenceSubgroup.Gamma0 (M / p) →*
      (ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))}
    (hρ : ModularCurve.IsDiamondPullbackModL K (M / p) (ModularCurve.infSubgroup p M H hpM) ρ)
    (γ : CongruenceSubgroup.Gamma0 (M / p)) (hγ : (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M)
    (k : ℤ) (h h' h₁ h'₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (ph ph' ph₁ ph'₁ : PowerSeries ℤ)
    (hh : ModularCurve.IsIntegralQExp h ph) (hh' : ModularCurve.IsIntegralQExp h' ph')
    (hh₁ : ModularCurve.IsIntegralQExp h₁ ph₁) (hh'₁ : ModularCurve.IsIntegralQExp h'₁ ph'₁)
    (hhs : (⇑h₁ : UpperHalfPlane → ℂ) = ((⇑h : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hh's : (⇑h'₁ : UpperHalfPlane → ℂ) = ((⇑h' : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hph' : ModularCurve.intSeriesC K ph' ≠ 0)
    (x : ModularCurve.qExpFunctionFieldC K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hx : (x : LaurentSeries K) = ModularCurve.intSeriesC K ph₁ / ModularCurve.intSeriesC K ph'₁) :
    ((ρ γ x : ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) =
      ModularCurve.intSeriesC K ph / ModularCurve.intSeriesC K ph' := by
  haveI hN : NeZero (M / p) := ModularCurve.neZero_div p M hpM
  let N : ℕ := M / p
  let H' : Subgroup (ZMod N)ˣ := ModularCurve.infSubgroup p M H hpM
  have hNK : ((N : ℕ) : K) ≠ 0 := by
    intro h0
    have hpN : p ∣ N := (CharP.cast_eq_zero_iff K p N).mp h0
    apply hpM2
    obtain ⟨c, hc⟩ := hpN
    refine ⟨c, ?_⟩
    have : M = p * N := (Nat.mul_div_cancel' hpM).symm
    rw [this, hc]; ring
  have hle : ΓH M H ≤ ΓH N H' := Subgroup.map_mono (gammaH_le_infSubgroup p hpM)
  have h1M : (1 : ℝ) ∈ (ΓH M H).strictPeriods := one_mem_strictPeriods

  have hph'₁ : intSeriesC K ph'₁ ≠ 0 :=
    ModularCurve.intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul p M hpM hpM2 H hHp K γ hγ k
      h' h'₁ ph' ph'₁ hh' hh'₁ hh's hph'

  obtain ⟨ka, a, b, pa, pb, ha, hb, hb0, hxab⟩ :=
    ModularCurve.mem_intFormRatiosC_of_coe_eq_intSeriesC_div K (CohCarrier.GammaH N H') (translation_mem_GammaH N H')
      x ph₁ ph'₁ hph'₁ hx

  obtain ⟨c, F, G, F₁, G₁, pF, pG, hF, hG, hF₁, hG₁, hFs, hGs, hF₁s, hG₁s⟩ :=
    exists_integral_pair₂ a b ha hb (γ : SL(2, ℤ)) γ.2
  have hG0 : intSeriesC K pG ≠ 0 := intSeriesC_ne_zero_of_pair K hNK b hb hb0 _ γ.2 G hG hGs
  have hNc : intSeriesC K (PowerSeries.C (((N : ℕ) : ℤ) ^ c)) ≠ 0 := by
    rw [intSeriesC_C, Int.cast_pow, Int.cast_natCast]
    exact HahnSeries.C_ne_zero (pow_ne_zero _ hNK)

  have hx' : (x : LaurentSeries K) =
      intSeriesC K (PowerSeries.C (((N : ℕ) : ℤ) ^ c) * pa) / intSeriesC K (PowerSeries.C (((N : ℕ) : ℤ) ^ c) * pb) := by
    rw [hxab, intSeriesC_mul, intSeriesC_mul, mul_div_mul_left _ _ hNc]
  have key : ((ρ γ x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) : LaurentSeries K) =
      intSeriesC K pF / intSeriesC K pG :=
    hρ γ ka F G F₁ G₁ pF pG _ _ hF hG hF₁ hG₁ hF₁s hG₁s hG0 x hx'
  rw [key]

  let Fm : ModularForm (ΓH M H) ka := restrictForm hle F
  let Gm : ModularForm (ΓH M H) ka := restrictForm hle G
  let am : ModularForm (ΓH M H) ka := restrictForm hle a
  let bm : ModularForm (ΓH M H) ka := restrictForm hle b
  let v : ModularForm (ΓH M H) (ka + k) := Fm.mul h' - Gm.mul h
  let v₁ : ModularForm (ΓH M H) (ka + k) := (((N : ℕ) : ℂ) ^ c) • (am.mul h'₁ - bm.mul h₁)
  have hv : IsIntegralQExp (⇑v) (pF * ph' - pG * ph) := by
    rw [IsIntegralQExp, map_sub, map_mul, map_mul, hF, hG, hh, hh']
    show _ = qExpansion 1 ⇑(Fm.mul h' - Gm.mul h)
    rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1M, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos h1M, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos h1M]
    rfl
  have hv₁ : IsIntegralQExp (⇑v₁) (PowerSeries.C (((N : ℕ) : ℤ) ^ c) * (pa * ph'₁ - pb * ph₁)) := by
    rw [IsIntegralQExp, map_mul, PowerSeries.map_C, eq_intCast, Int.cast_pow, Int.cast_natCast, map_sub, map_mul,
      map_mul, ha, hb, hh₁, hh'₁]
    show _ = qExpansion 1 ⇑((((N : ℕ) : ℂ) ^ c) • (am.mul h'₁ - bm.mul h₁))
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1M, PowerSeries.smul_eq_C_mul,
      ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1M, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos h1M, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos h1M]
    rfl
  have hFγ : ((⇑F : ℍ → ℂ) ∣[ka] (γ : SL(2, ℤ))) = (((N : ℕ) : ℂ) ^ c) • (⇑a : ℍ → ℂ) := by
    rw [hFs, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  have hGγ : ((⇑G : ℍ → ℂ) ∣[ka] (γ : SL(2, ℤ))) = (((N : ℕ) : ℂ) ^ c) • (⇑b : ℍ → ℂ) := by
    rw [hGs, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  have hvs : (⇑v₁ : ℍ → ℂ) = ((⇑v : ℍ → ℂ) ∣[ka + k] (γ : SL(2, ℤ))) := by
    show (⇑((((N : ℕ) : ℂ) ^ c) • (am.mul h'₁ - bm.mul h₁)) : ℍ → ℂ) = (⇑(Fm.mul h' - Gm.mul h) : ℍ → ℂ) ∣[ka + k] (γ : SL(2, ℤ))
    have hsub : ∀ (f g : ℍ → ℂ), ((f - g) ∣[ka + k] (γ : SL(2, ℤ))) = (f ∣[ka + k] (γ : SL(2, ℤ))) - (g ∣[ka + k] (γ : SL(2, ℤ))) :=
      fun f g => by rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.coe_sub, ModularForm.coe_sub, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.coe_mul, ModularForm.coe_mul, coe_restrictForm, coe_restrictForm, coe_restrictForm, coe_restrictForm,
      hsub, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2, hFγ, hGγ, ← hhs, ← hh's, smul_sub, smul_mul_assoc,
      smul_mul_assoc]

  have hcross : intSeriesC K pa * intSeriesC K ph'₁ - intSeriesC K pb * intSeriesC K ph₁ = 0 := by
    have := hxab.symm.trans hx
    rw [div_eq_div_iff hb0 hph'₁] at this
    rw [this, mul_comm, sub_self]
  have hv₁0 : intSeriesC K (PowerSeries.C (((N : ℕ) : ℤ) ^ c) * (pa * ph'₁ - pb * ph₁)) = 0 := by
    rw [intSeriesC_mul, intSeriesC_sub, intSeriesC_mul, intSeriesC_mul, hcross, mul_zero]

  have hv0 : intSeriesC K (pF * ph' - pG * ph) = 0 := by
    by_contra hne
    exact ModularCurve.intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul p M hpM hpM2 H hHp K γ hγ
      (ka + k) v v₁ _ _ hv hv₁ hvs hne hv₁0
  rw [intSeriesC_sub, intSeriesC_mul, intSeriesC_mul, sub_eq_zero] at hv0
  rw [div_eq_div_iff hG0 hph', hv0, mul_comm]

end
end S_ModularCurve_IsDiamondPullbackModL_coe_apply_eq_of_mem_Gamma0_of_level_mul
end P2MW
export P2MW.S_ModularCurve_IsDiamondPullbackModL_coe_apply_eq_of_mem_Gamma0_of_level_mul (solution)
