-- Prove2me | solution 1 for ModularCurve.intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ba8eb9d6-adf9-5bc0-b115-1bf0224c7402

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.XHDRModelAtP.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply"
p2m_attr_erase "simp" "CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open scoped MatrixGroups ModularForm
p2m_open "CongruenceSubgroup CohCarrier ModularCurve~coeffMap_injective~coeffMap_intSeriesC"

noncomputable section

namespace ValNz

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem T_mem_GammaH : ModularGroup.T ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ Gamma0 M := by
    rw [Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show (((ModularGroup.T) 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    simp [ModularGroup.T]
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_GammaH]
  exact AddSubgroup.mem_zmultiples _

theorem upperLeft_eq_inv (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M) :
    ((δ 0 0 : ℤ) : ZMod M) = ((gamma0Units M ⟨δ, hδ⟩)⁻¹ : (ZMod M)ˣ) := by
  have hdet : (δ 0 0 : ℤ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe δ
    rw [Matrix.det_fin_two] at this
    exact this
  have h10 : ((δ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hδ
  have hmul : ((δ 0 0 : ℤ) : ZMod M) * ((gamma0Units M ⟨δ, hδ⟩ : (ZMod M)ˣ) : ZMod M) = 1 := by
    rw [val_gamma0Units]
    show ((δ 0 0 : ℤ) : ZMod M) * ((δ 1 1 : ℤ) : ZMod M) = 1
    have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
    push_cast at this
    rw [h10, mul_zero, sub_zero] at this
    exact this
  exact Units.eq_inv_of_mul_eq_one_right hmul

theorem pow_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (i : ℕ) : γ ^ i ∈ Gamma0 M :=
  Subgroup.pow_mem _ hγ i

theorem gamma0Units_pow {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (i : ℕ) :
    gamma0Units M ⟨γ ^ i, pow_mem_Gamma0 hγ i⟩ = gamma0Units M ⟨γ, hγ⟩ ^ i := by
  rw [← map_pow]; rfl

theorem upperLeft_pow {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (i : ℕ) :
    (((γ ^ i : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = ((((gamma0Units M ⟨γ, hγ⟩)⁻¹) ^ i : (ZMod M)ˣ) : ZMod M) := by
  rw [upperLeft_eq_inv (γ ^ i) (pow_mem_Gamma0 hγ i), gamma0Units_pow hγ i, inv_pow]

theorem exists_pow_mem_GammaH [NeZero M] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ n : ℕ, 0 < n ∧ γ ^ n ∈ GammaH M H := by
  refine ⟨orderOf (gamma0Units M ⟨γ, hγ⟩), orderOf_pos _, ?_⟩
  rw [mem_GammaH_iff]
  refine ⟨pow_mem_Gamma0 hγ _, ?_⟩
  rw [gamma0Units_pow hγ, pow_orderOf_eq_one]
  exact one_mem H

end Group

section QExp

abbrev Q (φ : UpperHalfPlane → ℂ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 φ)

abbrev c : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := fun x y h => by
  ext k
  have := congrArg (fun s : LaurentSeries S => s.coeff k) h
  simp only [coeffMap_coeff] at this
  exact hf this

theorem c_injective : Function.Injective c := coeffMap_injective _ (algebraMap ℚ ℂ).injective

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R P) = HahnSeries.ofPowerSeries ℤ S (P.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  · lift k to ℕ using hk with k
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem coeffMap_intCast_ofPowerSeries (K : Type*) [Field K] (P : PowerSeries ℤ) :
    coeffMap (Int.castRingHom K) (HahnSeries.ofPowerSeries ℤ ℤ P) = intSeriesC K P := by
  rw [coeffMap_ofPowerSeries]; rfl

theorem coeffMap_intSeriesC {K K' : Type*} [Field K] [Field K'] (f : K →+* K') (P : PowerSeries ℤ) :
    coeffMap f (intSeriesC K P) = intSeriesC K' P := by
  rw [← coeffMap_intCast_ofPowerSeries, ← coeffMap_intCast_ofPowerSeries, coeffMap_coeffMap]
  congr 1
  ext n; simp

theorem intSeriesC_eq_zero_iff {K K' : Type*} [Field K] [Field K'] (f : K →+* K') (P : PowerSeries ℤ) :
    intSeriesC K P = 0 ↔ intSeriesC K' P = 0 := by
  constructor
  · intro h; rw [← coeffMap_intSeriesC f, h, map_zero]
  · intro h
    apply coeffMap_injective f f.injective
    rw [coeffMap_intSeriesC, h, map_zero]

theorem c_intSeriesC_eq_Q {φ : UpperHalfPlane → ℂ} {P : PowerSeries ℤ} (hP : IsIntegralQExp φ P) :
    c (intSeriesC ℚ P) = Q φ := by
  rw [coeffMap_intSeriesC]
  simp only [intSeriesC, Q]
  rw [hP]

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem Q_ne_zero (h : ModularForm ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hh : h ≠ 0) : Q ⇑h ≠ 0 := by
  intro h0
  apply hh
  have h0' : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑h) = HahnSeries.ofPowerSeries ℤ ℂ 0 := by
    rw [map_zero]; exact h0
  have : UpperHalfPlane.qExpansion 1 ⇑h = 0 := HahnSeries.ofPowerSeries_injective h0'
  exact (ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods h).mp this

theorem ne_zero_of_intSeriesC_ne_zero {K : Type*} [Field K]
    (h : ModularForm ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) {P : PowerSeries ℤ}
    (hP : IsIntegralQExp ⇑h P) (h0 : intSeriesC K P ≠ 0) : h ≠ 0 := by
  rintro rfl
  apply h0
  have hP0 : P = 0 := by
    apply hP.unique
    rw [ModularForm.coe_zero]
    exact isIntegralQExp_zero
  rw [hP0, intSeriesC_zero]

end QExp

section Orbit

private abbrev _root_.ValNz.T (γ : SL(2, ℤ)) (k : ℤ) (φ : UpperHalfPlane → ℂ) (i : ℕ) : LaurentSeries ℂ :=
  Q (φ ∣[k] ((γ ^ i : SL(2, ℤ)) : GL (Fin 2) ℝ))

p2m_export "ValNz" "T"
theorem T_zero (γ : SL(2, ℤ)) (k : ℤ) (φ : UpperHalfPlane → ℂ) : T γ k φ 0 = Q φ := by
  simp [T, SlashAction.slash_one]

theorem slash_slash_pow (γ : SL(2, ℤ)) (k : ℤ) (φ : UpperHalfPlane → ℂ) (i : ℕ) :
    ((φ ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] ((γ ^ i : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (φ ∣[k] ((γ ^ (i + 1) : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  rw [← SlashAction.slash_mul, ← map_mul, ← map_mul, ← pow_succ']

structure Orb (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (γ : SL(2, ℤ)) (k : ℤ) where
  hγ : γ ∈ Gamma0 M
  h : ModularForm ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k
  h₁ : ModularForm ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k
  ph : PowerSeries ℤ
  ph₁ : PowerSeries ℤ
  hh : IsIntegralQExp ⇑h ph
  hh₁ : IsIntegralQExp ⇑h₁ ph₁
  hhs : (⇑h₁ : UpperHalfPlane → ℂ) = ((⇑h : UpperHalfPlane → ℂ) ∣[k] (γ : GL (Fin 2) ℝ))
  hph : intSeriesC ℚ ph ≠ 0

namespace Orb

abbrev x {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {γ : SL(2, ℤ)} {k : ℤ} (O : Orb M H γ k) :
    LaurentSeries ℚ :=
  intSeriesC ℚ O.ph₁ / intSeriesC ℚ O.ph

theorem x_mem {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {γ : SL(2, ℤ)} {k : ℤ} (O : Orb M H γ k) :
    O.x ∈ xHFunctionField M H := by
  show intSeriesC ℚ O.ph₁ / intSeriesC ℚ O.ph ∈ qExpFunctionFieldC ℚ (GammaH M H)
  exact div_mem_qExpFunctionFieldC O.h₁ O.h O.hh₁ O.hh O.hph

abbrev dpow {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {γ : SL(2, ℤ)} {k : ℤ} (O : Orb M H γ k) (i : ℕ) :
    (ZMod M)ˣ :=
  (gamma0Units M ⟨γ, O.hγ⟩)⁻¹ ^ i

theorem exists_iterate {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {γ : SL(2, ℤ)} {k : ℤ} (O : Orb M H γ k)
    (i : ℕ) :
    ∃ y : LaurentSeries ℚ, y ∈ xHFunctionField M H ∧
      ((diamondAutHBar M H (O.dpow i)
          ⟨coeffEmb (AlgebraicClosure ℚ) O.x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) O.x_mem⟩ :
          xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y ∧
      c y * T γ k ⇑O.h i = T γ k ⇑O.h (i + 1) := by
  have hD : IsDiamondAutHBar M H (O.dpow i) (diamondAutHBar M H (O.dpow i)) :=
    (ModularCurve.heckeDiamondInputsHAll M H).isDiamondAutHBar _
  obtain ⟨y, hy, hσ, hq⟩ := hD k O.h₁ O.h O.ph₁ O.ph O.hh₁ O.hh O.hph (γ ^ i) (pow_mem_Gamma0 O.hγ i)
    (upperLeft_pow O.hγ i)
  refine ⟨y, hy, hσ, ?_⟩
  have hq' := hq
  rw [O.hhs, slash_slash_pow] at hq'
  exact hq'

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {γ : SL(2, ℤ)} {k : ℤ}

def y (O : Orb M H γ k) (i : ℕ) : LaurentSeries ℚ := (O.exists_iterate i).choose

theorem y_mem (O : Orb M H γ k) (i : ℕ) : O.y i ∈ xHFunctionField M H := (O.exists_iterate i).choose_spec.1

theorem y_dia (O : Orb M H γ k) (i : ℕ) :
    ((diamondAutHBar M H (O.dpow i)
        ⟨coeffEmb (AlgebraicClosure ℚ) O.x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) O.x_mem⟩ :
        xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (O.y i) :=
  (O.exists_iterate i).choose_spec.2.1

theorem y_T (O : Orb M H γ k) (i : ℕ) : c (O.y i) * T γ k ⇑O.h i = T γ k ⇑O.h (i + 1) :=
  (O.exists_iterate i).choose_spec.2.2

theorem Q_h_ne_zero (O : Orb M H γ k) : Q ⇑O.h ≠ 0 :=
  Q_ne_zero O.h (ne_zero_of_intSeriesC_ne_zero O.h O.hh O.hph)

theorem prod_T (O : Orb M H γ k) (m : ℕ) :
    c (∏ i ∈ Finset.range m, O.y i) * T γ k ⇑O.h 0 = T γ k ⇑O.h m := by
  induction m with
  | zero => rw [Finset.prod_range_zero, map_one, one_mul]
  | succ m ih =>
    rw [Finset.prod_range_succ, map_mul, mul_comm (c _) (c (O.y m)), mul_assoc, ih, y_T]

theorem prod_eq_one (O : Orb M H γ k) {n : ℕ} (hn : γ ^ n ∈ GammaH M H) :
    ∏ i ∈ Finset.range n, O.y i = 1 := by
  have hT : T γ k ⇑O.h n = T γ k ⇑O.h 0 := by
    rw [T_zero]
    show Q _ = Q _
    congr 1
    exact SlashInvariantForm.slash_action_eqn O.h _ (Subgroup.mem_map_of_mem _ hn)
  have := O.prod_T n
  rw [hT, T_zero] at this
  have h1 : c (∏ i ∈ Finset.range n, O.y i) = 1 :=
    mul_right_cancel₀ O.Q_h_ne_zero (this.trans (one_mul _).symm)
  exact c_injective (h1.trans (map_one c).symm)

theorem cx_mul_Q (O : Orb M H γ k) : c O.x * Q ⇑O.h = Q ⇑O.h₁ := by
  rw [map_div₀, c_intSeriesC_eq_Q O.hh, c_intSeriesC_eq_Q O.hh₁, div_mul_cancel₀ _ O.Q_h_ne_zero]

theorem T_one (O : Orb M H γ k) : T γ k ⇑O.h 1 = Q ⇑O.h₁ := by
  rw [O.hhs]
  simp [T, pow_one]

theorem y_zero (O : Orb M H γ k) : O.y 0 = O.x := by
  have h0 := O.y_T 0
  rw [T_zero, zero_add, T_one, ← cx_mul_Q] at h0
  exact c_injective (mul_right_cancel₀ O.Q_h_ne_zero h0)

theorem x_mul_prod_eq_one (O : Orb M H γ k) {m : ℕ} (hn : γ ^ (m + 1) ∈ GammaH M H) :
    O.x * ∏ i ∈ Finset.range m, O.y (i + 1) = 1 := by
  have := O.prod_eq_one hn
  rw [Finset.prod_range_succ', y_zero] at this
  rw [mul_comm]
  exact this

end Orb

end Orbit

section Gauss

variable (p : ℕ) [Fact p.Prime]

abbrev toA (P : PowerSeries ℤ) : PowerSeries ↥(GaloisRep.ratLocalizedAt p) :=
  P.map (Int.castRingHom _)

theorem toA_subtype (P : PowerSeries ℤ) :
    (toA p P).map (GaloisRep.ratLocalizedAt p).subtype = P.map (Int.castRingHom ℚ) := by
  ext n
  simp [toA, PowerSeries.coeff_map]

theorem ofPowerSeries_toA (P : PowerSeries ℤ) :
    HahnSeries.ofPowerSeries ℤ ℚ ((toA p P).map (GaloisRep.ratLocalizedAt p).subtype) = intSeriesC ℚ P := by
  rw [toA_subtype]; rfl

theorem residue_comp_intCast :
    (GaloisRep.ratLocalizedAtResidue p).comp (Int.castRingHom _) = Int.castRingHom (ZMod p) :=
  RingHom.ext_int _ _

theorem toA_residue (P : PowerSeries ℤ) :
    (toA p P).map (GaloisRep.ratLocalizedAtResidue p) = P.map (Int.castRingHom (ZMod p)) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  exact RingHom.congr_fun (residue_comp_intCast p) (PowerSeries.coeff n P)

theorem toA_residue_ne_zero_iff (P : PowerSeries ℤ) :
    (toA p P).map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ↔ intSeriesC (ZMod p) P ≠ 0 := by
  rw [toA_residue, not_iff_not]
  constructor
  · intro h; simp [intSeriesC, h]
  · intro h
    exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)

theorem gauss_mul {x₁ x₂ : LaurentSeries ℚ} {a₁ a₁' a₂ a₂' : PowerSeries ↥(GaloisRep.ratLocalizedAt p)}
    (h₁ : a₁'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0)
    (e₁ : x₁ * HahnSeries.ofPowerSeries ℤ ℚ (a₁'.map (GaloisRep.ratLocalizedAt p).subtype) =
      HahnSeries.ofPowerSeries ℤ ℚ (a₁.map (GaloisRep.ratLocalizedAt p).subtype))
    (h₂ : a₂'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0)
    (e₂ : x₂ * HahnSeries.ofPowerSeries ℤ ℚ (a₂'.map (GaloisRep.ratLocalizedAt p).subtype) =
      HahnSeries.ofPowerSeries ℤ ℚ (a₂.map (GaloisRep.ratLocalizedAt p).subtype)) :
    (a₁' * a₂').map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      x₁ * x₂ * HahnSeries.ofPowerSeries ℤ ℚ ((a₁' * a₂').map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ ((a₁ * a₂).map (GaloisRep.ratLocalizedAt p).subtype) := by
  refine ⟨?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero h₁ h₂
  · rw [map_mul, map_mul, map_mul, map_mul, ← e₁, ← e₂]; ring

end Gauss

end ValNz

open ValNz in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [CharP K p]
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (k : ℤ) (h h₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (ph ph₁ : PowerSeries ℤ)
    (hh : ModularCurve.IsIntegralQExp h ph) (hh₁ : ModularCurve.IsIntegralQExp h₁ ph₁)
    (hhs : (⇑h₁ : UpperHalfPlane → ℂ) = ((⇑h : UpperHalfPlane → ℂ) ∣[k] γ))
    (h0 : ModularCurve.intSeriesC K ph ≠ 0) :
    ModularCurve.intSeriesC K ph₁ ≠ 0 := by

  have hKp : ∀ P : PowerSeries ℤ, intSeriesC K P ≠ 0 ↔ intSeriesC (ZMod p) P ≠ 0 := fun P =>
    not_congr (intSeriesC_eq_zero_iff (ZMod.castHom (dvd_refl p) K) P).symm
  have hp0 : intSeriesC (ZMod p) ph ≠ 0 := (hKp ph).mp h0
  have hred : ∀ P : PowerSeries ℤ, intSeriesC (ZMod p) P ≠ 0 ↔ P.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro P
    rw [not_iff_not]
    constructor
    · intro hP; exact HahnSeries.ofPowerSeries_injective (hP.trans (map_zero _).symm)
    · intro hP; simp [intSeriesC, hP]
  have hph : intSeriesC ℚ ph ≠ 0 := by
    intro hq
    apply (hred ph).mp hp0
    have h2 : ph.map (Int.castRingHom ℚ) = 0 :=
      HahnSeries.ofPowerSeries_injective (hq.trans (map_zero _).symm)
    have : ph = 0 := PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective (h2.trans (map_zero _).symm)
    rw [this, map_zero]
  rw [hKp]

  let O : Orb M H γ k := ⟨hγ, h, h₁, ph, ph₁, hh, hh₁, hhs, hph⟩

  obtain ⟨n, hn0, hn⟩ := exists_pow_mem_GammaH (H := H) hγ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩

  have hG : ∀ i, ∃ b b' : PowerSeries ↥(GaloisRep.ratLocalizedAt p),
      b'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      O.y i * HahnSeries.ofPowerSeries ℤ ℚ (b'.map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (b.map (GaloisRep.ratLocalizedAt p).subtype) := by
    intro i
    refine ModularCurve.exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul p M hpM hpM2
      H hHp (O.dpow i) O.x (O.y i)
      O.x_mem (O.y_mem i) (O.y_dia i) (toA p ph₁) (toA p ph) ?_ ?_
    · exact (toA_residue_ne_zero_iff p ph).mpr hp0
    · show intSeriesC ℚ ph₁ / intSeriesC ℚ ph * _ = _
      rw [ofPowerSeries_toA, ofPowerSeries_toA, div_mul_cancel₀ _ hph]

  have hP : ∀ m' : ℕ, ∃ B B' : PowerSeries ↥(GaloisRep.ratLocalizedAt p),
      B'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      (∏ i ∈ Finset.range m', O.y (i + 1)) *
          HahnSeries.ofPowerSeries ℤ ℚ (B'.map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (B.map (GaloisRep.ratLocalizedAt p).subtype) := by
    intro m'
    induction m' with
    | zero => exact ⟨1, 1, by rw [map_one]; exact one_ne_zero, by simp⟩
    | succ m' ih =>
      obtain ⟨B, B', hB', eB⟩ := ih
      obtain ⟨b, b', hb', eb⟩ := hG (m' + 1)
      refine ⟨B * b, B' * b', (gauss_mul p hB' eB hb' eb).1, ?_⟩
      rw [Finset.prod_range_succ]
      exact (gauss_mul p hB' eB hb' eb).2
  obtain ⟨B, B', hB', eB⟩ := hP m
  have hx1 : O.x * ∏ i ∈ Finset.range m, O.y (i + 1) = 1 := O.x_mul_prod_eq_one hn

  have key : intSeriesC ℚ ph * HahnSeries.ofPowerSeries ℤ ℚ (B'.map (GaloisRep.ratLocalizedAt p).subtype) =
      intSeriesC ℚ ph₁ * HahnSeries.ofPowerSeries ℤ ℚ (B.map (GaloisRep.ratLocalizedAt p).subtype) := by
    have hxdef : O.x * intSeriesC ℚ ph = intSeriesC ℚ ph₁ := div_mul_cancel₀ _ hph
    calc intSeriesC ℚ ph * HahnSeries.ofPowerSeries ℤ ℚ (B'.map (GaloisRep.ratLocalizedAt p).subtype)
        = (O.x * ∏ i ∈ Finset.range m, O.y (i + 1)) *
            (intSeriesC ℚ ph * HahnSeries.ofPowerSeries ℤ ℚ (B'.map (GaloisRep.ratLocalizedAt p).subtype)) := by
          rw [hx1, one_mul]
      _ = (O.x * intSeriesC ℚ ph) *
            ((∏ i ∈ Finset.range m, O.y (i + 1)) *
              HahnSeries.ofPowerSeries ℤ ℚ (B'.map (GaloisRep.ratLocalizedAt p).subtype)) := by ring
      _ = intSeriesC ℚ ph₁ * HahnSeries.ofPowerSeries ℤ ℚ (B.map (GaloisRep.ratLocalizedAt p).subtype) := by
          rw [hxdef, eB]

  have key' : (toA p ph * B').map (GaloisRep.ratLocalizedAt p).subtype =
      (toA p ph₁ * B).map (GaloisRep.ratLocalizedAt p).subtype := by
    have inj : Function.Injective (HahnSeries.ofPowerSeries ℤ ℚ) := HahnSeries.ofPowerSeries_injective
    apply inj
    rw [map_mul, map_mul, map_mul, map_mul, ofPowerSeries_toA, ofPowerSeries_toA]
    exact key
  have key'' : toA p ph * B' = toA p ph₁ * B :=
    PowerSeries.map_injective (GaloisRep.ratLocalizedAt p).subtype Subtype.val_injective key'
  have red := congrArg (PowerSeries.map (GaloisRep.ratLocalizedAtResidue p)) key''
  rw [map_mul, map_mul, toA_residue, toA_residue] at red
  have hl : ph.map (Int.castRingHom (ZMod p)) * B'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 :=
    mul_ne_zero ((hred ph).mp hp0) hB'
  rw [red] at hl
  rw [hred]
  exact left_ne_zero_of_mul hl

end
end S_ModularCurve_intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul
end P2MW
export P2MW.S_ModularCurve_intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul (solution)
