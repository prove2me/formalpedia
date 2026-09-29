-- Prove2me | solution 1 for ModularCurve.exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8e129ee7-68c0-53ec-9f13-8ae1efc5f3c5

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_comp_zero_iff_map_ker_le
import Theorems.Thm_ModularCurve_XHDRModelAtP_range_comp_zero_fibreMap_dia
import Theorems.Thm_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia
import Theorems.Thm_ModularCurve_exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
import Theorems.Thm_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Theorems.Thm_ModularCurve_XHDRModelAtP_map_ker_le_asIdeal_iff_map_ker_le_spec_map_tensor_asIdeal
import Theorems.Thm_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve~H1 ModularCurve~coeffEmb_injective ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

noncomputable section

namespace DiaGaussCore

theorem natCast_mem_maximalIdeal (p : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ((p : ↥A)) ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  exact_mod_cast hA

theorem isUnit_natCast_of_coprime (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) {n : ℕ} (hn : n.Coprime p) : IsUnit ((n : ↥A)) := by
  by_contra hu
  have hn' : ((n : ↥A)) ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hu
  have hp' := natCast_mem_maximalIdeal p A hA

  have hg : Nat.gcd n p = 1 := hn
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * n + v * p = 1 := by
    refine ⟨Nat.gcdA n p, Nat.gcdB n p, ?_⟩
    have := Nat.gcd_eq_gcd_ab n p
    rw [hg] at this
    push_cast at this
    linarith [this]
  have h1 : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (u : ↥A) hn') (Ideal.mul_mem_left _ (v : ↥A) hp')
    convert this using 1
    exact_mod_cast huv.symm
  exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem algebraMap_mem (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (r : R p) : algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) ∈ A := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime p A hA hr
  have hinv : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = ((r.den : AlgebraicClosure ℚ))⁻¹ := by
    have h1 : ((u⁻¹ : (↥A)ˣ) : ↥A) * (r.den : ↥A) = 1 := by rw [← hu, Units.inv_mul]
    have h2 := congrArg (fun a : ↥A => (a : AlgebraicClosure ℚ)) h1
    push_cast at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hr' : (r : ℚ) = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
  show algebraMap ℚ (AlgebraicClosure ℚ) r ∈ A
  rw [hr', map_div₀, map_intCast, map_natCast, div_eq_mul_inv, ← hinv]
  exact mul_mem (intCast_mem A _) ((u⁻¹ : (↥A)ˣ) : ↥A).2

def rho (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) : R p →+* ↥A where
  toFun r := ⟨algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ), algebraMap_mem p A hA r⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

theorem subtype_comp_rho (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    A.subtype.comp (rho p A hA) = algebraMap (R p) (AlgebraicClosure ℚ) := by
  ext r
  show algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) = algebraMap (R p) (AlgebraicClosure ℚ) r
  rw [IsScalarTower.algebraMap_apply (R p) ℚ (AlgebraicClosure ℚ)]
  rfl

end DiaGaussCore

namespace DiaGaussCore

section Red

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ}
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev O (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) : Type :=
  ↥(chartAlgInf p (ΓM M H) hj)

abbrev qexp {p M : ℕ} {H : Subgroup (ZMod M)ˣ} {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (b : O p M H hj) : LaurentSeries ℚ :=
  ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)

theorem coeffMap_R_injective (p : ℕ) : Function.Injective (coeffMap (algebraMap (R p) ℚ)) := fun x y h => by
  ext k
  have := congrArg (fun s : LaurentSeries ℚ => s.coeff k) h
  simp only [coeffMap_coeff] at this
  first
  | exact this
  | exact Subtype.val_injective this

theorem exists_unique_lift (b : O p M H hj) :
    ∃! y : LaurentSeries (R p), coeffMap (algebraMap (R p) ℚ) y = qexp b := by
  obtain ⟨y, hy⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt _ hj)).2 b
  exact ⟨y, hy, fun y' hy' => coeffMap_R_injective p (hy'.trans hy.symm)⟩

private def _root_.DiaGaussCore.lift (b : O p M H hj) : LaurentSeries (R p) := (exists_unique_lift hj b).choose

p2m_export "DiaGaussCore" "lift"
theorem coeffMap_lift (b : O p M H hj) : coeffMap (algebraMap (R p) ℚ) (lift hj b) = qexp b :=
  (exists_unique_lift hj b).choose_spec.1

theorem lift_eq_of_coeffMap_eq {b : O p M H hj} {y : LaurentSeries (R p)}
    (hy : coeffMap (algebraMap (R p) ℚ) y = qexp b) : lift hj b = y :=
  ((exists_unique_lift hj b).choose_spec.2 y hy).symm

theorem lift_mul (b c : O p M H hj) : lift hj (b * c) = lift hj b * lift hj c := by
  apply lift_eq_of_coeffMap_eq
  rw [map_mul, coeffMap_lift, coeffMap_lift]
  rfl

theorem lift_add (b c : O p M H hj) : lift hj (b + c) = lift hj b + lift hj c := by
  apply lift_eq_of_coeffMap_eq
  rw [map_add, coeffMap_lift, coeffMap_lift]
  rfl

theorem lift_one : lift hj (1 : O p M H hj) = 1 := by
  apply lift_eq_of_coeffMap_eq
  rw [map_one]
  rfl

theorem lift_zero : lift hj (0 : O p M H hj) = 0 := by
  apply lift_eq_of_coeffMap_eq
  rw [map_zero]
  rfl

def red {κ : Type} [CommRing κ] (τ : R p →+* κ) : O p M H hj →+* LaurentSeries κ where
  toFun b := coeffMap τ (lift hj b)
  map_one' := by rw [lift_one, map_one]
  map_mul' b c := by rw [lift_mul, map_mul]
  map_zero' := by rw [lift_zero, map_zero]
  map_add' b c := by rw [lift_add, map_add]

theorem red_apply {κ : Type} [CommRing κ] (τ : R p →+* κ) (b : O p M H hj) :
    red hj τ b = coeffMap τ (lift hj b) := rfl

theorem red_eq_of_coeffMap_eq {κ : Type} [CommRing κ] (τ : R p →+* κ) (b : O p M H hj) (y : LaurentSeries (R p))
    (hy : coeffMap (algebraMap (R p) ℚ) y = qexp b) : red hj τ b = coeffMap τ y := by
  rw [red_apply, lift_eq_of_coeffMap_eq hj hy]

end Red

section Contract

variable {R κ O' L : Type*} [CommRing R] [CommRing κ] [Algebra R κ] [CommRing O'] [Algebra R O']
  [CommRing L] [IsDomain L] [Algebra κ L]

theorem mem_ker_of_pow_tmul_mem (red : O' →+* L)
    (hcompat : ∀ r : R, red (algebraMap R O' r) = algebraMap κ L (algebraMap R κ r)) (b : O') (n : ℕ)
    (hb : (Algebra.TensorProduct.includeRight (R := R) (A := κ) b) ^ n ∈
      Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')) (RingHom.ker red)) :
    b ∈ RingHom.ker red := by
  letI : Algebra R L := (red.comp (algebraMap R O')).toAlgebra
  let redA : O' →ₐ[R] L := { red with commutes' := fun _ => rfl }
  let fA : κ →ₐ[R] L := { algebraMap κ L with commutes' := fun r => (hcompat r).symm }

  let ev : κ ⊗[R] O' →ₐ[R] L :=
    Algebra.TensorProduct.lift fA redA (fun _ _ => Commute.all _ _)
  have hev : ∀ c : O', ev (Algebra.TensorProduct.includeRight (R := R) (A := κ) c) = red c := by
    intro c
    simp [ev, redA, fA, Algebra.TensorProduct.includeRight_apply]
  have hmap : Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')) (RingHom.ker red) ≤
      RingHom.ker ev.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show ev (Algebra.TensorProduct.includeRight c) = 0
    rw [hev]
    exact hc
  have h0 : ev ((Algebra.TensorProduct.includeRight (R := R) (A := κ) b) ^ n) = 0 := hmap hb
  rw [map_pow, hev] at h0
  exact pow_eq_zero_iff'.mp h0 |>.1 |> fun h => h

end Contract

end DiaGaussCore

namespace DiaGaussCore

section Stable

variable {R κ O' L : Type*} [CommRing R] [CommRing κ] [Algebra R κ] [CommRing O'] [Algebra R O']
  [CommRing L] [IsDomain L] [Algebra κ L]

theorem map_comp_includeRight' (τ : O' →ₐ[R] O') :
    (Algebra.TensorProduct.map (AlgHom.id R κ) τ).comp
        (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')) =
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')).comp τ := by
  ext b
  simp

theorem map_ker_le_of_forall (red : O' →+* L)
    (hcompat : ∀ r : R, red (algebraMap R O' r) = algebraMap κ L (algebraMap R κ r)) (τ : O' →ₐ[R] O')
    (H1 : ∀ z : PrimeSpectrum (κ ⊗[R] O'),
      Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')) (RingHom.ker red) ≤ z.asIdeal →
      Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')) (RingHom.ker red) ≤
        z.asIdeal.comap (Algebra.TensorProduct.map (AlgHom.id R κ) τ)) :
    ∀ b ∈ RingHom.ker red, τ b ∈ RingHom.ker red := by
  set I := Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')) (RingHom.ker red) with hI
  set φ := Algebra.TensorProduct.map (AlgHom.id R κ) τ with hφ

  have h1 : Ideal.map φ I ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro J ⟨hIJ, hJ⟩
    rw [Ideal.map_le_iff_le_comap]
    exact H1 ⟨J, hJ⟩ hIJ
  intro b hb
  have h3 : Algebra.TensorProduct.includeRight (R := R) (A := κ) (τ b) ∈ I.radical := by
    apply h1
    have hφb : Algebra.TensorProduct.includeRight (R := R) (A := κ) (τ b) =
        φ (Algebra.TensorProduct.includeRight (R := R) (A := κ) b) := by
      rw [hφ]
      simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
    rw [hφb]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hb)
  obtain ⟨n, hn⟩ := h3
  exact mem_ker_of_pow_tmul_mem red hcompat (τ b) n hn

theorem ker_stable (red : O' →+* L)
    (hcompat : ∀ r : R, red (algebraMap R O' r) = algebraMap κ L (algebraMap R κ r)) (σ : O' ≃ₐ[R] O')
    (H : ∀ z : PrimeSpectrum (κ ⊗[R] O'),
      Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')) (RingHom.ker red) ≤ z.asIdeal ↔
      Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')) (RingHom.ker red) ≤
        z.asIdeal.comap (Algebra.TensorProduct.map (AlgHom.id R κ) (σ : O' →ₐ[R] O'))) :
    ∀ b ∈ RingHom.ker red, σ b ∈ RingHom.ker red ∧ σ.symm b ∈ RingHom.ker red := by
  intro b hb
  refine ⟨map_ker_le_of_forall (κ := κ) red hcompat (σ : O' →ₐ[R] O') (fun z h => (H z).mp h) b hb, ?_⟩
  refine map_ker_le_of_forall (κ := κ) red hcompat (σ.symm : O' →ₐ[R] O') (fun z hz => ?_) b hb

  let φ' := Algebra.TensorProduct.map (AlgHom.id R κ) (σ.symm : O' →ₐ[R] O')
  let φ := Algebra.TensorProduct.map (AlgHom.id R κ) (σ : O' →ₐ[R] O')
  have hcomp : φ'.comp φ = AlgHom.id R _ := by
    apply Algebra.TensorProduct.ext'
    intro a c
    simp [φ, φ', Algebra.TensorProduct.map_tmul]
  let z' : PrimeSpectrum (κ ⊗[R] O') := ⟨z.asIdeal.comap φ', Ideal.IsPrime.comap _⟩
  have hz' : z'.asIdeal.comap φ = z.asIdeal := by
    show (z.asIdeal.comap φ'.toRingHom).comap φ.toRingHom = z.asIdeal
    rw [Ideal.comap_comap]
    have : φ'.toRingHom.comp φ.toRingHom = RingHom.id _ := congrArg AlgHom.toRingHom hcomp
    rw [this, Ideal.comap_id]
  have := (H z').mpr (by rw [hz']; exact hz)
  exact this

end Stable

end DiaGaussCore

namespace DiaGaussCore
namespace GC

abbrev Rp (p : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt p)

scoped instance (p : ℕ) [hp : Fact p.Prime] : IsDiscreteValuationRing (Rp p) :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp.out

theorem maximalIdeal_eq (p : ℕ) [hp : Fact p.Prime] :
    IsLocalRing.maximalIdeal (Rp p) = Ideal.span {(p : Rp p)} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp.out

theorem residue_eq_zero_of_mem (p : ℕ) [hp : Fact p.Prime] {r : Rp p} (hr : r ∈ IsLocalRing.maximalIdeal (Rp p)) :
    GaloisRep.ratLocalizedAtResidue p r = 0 := by
  rw [maximalIdeal_eq, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem isUnit_of_residue_ne_zero (p : ℕ) [hp : Fact p.Prime] {r : Rp p}
    (hr : GaloisRep.ratLocalizedAtResidue p r ≠ 0) : IsUnit r := by
  by_contra h
  exact hr (residue_eq_zero_of_mem p ((IsLocalRing.mem_maximalIdeal _).mpr h))

theorem exists_eq_mul_of_residue_eq_zero (p : ℕ) [hp : Fact p.Prime] {r : Rp p}
    (hr : GaloisRep.ratLocalizedAtResidue p r = 0) : ∃ s : Rp p, r = p * s := by
  have h : ¬ IsUnit r := fun hu => (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hr
  have hm : r ∈ IsLocalRing.maximalIdeal (Rp p) := (IsLocalRing.mem_maximalIdeal _).mpr h
  rw [maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hm

abbrev psQ (p : ℕ) (x : PowerSeries (Rp p)) : LaurentSeries ℚ :=
  HahnSeries.ofPowerSeries ℤ ℚ (x.map (GaloisRep.ratLocalizedAt p).subtype)

theorem psQ_injective (p : ℕ) : Function.Injective (psQ p) := fun x y h =>
  PowerSeries.map_injective _ Subtype.coe_injective (HahnSeries.ofPowerSeries_injective h)

theorem subtype_comp_intCast (p : ℕ) :
    (GaloisRep.ratLocalizedAt p).subtype.comp (Int.castRingHom (Rp p)) = Int.castRingHom ℚ :=
  RingHom.ext_int _ _

theorem residue_comp_intCast (p : ℕ) [Fact p.Prime] :
    (GaloisRep.ratLocalizedAtResidue p).comp (Int.castRingHom (Rp p)) = Int.castRingHom (ZMod p) :=
  RingHom.ext_int _ _

theorem jqModC_rat_ne_zero : jqModC ℚ ≠ 0 := by
  intro h
  have := congrArg (fun s : LaurentSeries ℚ => s.coeff (-1)) h
  simp only [coeff_jqModC_neg_one, HahnSeries.coeff_zero] at this
  exact one_ne_zero this

theorem single_one_mul_jqModC :
    HahnSeries.single (1 : ℤ) (1 : ℚ) * jqModC ℚ = HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := by
  rw [jqModC, ← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel, one_mul]
  exact one_mul _

theorem map_map_ps {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] (f : A →+* B) (g : B →+* C)
    (x : PowerSeries A) : (x.map f).map g = x.map (g.comp f) := by
  ext n
  simp only [PowerSeries.coeff_map, RingHom.comp_apply]

theorem psQ_jNum (p : ℕ) : psQ p (jNum.map (Int.castRingHom (Rp p))) = HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := by
  rw [psQ, map_map_ps, subtype_comp_intCast]

theorem psQ_X (p : ℕ) : psQ p PowerSeries.X = HahnSeries.single (1 : ℤ) (1 : ℚ) := by
  rw [psQ, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem jNum_map_residue_ne_zero (p : ℕ) [Fact p.Prime] :
    (jNum.map (Int.castRingHom (Rp p))).map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
  rw [map_map_ps, residue_comp_intCast]
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one, map_zero] at this
  exact one_ne_zero this

theorem coeff_zero_inv_jqModC : ((jqModC ℚ)⁻¹).coeff 0 = 0 := by
  have hu : jNumQ * jNumQ.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNumQ]; rfl)
  have hj : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
  have hinv : (jqModC ℚ)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ.invOfUnit 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hj, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
      ← map_mul, hu, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
    rfl
  rw [hinv, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_X_mul]

abbrev FG (Γ : Subgroup SL(2, ℤ)) : Type := ↥(qExpFunctionFieldC ℚ Γ)

abbrev OO (Γ : Subgroup SL(2, ℤ)) (p : ℕ) (j : FG Γ) [Fact (j ≠ 0)] : Type :=
  ↥(TwoChartIntegralModel.chartAlgInf (Rp p) (FG Γ) j)

abbrev Aj (Γ : Subgroup SL(2, ℤ)) (p : ℕ) (j : FG Γ) : Subalgebra (Rp p) (FG Γ) :=
  Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))

section Frame

variable (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [hp : Fact p.Prime]
variable (j : FG Γ) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
variable (W₀ : ValuationSubring (FG Γ))
  (hW₀ : ∀ f : FG Γ, f ∈ W₀ ↔
    ∃ a a' : PowerSeries (Rp p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      (f : LaurentSeries ℚ) * psQ p a' = psQ p a)

include hW₀ in

theorem algebraMap_mem (r : Rp p) : algebraMap (Rp p) (FG Γ) r ∈ W₀ := by
  rw [hW₀]
  refine ⟨PowerSeries.C r, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
  rw [psQ, psQ, map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  have h1 : ((algebraMap (Rp p) (FG Γ) r : FG Γ) : LaurentSeries ℚ) = HahnSeries.single 0 (r : ℚ) := by
    first
    | exact algebraMap_laurentSeries_eq_single (r : ℚ)
    | rfl
    | (change algebraMap ℚ (LaurentSeries ℚ) (r : ℚ) = _; exact algebraMap_laurentSeries_eq_single ℚ (r : ℚ))
  rw [h1]
  rfl

include hj hW₀ in

theorem inv_j_mem : (j⁻¹ : FG Γ) ∈ W₀ := by
  rw [hW₀]
  refine ⟨PowerSeries.X, jNum.map (Int.castRingHom (Rp p)), jNum_map_residue_ne_zero p, ?_⟩
  rw [psQ_jNum, psQ_X, ← single_one_mul_jqModC, ← hj]
  show ((j : FG Γ) : LaurentSeries ℚ)⁻¹ * (HahnSeries.single 1 1 * (j : LaurentSeries ℚ)) = HahnSeries.single 1 1
  rw [mul_left_comm, inv_mul_cancel₀ (hj ▸ jqModC_rat_ne_zero), mul_one]

include hj hW₀ in

theorem j_mem : (j : FG Γ) ∈ W₀ := by
  rw [hW₀]
  refine ⟨jNum.map (Int.castRingHom (Rp p)), PowerSeries.X, by rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero, ?_⟩
  rw [psQ_jNum, psQ_X, ← single_one_mul_jqModC, ← hj, mul_comm]

include hj hW₀ in

theorem adjoin_subset (x : FG Γ) (hx : x ∈ Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) : x ∈ W₀ := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact inv_j_mem Γ p j hj W₀ hW₀
  | algebraMap r => exact algebraMap_mem Γ p W₀ hW₀ r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

include hj hW₀ in

theorem coe_mem (b : OO Γ p j) : (b : FG Γ) ∈ W₀ := by
  have hb : IsIntegral (Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) (b : FG Γ) := b.2
  let φ : ↥(Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) →+* ↥W₀ :=
    (algebraMap ↥(Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) (FG Γ)).codRestrict W₀.toSubring
      (fun x => adjoin_subset Γ p j hj W₀ hW₀ x x.2)
  have hcomp : (algebraMap ↥W₀ (FG Γ)).comp φ = (RingHom.id (FG Γ)).comp (algebraMap _ (FG Γ)) :=
    RingHom.ext fun _ => rfl
  have hint : IsIntegral ↥W₀ (b : FG Γ) := hb.map_of_comp_eq φ (RingHom.id (FG Γ)) hcomp
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W₀) (K := FG Γ)).mp hint
  rw [← hy]
  exact y.2

def toW₀ : OO Γ p j →+* ↥W₀ :=
  (algebraMap (OO Γ p j) (FG Γ)).codRestrict W₀.toSubring (fun b => coe_mem Γ p j hj W₀ hW₀ b)

def centre : Ideal (OO Γ p j) := Ideal.comap (toW₀ Γ p j hj W₀ hW₀) (IsLocalRing.maximalIdeal ↥W₀)

theorem mem_centre_iff (b : OO Γ p j) : b ∈ centre Γ p j hj W₀ hW₀ ↔ (b : FG Γ) ∈ W₀.nonunits := by
  rw [centre, Ideal.mem_comap, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · intro h; exact ⟨coe_mem Γ p j hj W₀ hW₀ b, h⟩
  · rintro ⟨_, h⟩; exact h

theorem mem_centre_iff_not_isUnit (b : OO Γ p j) :
    b ∈ centre Γ p j hj W₀ hW₀ ↔ ¬ IsUnit (toW₀ Γ p j hj W₀ hW₀ b) := by
  rw [centre, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem centre_isPrime : (centre Γ p j hj W₀ hW₀).IsPrime := by
  unfold centre
  exact Ideal.comap_isPrime _ _

include hW₀ in

theorem inv_natCast_not_mem : ((p : FG Γ))⁻¹ ∉ W₀ := by
  rw [hW₀]
  rintro ⟨a, a', ha', h⟩
  apply ha'
  have hp0 : (p : FG Γ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h3 : ((p : FG Γ) : LaurentSeries ℚ) * psQ p a = psQ p ((p : PowerSeries (Rp p)) * a) := by
    rw [psQ, psQ, map_mul, map_natCast, map_mul, map_natCast]
    push_cast
    rfl
  have h2 : psQ p a' = psQ p ((p : PowerSeries (Rp p)) * a) := by
    rw [← h3, ← h, ← mul_assoc]
    have hpp : ((p : FG Γ) : LaurentSeries ℚ) * ((((p : FG Γ))⁻¹ : FG Γ) : LaurentSeries ℚ) = 1 := by
      rw [← show (((p : FG Γ) * (p : FG Γ)⁻¹ : FG Γ) : LaurentSeries ℚ) =
          ((p : FG Γ) : LaurentSeries ℚ) * ((((p : FG Γ))⁻¹ : FG Γ) : LaurentSeries ℚ) from by push_cast; rfl,
        mul_inv_cancel₀ hp0]
      rfl
    rw [hpp, one_mul]
  rw [psQ_injective p h2, map_mul, map_natCast, ← map_natCast (PowerSeries.C (R := ZMod p)) p, ZMod.natCast_self,
    map_zero, zero_mul]

theorem natCast_mem_centre : (p : OO Γ p j) ∈ centre Γ p j hj W₀ hW₀ := by
  rw [mem_centre_iff_not_isUnit]
  intro hu
  obtain ⟨u, hu⟩ := hu
  apply inv_natCast_not_mem Γ p W₀ hW₀
  have hcoe : ((toW₀ Γ p j hj W₀ hW₀ (p : OO Γ p j) : ↥W₀) : FG Γ) = (p : FG Γ) := by
    rw [map_natCast]; norm_cast
  have h1 : ((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) = 1 := Units.inv_mul u
  rw [hu] at h1
  have h2 := congrArg (fun z : ↥W₀ => (z : FG Γ)) h1
  first
    | (simp only [Subring.coe_mul, hcoe] at h2)
    | (simp only [MulMemClass.coe_mul, OneMemClass.coe_one, Subring.coe_one, hcoe] at h2)
    | (push_cast [hcoe] at h2)
  have hp0 : (p : FG Γ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : (((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : FG Γ) = (p : FG Γ)⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [← this]
  exact ((u⁻¹ : (↥W₀)ˣ) : ↥W₀).2

include hj hW₀ in

theorem jInv_not_mem_centre : TwoChartIntegralModel.jInvChartInf (Rp p) (FG Γ) j ∉ centre Γ p j hj W₀ hW₀ := by
  rw [mem_centre_iff_not_isUnit, not_not]
  refine IsUnit.of_mul_eq_one ⟨(j : FG Γ), j_mem Γ p j hj W₀ hW₀⟩ (Subtype.ext ?_)
  show ((j⁻¹ : FG Γ)) * (j : FG Γ) = 1
  exact inv_mul_cancel₀ (Fact.out : j ≠ 0)

include hj in
omit hp in
theorem coeff_zero_jInv :
    (((TwoChartIntegralModel.jInvChartInf (Rp p) (FG Γ) j : FG Γ)) : LaurentSeries ℚ).coeff 0 = 0 := by
  rw [TwoChartIntegralModel.coe_jInvChartInf]
  rw [show ((j⁻¹ : FG Γ) : LaurentSeries ℚ) = ((j : FG Γ) : LaurentSeries ℚ)⁻¹ from by push_cast; rfl, hj]
  exact coeff_zero_inv_jqModC

omit hp in

theorem exists_powerSeries_of_forall_coeff_neg_eq_zero (y : LaurentSeries (Rp p))
    (hy : ∀ n : ℤ, n < 0 → y.coeff n = 0) :
    ∃ Y : PowerSeries (Rp p), HahnSeries.ofPowerSeries ℤ (Rp p) Y = y := by
  refine ⟨PowerSeries.mk fun n => y.coeff n, HahnSeries.ext (funext fun k => ?_)⟩
  rcases lt_or_ge k 0 with hk | hk
  · rw [hy k hk]
    exact ofPowerSeries_coeff_of_neg (PowerSeries.mk fun n => y.coeff n) hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

private theorem _root_.DiaGaussCore.GC.coeffMap_ofPowerSeries {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (Y : PowerSeries A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A Y) = HahnSeries.ofPowerSeries ℤ B (Y.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg Y hk, ofPowerSeries_coeff_of_neg (Y.map f) hk, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

p2m_export "DiaGaussCore.GC" "coeffMap_ofPowerSeries"
include hj hW₀ in

theorem exists_psQ_eq (b : OO Γ p j) : ∃ Y : PowerSeries (Rp p), psQ p Y = ((b : FG Γ) : LaurentSeries ℚ) := by
  obtain ⟨y, hy⟩ := (exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC Γ p j hj).2 b
  have hj' : ∀ n : ℤ, n ≤ 0 → ((j : FG Γ) : LaurentSeries ℚ)⁻¹.coeff n = 0 := by
    intro n hn
    rw [hj]
    rcases hn.lt_or_eq with hlt | rfl
    · have hu : jNumQ * jNumQ.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNumQ]; rfl)
      have hjq : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
      have hinv : (jqModC ℚ)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ.invOfUnit 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [hjq, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
          ← map_mul, hu, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
        rfl
      rw [hinv]
      exact ofPowerSeries_coeff_of_neg _ hlt
    · exact coeff_zero_inv_jqModC
  obtain ⟨ε, hε⟩ := exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero (qExpFunctionFieldC ℚ Γ) p j hj'
  have hneg : ∀ n : ℤ, n < 0 → y.coeff n = 0 := by
    intro n hn
    have h := (hε b).1 n hn
    rw [← hy, coeffMap_coeff] at h
    exact Subtype.coe_injective (by simpa using h)
  obtain ⟨Y, hY⟩ := exists_powerSeries_of_forall_coeff_neg_eq_zero p y hneg
  refine ⟨Y, ?_⟩
  rw [← hy, ← hY, psQ, coeffMap_ofPowerSeries]
  rfl

end Frame

end DiaGaussCore.GC
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore.GC"
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore"

namespace DiaGaussCore

open DiaGaussCore.GC

section Ker

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ}
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem tau_eq_zero_iff (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (r : R p) :
    (IsLocalRing.residue ↥A).comp (rho p A hA) r = 0 ↔ GaloisRep.ratLocalizedAtResidue p r = 0 := by
  constructor
  · intro h
    by_contra hne
    have hu : IsUnit r := isUnit_of_residue_ne_zero p hne
    have hu' : IsUnit (rho p A hA r) := hu.map _
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff] at h
    exact (IsLocalRing.mem_maximalIdeal _).mp h hu'
  · intro h
    obtain ⟨s, rfl⟩ := exists_eq_mul_of_residue_eq_zero p h
    rw [map_mul, RingHom.comp_apply, map_natCast, (IsLocalRing.residue_eq_zero_iff _).mpr (natCast_mem_maximalIdeal p A hA),
      zero_mul]

theorem map_tau_eq_zero_iff (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (Y : PowerSeries (R p)) :
    Y.map ((IsLocalRing.residue ↥A).comp (rho p A hA)) = 0 ↔ Y.map (GaloisRep.ratLocalizedAtResidue p) = 0 := by
  constructor <;> intro h <;> ext n <;>
  · have := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_map, map_zero] at this ⊢
    first
    | exact (tau_eq_zero_iff A hA _).mp this
    | exact (tau_eq_zero_iff A hA _).mpr this

variable (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (ΓM M H)))
  (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (ΓM M H)), f ∈ W₀ ↔
    ∃ a a' : PowerSeries (R p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      (f : LaurentSeries ℚ) * psQ p a' = psQ p a)
  (𝔮 : Ideal (O p M H hj))
  (h𝔮 : ∀ b : O p M H hj, b ∈ 𝔮 ↔ (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₀.nonunits)

include hW₀ h𝔮 in

theorem mem_iff_red_eq_zero (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (b : O p M H hj) :
    b ∈ 𝔮 ↔ red hj ((IsLocalRing.residue ↥A).comp (rho p A hA)) b = 0 := by
  haveI : Fact (jAt (ΓM M H) hj ≠ 0) := inferInstance
  obtain ⟨Y, hY⟩ := exists_psQ_eq (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt _ hj) W₀ hW₀ b

  have hlift : lift hj b = HahnSeries.ofPowerSeries ℤ (R p) Y := by
    apply lift_eq_of_coeffMap_eq
    rw [ModularCurve.coeffMap_ofPowerSeries]
    exact hY
  have hred : red hj ((IsLocalRing.residue ↥A).comp (rho p A hA)) b =
      HahnSeries.ofPowerSeries ℤ _ (Y.map ((IsLocalRing.residue ↥A).comp (rho p A hA))) := by
    rw [red_apply, hlift, ModularCurve.coeffMap_ofPowerSeries]
  rw [hred, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective), map_tau_eq_zero_iff A hA, h𝔮]

  have hbW : (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₀ := coe_mem (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt _ hj) W₀ hW₀ b
  set bF : ↥(qExpFunctionFieldC ℚ (ΓM M H)) := (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) with hbF
  have hpsQ_mul : ∀ c c' : PowerSeries (R p), psQ p (c * c') = psQ p c * psQ p c' := fun c c' => by
    simp only [psQ, map_mul]
  constructor
  · intro hnu
    by_contra hY0

    have hb0 : bF ≠ 0 := by
      intro h0
      apply hY0
      have : psQ p Y = psQ p 0 := by rw [hY, h0]; simp [psQ]
      rw [psQ_injective p this, map_zero]

    have hinv : bF⁻¹ ∈ W₀ := by
      rw [hW₀]
      refine ⟨1, Y, hY0, ?_⟩
      have : ((bF⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((bF : LaurentSeries ℚ))⁻¹ := by
        push_cast; rfl
      rw [this, hY, inv_mul_cancel₀ (by exact_mod_cast hb0 : (bF : LaurentSeries ℚ) ≠ 0)]
      simp [psQ]

    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hnu
    obtain ⟨hmem, hmax⟩ := hnu
    apply (IsLocalRing.mem_maximalIdeal _).mp hmax
    refine ⟨⟨⟨bF, hmem⟩, ⟨bF⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩, rfl⟩
  · intro hY0
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    refine ⟨hbW, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu⟩ := hu
    have hb0 : bF ≠ 0 := by
      intro h0
      apply u.ne_zero
      exact Subtype.ext (by rw [hu]; exact h0)
    have hinv : bF⁻¹ ∈ W₀ := by
      have : (((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = bF⁻¹ := by
        have h1 : ((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) = 1 := Units.inv_mul u
        have h2 := congrArg (fun w : ↥W₀ => (w : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) h1
        simp only [hu] at h2
        push_cast at h2
        exact eq_inv_of_mul_eq_one_left h2
      rw [← this]
      exact ((u⁻¹ : (↥W₀)ˣ) : ↥W₀).2
    rw [hW₀] at hinv
    obtain ⟨c, c', hc', e⟩ := hinv
    apply hc'

    have e' : psQ p c' = psQ p (Y * c) := by
      rw [hpsQ_mul, hY]
      have : ((bF⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((bF : LaurentSeries ℚ))⁻¹ := by
        push_cast; rfl
      rw [this] at e
      have hbL : (bF : LaurentSeries ℚ) ≠ 0 := by exact_mod_cast hb0
      calc psQ p c' = (bF : LaurentSeries ℚ) * (((bF : LaurentSeries ℚ))⁻¹ * psQ p c') := by
            rw [← mul_assoc, mul_inv_cancel₀ hbL, one_mul]
        _ = (bF : LaurentSeries ℚ) * psQ p c := by rw [e]
    rw [psQ_injective p e', map_mul, hY0, zero_mul]

end Ker
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore.GC"

end DiaGaussCore
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore.GC"

namespace DiaGaussCore

section RedAlg

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ}
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem qexp_algebraMap (r : R p) : qexp (algebraMap (R p) (O p M H hj) r) = HahnSeries.single 0 (r : ℚ) := by
  show ((((algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj) r : ↥(chartAlgInf p (ΓM M H) hj)) :
        ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ)) = HahnSeries.single 0 (r : ℚ)
  rw [Subalgebra.coe_algebraMap]
  first
  | exact algebraMap_laurentSeries_eq_single (r : ℚ)
  | exact algebraMap_laurentSeries_eq_single ℚ (r : ℚ)
  | rfl

theorem lift_algebraMap (r : R p) : lift hj (algebraMap (R p) (O p M H hj) r) = HahnSeries.single 0 r := by
  apply lift_eq_of_coeffMap_eq
  rw [coeffMap_single, qexp_algebraMap]
  rfl

theorem red_algebraMap {κ : Type} [CommRing κ] (τ : R p →+* κ) (r : R p) :
    red hj τ (algebraMap (R p) (O p M H hj) r) = HahnSeries.C (τ r) := by
  rw [red_apply, lift_algebraMap, coeffMap_single]
  rfl

theorem red_ker_stable {κ : Type} [Field κ] (τ : R p →+* κ) (σ : O p M H hj ≃ₐ[R p] O p M H hj)
    (Hpt : letI : Algebra (R p) κ := τ.toAlgebra
      ∀ z : PrimeSpectrum (κ ⊗[R p] O p M H hj),
        Ideal.map (Algebra.TensorProduct.includeRight (R := R p) (A := κ) (B := O p M H hj))
          (RingHom.ker (red hj τ)) ≤ z.asIdeal ↔
        Ideal.map (Algebra.TensorProduct.includeRight (R := R p) (A := κ) (B := O p M H hj))
          (RingHom.ker (red hj τ)) ≤
          z.asIdeal.comap (Algebra.TensorProduct.map (AlgHom.id (R p) κ) (σ : O p M H hj →ₐ[R p] O p M H hj))) :
    ∀ b : O p M H hj, red hj τ b = 0 → red hj τ (σ b) = 0 ∧ red hj τ (σ.symm b) = 0 := by
  letI : Algebra (R p) κ := τ.toAlgebra
  have hcompat : ∀ r : R p, red hj τ (algebraMap (R p) (O p M H hj) r) =
      algebraMap κ (LaurentSeries κ) (algebraMap (R p) κ r) := by
    intro r
    rw [red_algebraMap, LaurentSeries.algebraMap_apply]
    rfl
  intro b hb
  exact ker_stable (κ := κ) (red hj τ) hcompat σ Hpt b hb

end RedAlg
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore.GC"

end DiaGaussCore
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore.GC"

namespace DiaGaussCore

section Main

theorem coeffEmb_injective (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (coeffEmb L) := fun x y h => by
  ext k
  have := congrArg (fun s : LaurentSeries L => s.coeff k) h
  simp only [coeffEmb_coeff] at this
  exact (algebraMap ℚ L).injective this

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem dia_apply_eq_symm {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (d : (ZMod M)ˣ)
    (σ : O p M H hj ≃ₐ[R p] O p M H hj)
    (hσ : ∀ b : O p M H hj, coeffEmb (AlgebraicClosure ℚ) (qexp (σ b)) =
      (((diamondAutHBar M H d).symm ⟨coeffEmb (AlgebraicClosure ℚ) (qexp b),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ :
        ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))
    (a : O p M H hj) :
    ((diamondAutHBar M H d ⟨coeffEmb (AlgebraicClosure ℚ) (qexp a),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ :
        ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (qexp (σ.symm a)) := by
  have h := hσ (σ.symm a)
  rw [AlgEquiv.apply_symm_apply] at h

  have h' : (⟨coeffEmb (AlgebraicClosure ℚ) (qexp a),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ :
        ↥(xHFunctionFieldBar M H)) =
      (diamondAutHBar M H d).symm ⟨coeffEmb (AlgebraicClosure ℚ) (qexp (σ.symm a)),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ((σ.symm a : O p M H hj) : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ :=
    Subtype.ext h
  rw [h', AlgEquiv.apply_symm_apply]

end Main
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore.GC"

end DiaGaussCore
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore.GC"

namespace DiaGaussCore

theorem T_mem_GammaH {M : ℕ} {H : Subgroup (ZMod M)ˣ} : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show (((ModularGroup.T) 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    simp [ModularGroup.T]
  rw [this]
  exact one_mem H

end DiaGaussCore
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul.DiaGaussCore.GC"

open DiaGaussCore DiaGaussCore.GC in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ) (x y : LaurentSeries ℚ)
    (hx : x ∈ ModularCurve.xHFunctionField M H) (hy : y ∈ ModularCurve.xHFunctionField M H)
    (hσ : ((ModularCurve.diamondAutHBar M H d
        ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) x,
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hx⟩ :
          ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.coeffEmb (AlgebraicClosure ℚ) y)
    (a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p))
    (ha' : a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0)
    (hxa : x * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
      HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)) :
    ∃ b b' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), b'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      y * HahnSeries.ofPowerSeries ℤ ℚ (b'.map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (b.map (GaloisRep.ratLocalizedAt p).subtype) := by

  have hj0 : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)) :=
    intFormRatiosC_subset ℚ ⊤ (ModularCurve.jqModC_mem_intFormRatiosC ℚ ⊤)

  obtain ⟨𝔓, θ, -, -⟩ := ModularCurve.exists_xHDRModelAtP_atkinLehner_generic p M H hpM hpM2 hHp hj0

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  haveI : CharP (IsLocalRing.ResidueField ↥A) p :=
    IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal ↥A p (natCast_mem_maximalIdeal p A hA)
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  let ρ : R p →+* ↥A := rho p A hA
  have hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ) := subtype_comp_rho p A hA
  let τ : R p →+* IsLocalRing.ResidueField ↥A := (IsLocalRing.residue ↥A).comp ρ
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := τ.toAlgebra
  have halg : algebraMap (R p) (IsLocalRing.ResidueField ↥A) = (IsLocalRing.residue ↥A).comp ρ := rfl

  obtain ⟨σ, hσO⟩ := ModularCurve.exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm p M H hj0 d
  have hdia := 𝔓.iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf d σ hσO

  let rd : O p M H hj0 →+* LaurentSeries (IsLocalRing.ResidueField ↥A) := red hj0 τ
  have hred : ∀ (b : O p M H hj0) (z : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) z = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        rd b = coeffMap ((IsLocalRing.residue ↥A).comp ρ) z := fun b z hz => red_eq_of_coeffMap_eq hj0 τ b z hz
  have HP5 := fun z => 𝔓.map_ker_le_asIdeal_iff_map_ker_le_spec_map_tensor_asIdeal A hA ρ hρ halg rd hred d σ hdia z
  have Hpt : ∀ z : PrimeSpectrum ((IsLocalRing.ResidueField ↥A) ⊗[R p] O p M H hj0),
      Ideal.map (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := O p M H hj0))
        (RingHom.ker rd) ≤ z.asIdeal ↔
      Ideal.map (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := O p M H hj0))
        (RingHom.ker rd) ≤
        z.asIdeal.comap (Algebra.TensorProduct.map (AlgHom.id (R p) (IsLocalRing.ResidueField ↥A))
          (σ : O p M H hj0 →ₐ[R p] O p M H hj0)) := fun z => HP5 z
  have hstab := red_ker_stable hj0 τ σ Hpt

  obtain ⟨W₀, hW₀, -, -, -, -⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC p (ΓM M H) hj0
  obtain ⟨hOW, 𝔮, h𝔮, -⟩ :=
    ModularCurve.chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
      (ΓM M H) T_mem_GammaH p (jAt (ΓM M H) hj0) (coe_jAt _ hj0) W₀ hW₀
  have hker : ∀ b : O p M H hj0, b ∈ 𝔮 ↔ rd b = 0 := fun b => mem_iff_red_eq_zero hj0 W₀ hW₀ 𝔮 h𝔮 A hA b
  have h𝔮σ : ∀ b : O p M H hj0, b ∈ 𝔮 → σ b ∈ 𝔮 ∧ σ.symm b ∈ 𝔮 := by
    intro b hb
    have := hstab b ((hker b).mp hb)
    exact ⟨(hker _).mpr this.1, (hker _).mpr this.2⟩

  let xF : ↥(qExpFunctionFieldC ℚ (ΓM M H)) := ⟨x, hx⟩
  let yF : ↥(qExpFunctionFieldC ℚ (ΓM M H)) := ⟨y, hy⟩
  have hxW : xF ∈ W₀ := (hW₀ xF).mpr ⟨a, a', ha', hxa⟩
  obtain ⟨a₁, b₁, hb₁, hxab⟩ :=
    (ModularCurve.mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
      (ΓM M H) T_mem_GammaH p (jAt (ΓM M H) hj0) (coe_jAt _ hj0) W₀ hW₀ 𝔮 h𝔮 xF).mp hxW

  have hb₁' : σ.symm b₁ ∉ 𝔮 := fun h => hb₁ (by simpa using (h𝔮σ _ h).1)
  have hyab : yF * ((σ.symm b₁ : O p M H hj0) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) =
      ((σ.symm a₁ : O p M H hj0) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
    apply Subtype.ext
    apply coeffEmb_injective (AlgebraicClosure ℚ)
    show coeffEmb (AlgebraicClosure ℚ) (y * qexp (σ.symm b₁)) = coeffEmb (AlgebraicClosure ℚ) (qexp (σ.symm a₁))
    rw [map_mul, ← hσ, ← dia_apply_eq_symm d σ hσO b₁, ← dia_apply_eq_symm d σ hσO a₁]

    have hK : (⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hx⟩ :
          ↥(xHFunctionFieldBar M H)) *
        ⟨coeffEmb (AlgebraicClosure ℚ) (qexp b₁),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b₁ : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ =
        ⟨coeffEmb (AlgebraicClosure ℚ) (qexp a₁),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a₁ : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ := by
      apply Subtype.ext
      show coeffEmb (AlgebraicClosure ℚ) x * coeffEmb (AlgebraicClosure ℚ) (qexp b₁) = coeffEmb (AlgebraicClosure ℚ) (qexp a₁)
      rw [← map_mul]
      congr 1
      exact congrArg Subtype.val hxab
    have := congrArg (fun u : ↥(xHFunctionFieldBar M H) => ((diamondAutHBar M H d u : ↥(xHFunctionFieldBar M H)) :
      LaurentSeries (AlgebraicClosure ℚ))) hK
    simp only [map_mul] at this
    push_cast at this
    exact this
  have hyW : yF ∈ W₀ :=
    (ModularCurve.mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
      (ΓM M H) T_mem_GammaH p (jAt (ΓM M H) hj0) (coe_jAt _ hj0) W₀ hW₀ 𝔮 h𝔮 yF).mpr ⟨σ.symm a₁, σ.symm b₁, hb₁', hyab⟩
  exact (hW₀ yF).mp hyW

end
end S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul
end P2MW
export P2MW.S_ModularCurve_exists_mul_ofPowerSeries_eq_of_diamondAutHBar_apply_eq_coeffEmb_of_level_mul (solution)
