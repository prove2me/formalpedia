-- Prove2me | solution 1 for ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cf846ce5-67ec-5151-bbd8-b10059a3d7fc

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFinitePresentation_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_flat_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_sections_of_isAffineOpen
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_one_pullback_snd_toBase_of_charZero
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero
import Theorems.Thm_ModularCurve_isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero
import Theorems.Thm_ModularCurve_exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XHDRLevel_isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_mem_range_or_mem_range_comp_and_range_ne_of_minimalPrimes_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_dense_range_chart_pullback_of_not_isOpen_singleton
import Theorems.Thm_ModularCurve_exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
import Theorems.Thm_ModularCurve_not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
import Theorems.Thm_ModularCurve_geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div
import Theorems.Thm_ModularCurve_XHDRLevel_retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime
import Theorems.Thm_RingHom_isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow
import Theorems.Thm_ModularCurve_coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup
import Theorems.Thm_ModularCurve_XHDRLevel_exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL
import Theorems.Thm_ModularCurve_XHDRLevel_comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner
import Theorems.Thm_ModularCurve_XHDRLevel_comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime
import Theorems.Thm_ModularCurve_XHDRLevel_fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner
import Theorems.Thm_ModularCurve_XHDRLevel_eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id
import Theorems.Thm_AlgebraicGeometry_comp_hom_eq_hom_comp_of_unique_isClosedImmersion_section
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ModularCurve_isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one
import Theorems.Thm_ModularCurve_XHDRLevel_range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
import Theorems.Thm_ModularCurve_exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_hom_comm_and_hom_comp_hom_eq_of_chartPins
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_algEquiv_diamondAutHBar_comm_of_qExpand_of_diamondAutHBar_div
import Theorems.Thm_ModularCurve_diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic_chart
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
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

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic_chart.AlgebraicGeometry AlgebraicCurve NeronModelInfra ModularCurve~nodeEquiv P2MW.S_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic_chart.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic_chart.ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

universe u v

noncomputable section

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem wFrame_at_sigma (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σR : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[R p] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    [Fact (σR (jAt (ΓM M H) hj) ≠ 0)]
    [hFTfin : Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓM M H) hj)]
    [hFTinf : Algebra.FiniteType (R p) ↥(chartAlgInf p (ΓM M H) hj)] :
    Algebra.FiniteType (R p)
        ↥(TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj))) ∧
      Algebra.FiniteType (R p)
        ↥(TwoChartIntegralModel.chartAlgFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj))) ∧
      IsSeparated (TwoChartIntegralModel.toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj))) ∧
      IsSeparated (toBase p (ΓM M H) hj) := by
  set F := ↥(qExpFunctionFieldC ℚ (ΓM M H)) with hF
  set j := jAt (ΓM M H) hj with hjdef

  obtain ⟨t, eFin, eInf, heFin, heInf, ht_over, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq (R p) F F j (σR j) σR rfl
  obtain ⟨t', eFin', eInf', heFin', heInf', ht'_over, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq (R p) F F (σR j) j σR.symm (σR.symm_apply_apply j)

  have hInfσ : Algebra.FiniteType (R p) ↥(TwoChartIntegralModel.chartAlgInf (R p) F (σR j)) := by
    refine hFTinf.of_surjective eInf (fun y => ⟨eInf' y, Subtype.ext ?_⟩)
    rw [heInf, heInf', AlgEquiv.apply_symm_apply]
  have hFinσ : Algebra.FiniteType (R p) ↥(TwoChartIntegralModel.chartAlgFin (R p) F (σR j)) := by
    refine hFTfin.of_surjective eFin (fun y => ⟨eFin' y, Subtype.ext ?_⟩)
    rw [heFin, heFin', AlgEquiv.apply_symm_apply]

  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsNoetherianRing (R p) := inferInstance
  haveI : IsProper (toBase p (ΓM M H) hj) := AlgebraicCurve.TwoChartIntegralModel.isProper_toBase (R p) F j
  have hSep : IsSeparated (toBase p (ΓM M H) hj) := inferInstance
  have hSepσ : IsSeparated (TwoChartIntegralModel.toBase (R p) F (σR j)) := by
    have e : TwoChartIntegralModel.toBase (R p) F (σR j) = t.inv ≫ TwoChartIntegralModel.toBase (R p) F j := by
      rw [← ht_over, Iso.inv_hom_id_assoc]
    have hSep' : IsSeparated (TwoChartIntegralModel.toBase (R p) F j) := hSep
    rw [e]; infer_instance
  exact ⟨hInfσ, hFinσ, hSepσ, hSep⟩

namespace Ws19Glue

theorem exists_gamma0_apply_eq {M : ℕ} [NeZero M] (d : (ZMod M)ˣ) :
    ∃ γ : CongruenceSubgroup.Gamma0 M, (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  set a : ℤ := ((d : ZMod M).val : ℤ) with ha
  have hcop : Nat.Coprime (d : ZMod M).val M := ZMod.val_coe_unit_coprime d
  have hg : Int.gcd a (M : ℤ) = 1 := by rw [ha, Int.gcd_natCast_natCast]; exact hcop
  have hbez : a * Int.gcdA a M + (M : ℤ) * Int.gcdB a M = 1 := by
    have h := Int.gcd_eq_gcd_ab a M
    rw [hg] at h
    push_cast at h
    linarith
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![a, -Int.gcdB a M; (M : ℤ), Int.gcdA a M]
  have hdet : A.det = 1 := by
    rw [Matrix.det_fin_two_of]
    linarith
  refine ⟨⟨⟨A, hdet⟩, ?_⟩, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    show (((M : ℤ) : ℤ) : ZMod M) = 0
    simp
  · show ((a : ℤ) : ZMod M) = d
    rw [ha, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem gamma0_diag {M : ℕ} (γ : CongruenceSubgroup.Gamma0 M) :
    (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) * (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))
  rw [Matrix.det_fin_two] at hdet
  have h10 : (((γ : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := CongruenceSubgroup.Gamma0_mem.mp γ.2
  have := congrArg (Int.cast : ℤ → ZMod M) hdet
  push_cast at this
  rw [h10, mul_zero, sub_zero] at this
  exact this

theorem mul_inv_mem_Gamma1 {M : ℕ} (γ γ' : CongruenceSubgroup.Gamma0 M)
    (h : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (((γ' : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)) :
    ((γ * γ'⁻¹ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma1 M := by
  have hd := gamma0_diag γ
  have hd' := gamma0_diag γ'
  have h10 : (((γ : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := CongruenceSubgroup.Gamma0_mem.mp γ.2
  have h10' : (((γ' : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := CongruenceSubgroup.Gamma0_mem.mp γ'.2
  have hmul : ((γ * γ'⁻¹ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) = (γ : SL(2, ℤ)) * (γ' : SL(2, ℤ))⁻¹ := rfl
  rw [CongruenceSubgroup.Gamma1_mem, hmul]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  rw [h10, h10']
  refine ⟨?_, ?_, by ring⟩
  · rw [h]; linear_combination hd'
  · rw [← h]; linear_combination hd

theorem Gamma1_le_GammaH' {M : ℕ} (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  have hA' := hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA'
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact hA'.2.2
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hA'.2.1
  rw [h1]
  exact one_mem H

def toRingAutHom {G : Type*} [Group G] {F : Type*} [Field F] {_inst : Algebra ℚ F} (ρ : G →* (F ≃ₐ[ℚ] F)) : G →* RingAut F :=
  MonoidHom.mk' (fun g => (ρ g).toRingEquiv) (fun a b => by show (ρ (a * b)).toRingEquiv = _; rw [map_mul]; rfl)

theorem toRingAutHom_apply {G : Type*} [Group G] {F : Type*} [Field F] {_inst : Algebra ℚ F} (ρ : G →* (F ≃ₐ[ℚ] F)) (g : G) (x : F) :
    toRingAutHom ρ g x = ρ g x := rfl

theorem toRingAutHom_eq_one {G : Type*} [Group G] {F : Type*} [Field F] {_inst : Algebra ℚ F} (ρ : G →* (F ≃ₐ[ℚ] F)) (g : G)
    (h : ρ g = 1) : toRingAutHom ρ g = 1 := by
  show (ρ g).toRingEquiv = 1
  rw [h]
  rfl
end Ws19Glue

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.sectionFibre XHDRLevel.fibreMap XHDRLevel.overOfIso XHDRModelAtP ssPlacesQExp infSubgroup neZero_div translation_mem_GammaH Gamma1_le_GammaH xHFunctionField xHFunctionFieldBar qExpFunctionFieldC qExpFunctionFieldC_mono qExpand qExpand_C jNumQ constantCoeff_jNumQ jq coeffMap coeffMap_coeff coeffMap_id coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qExpFrobeniusModL qExpFrobeniusPlaceModL QExpFrobeniusInputsModL jqModC jqModC_rat coeffMap_qExpand diamondAutHBar finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd transcendental_of_coe_eq_coeffEmb_jq exists_algEquiv_laurentBaseChange_cover exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar GammaH_le_GammaH_div_infSubgroup finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand qExpand_mem_xHFunctionField_of_mem_div XHDRLevel.retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL XHDRLevel.comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner XHDRLevel.comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime XHDRLevel.fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner XHDRLevel.eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero XHDRLevel.exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH XHDRLevel.range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one XHDRLevel.range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply algEquiv_diamondAutHBar_comm_of_qExpand_of_diamondAutHBar_div diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X toBase chartAlgFin chartAlgInf ιFin ιInf fibre sectionFibre fibreMap overOfIso ΓN ΓM isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id"
p2m_open "ModularCurve.XHDRLevel ModularCurve~nodeEquiv"

theorem inv_jqModC_eq : (jqModC ℚ)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ.invOfUnit 1) := by
  have hu : jNumQ * jNumQ.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNumQ]; rfl)
  have hj : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
  apply inv_eq_of_mul_eq_one_right
  rw [hj, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
    ← map_mul, hu, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
  rfl

theorem coeff_inv_jqModC_eq_zero_of_nonpos (n : ℤ) (hn : n ≤ 0) : ((jqModC ℚ)⁻¹).coeff n = 0 := by
  rw [inv_jqModC_eq]
  show ((PowerSeries.X * jNumQ.invOfUnit 1 : PowerSeries ℚ) : LaurentSeries ℚ).coeff n = 0
  rw [PowerSeries.coeff_coe]
  split_ifs with h
  · rfl
  · have h0 : n = 0 := le_antisymm hn (not_lt.mp h)
    subst h0
    simp

end ModularCurve.XHDRLevel

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem htheta_bc (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hσq : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
        (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
        (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
          ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθσ : ∀ y : ↥(xHFunctionField M H),
      ((θ ⟨coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩ :
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField M H))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((σ.toRingEquiv y : ↥(xHFunctionField M H)) : LaurentSeries ℚ)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
      ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro f u hfu

  have hle : ∀ x : LaurentSeries ℚ, x ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) → x ∈ xHFunctionField M H :=
    fun x hx => qExpFunctionFieldC_mono ℚ (ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM) hx
  have hleB : ∀ x : LaurentSeries (AlgebraicClosure ℚ),
      x ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) → x ∈ xHFunctionFieldBar M H := by
    intro x hx
    refine IntermediateField.adjoin.mono (AlgebraicClosure ℚ) _ _ ?_ hx
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hle y hy, rfl⟩

  have hf : f = ⟨(u : LaurentSeries (AlgebraicClosure ℚ)), hleB _ u.2⟩ := Subtype.ext hfu
  subst hf

  clear hfu
  obtain ⟨x, hx⟩ := u
  show ((θ ⟨x, hleB x hx⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx

      have h1 := hθσ ⟨y, hle y hy⟩
      have h2 : ((σ ⟨y, hle y hy⟩ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p y :=
        hσq ⟨y, hle y hy⟩ ⟨y, hy⟩ rfl
      refine h1.trans ?_
      show coeffEmb (AlgebraicClosure ℚ) ((σ ⟨y, hle y hy⟩ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = _
      rw [h2]
      exact ModularCurve.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) p y
  | algebraMap c =>

      have h1 : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c, hleB _ (IntermediateField.algebraMap_mem _ c)⟩ :
          ↥(xHFunctionFieldBar M H)) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c := Subtype.ext rfl
      rw [h1, AlgEquiv.commutes]
      show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c = qExpand (AlgebraicClosure ℚ) p (algebraMap _ _ c)
      have hC : (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) c = HahnSeries.C c := by
        show HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (algebraMap (AlgebraicClosure ℚ) (PowerSeries (AlgebraicClosure ℚ)) c) = _
        rw [← PowerSeries.C_eq_algebraMap]; exact HahnSeries.ofPowerSeries_C c
      rw [hC, qExpand_C]
  | add x y hx hy ihx ihy =>
      have h1 : (⟨x + y, hleB _ (add_mem hx hy)⟩ : ↥(xHFunctionFieldBar M H)) = ⟨x, hleB _ hx⟩ + ⟨y, hleB _ hy⟩ := rfl
      rw [h1, map_add]
      show ((θ ⟨x, hleB x hx⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) + (θ ⟨y, hleB y hy⟩ : ↥(xHFunctionFieldBar M H)) = _
      rw [ihx, ihy, map_add]
  | inv x hx ihx =>
      have h1 : (⟨x⁻¹, hleB _ (inv_mem hx)⟩ : ↥(xHFunctionFieldBar M H)) = (⟨x, hleB _ hx⟩)⁻¹ := rfl
      rw [h1, map_inv₀]
      show ((θ ⟨x, hleB x hx⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ = _
      rw [ihx, map_inv₀]
  | mul x y hx hy ihx ihy =>
      have h1 : (⟨x * y, hleB _ (mul_mem hx hy)⟩ : ↥(xHFunctionFieldBar M H)) = ⟨x, hleB _ hx⟩ * ⟨y, hleB _ hy⟩ := rfl
      rw [h1, map_mul]
      show ((θ ⟨x, hleB x hx⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * (θ ⟨y, hleB y hy⟩ : ↥(xHFunctionFieldBar M H)) = _
      rw [ihx, ihy, map_mul]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem htheta_bc2 (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hσdia : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
        ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
          (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ) →
            coeffEmb (AlgebraicClosure ℚ)
                ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
              ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c
                  ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                  ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
                LaurentSeries (AlgebraicClosure ℚ)))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθσ : ∀ y : ↥(xHFunctionField M H),
      ((θ ⟨coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩ :
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField M H))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((σ.toRingEquiv y : ↥(xHFunctionField M H)) : LaurentSeries ℚ)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
            LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro c hc f u hfu

  have hrat : ∀ y : LaurentSeries ℚ, y ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) → qExpand ℚ p y ∈ xHFunctionField M H :=
    fun y hy => ModularCurve.qExpand_mem_xHFunctionField_of_mem_div p M H hpM hy
  have hCq : ∀ a : AlgebraicClosure ℚ,
      qExpand (AlgebraicClosure ℚ) p (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a := by
    intro a
    have hC : (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) a = HahnSeries.C a := by
      show HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (algebraMap (AlgebraicClosure ℚ) (PowerSeries (AlgebraicClosure ℚ)) a) = _
      rw [← PowerSeries.C_eq_algebraMap]; exact HahnSeries.ofPowerSeries_C a
    rw [hC, qExpand_C]
  have hβ : ∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) →
      qExpand (AlgebraicClosure ℚ) p x ∈ xHFunctionFieldBar M H := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        have e : qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) y) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p y) :=
          (ModularCurve.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) p y).symm
        rw [e]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hrat y hy)
    | algebraMap a => rw [hCq]; exact IntermediateField.algebraMap_mem _ a
    | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
    | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx
    | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy

  have hf : f = ⟨qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)), hβ _ u.2⟩ := Subtype.ext hfu
  subst hf
  clear hfu
  obtain ⟨x, hx⟩ := u
  show ((θ ⟨qExpand (AlgebraicClosure ℚ) p x, hβ x hx⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
    ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c ⟨x, hx⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
      LaurentSeries (AlgebraicClosure ℚ))
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx

      have hmem : qExpand ℚ p y ∈ xHFunctionField M H := hrat y hy
      have e1 : (⟨qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) y), hβ _ (IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩)⟩ :
            ↥(xHFunctionFieldBar M H)) =
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p y), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ :=
        Subtype.ext (ModularCurve.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) p y).symm
      rw [e1]
      have h1 := hθσ ⟨qExpand ℚ p y, hmem⟩
      have h2 := hσdia c hc ⟨qExpand ℚ p y, hmem⟩ ⟨y, hy⟩ rfl
      exact h1.trans h2
  | algebraMap a =>
      have e1 : (⟨qExpand (AlgebraicClosure ℚ) p (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a),
            hβ _ (IntermediateField.algebraMap_mem _ a)⟩ : ↥(xHFunctionFieldBar M H)) =
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a := Subtype.ext (hCq a)
      have e2 : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a, IntermediateField.algebraMap_mem _ a⟩ :
            ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) a := Subtype.ext rfl
      rw [e1, e2, AlgEquiv.commutes, AlgEquiv.commutes]
      rfl
  | add x y hx hy ihx ihy =>
      have e1 : (⟨qExpand (AlgebraicClosure ℚ) p (x + y), hβ _ (add_mem hx hy)⟩ : ↥(xHFunctionFieldBar M H)) =
          ⟨qExpand (AlgebraicClosure ℚ) p x, hβ _ hx⟩ + ⟨qExpand (AlgebraicClosure ℚ) p y, hβ _ hy⟩ := Subtype.ext (map_add _ _ _)
      have e2 : (⟨x + y, add_mem hx hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e1, e2, map_add, map_add]
      show ((θ ⟨_, hβ x hx⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) + (θ ⟨_, hβ y hy⟩ : ↥(xHFunctionFieldBar M H)) =
        ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c ⟨x, hx⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) +
          (diamondAutHBar (M / p) (infSubgroup p M H hpM) c ⟨y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
      rw [ihx, ihy]
  | inv x hx ihx =>
      have e1 : (⟨qExpand (AlgebraicClosure ℚ) p x⁻¹, hβ _ (inv_mem hx)⟩ : ↥(xHFunctionFieldBar M H)) =
          (⟨qExpand (AlgebraicClosure ℚ) p x, hβ _ hx⟩)⁻¹ := Subtype.ext (map_inv₀ _ _)
      have e2 : (⟨x⁻¹, inv_mem hx⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = (⟨x, hx⟩)⁻¹ := rfl
      rw [e1, e2, map_inv₀, map_inv₀]
      show ((θ ⟨_, hβ x hx⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ =
        ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c ⟨x, hx⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ))⁻¹
      rw [ihx]
  | mul x y hx hy ihx ihy =>
      have e1 : (⟨qExpand (AlgebraicClosure ℚ) p (x * y), hβ _ (mul_mem hx hy)⟩ : ↥(xHFunctionFieldBar M H)) =
          ⟨qExpand (AlgebraicClosure ℚ) p x, hβ _ hx⟩ * ⟨qExpand (AlgebraicClosure ℚ) p y, hβ _ hy⟩ := Subtype.ext (map_mul _ _ _)
      have e2 : (⟨x * y, mul_mem hx hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e1, e2, map_mul, map_mul]
      show ((θ ⟨_, hβ x hx⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * (θ ⟨_, hβ y hy⟩ : ↥(xHFunctionFieldBar M H)) =
        ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c ⟨x, hx⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) *
          (diamondAutHBar (M / p) (infSubgroup p M H hpM) c ⟨y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
      rw [ihx, ihy]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem wInt_at_sigma (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σR : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[R p] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    [Fact (σR (jAt (ΓM M H) hj) ≠ 0)]
    [hST : @IsScalarTower (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) Algebra.toSMul
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))).toSMul Algebra.toSMul]
    (hσj : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((σR (jAt (ΓM M H) hj) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ)) :
    σR (jAt (ΓM M H) hj) ∈ chartAlgFin p (ΓM M H) hj ∧
    jAt (ΓM M H) hj ∈ TwoChartIntegralModel.chartAlgFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj)) ∧
    (∀ y ∈ TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj)),
      ∃ s ∈ chartAlgInf p (ΓM M H) hj, (∃ a ∈ chartAlgInf p (ΓM M H) hj, s = 1 + (jAt (ΓM M H) hj)⁻¹ * a) ∧
        s * y ∈ chartAlgInf p (ΓM M H) hj) ∧
    (∀ y ∈ chartAlgInf p (ΓM M H) hj,
      ∃ s ∈ TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj)),
        (∃ a ∈ TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj)),
          s = 1 + (σR (jAt (ΓM M H) hj))⁻¹ * a) ∧
        s * y ∈ TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have hce : ∀ x : LaurentSeries ℚ, coeffEmb ℚ x = x := fun x => coeffMap_id x
  have h1 : ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = coeffEmb ℚ jq := by
    rw [hce, coe_jAt]; rfl
  have h2 : ((σR (jAt (ΓM M H) hj) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = coeffEmb ℚ (qExpand ℚ p jq) := by
    rw [hce, hσj]; rfl
  refine @ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand p _ ℚ _ _
    (qExpFunctionFieldC ℚ (ΓM M H)) (R p) _ _ _ _ _ hST
    (jAt (ΓM M H) hj) h1 _ (σR (jAt (ΓM M H) hj)) h2 _

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift Surjective Spec.map_comp_assoc SmoothOfRelativeDimension IsProper morphismRestrict_ι Scheme.Hom GeometricallyIntegral Scheme.Pullback.range_fst Spec IsIntegral Scheme.Opens.toScheme Spec.map Scheme Smooth pullbackSpecIso IsOpenImmersion Flat isIntegral_of_isOpenImmersion IsClosedImmersion IsReduced IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Spec.map_id Scheme.Opens Scheme.Hom.id_base LocallyOfFinitePresentation isReduced_of_isOpenImmersion isPullback_SpecMap_of_isPushout IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.ΓSpecIso exists_smooth_maximal_and_image_eq_of_iso_over smoothOfRelativeDimension_of_irreducibleSpace exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd comp_hom_eq_hom_comp_of_unique_isClosedImmersion_section IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_ι_comp_of_smooth_of_isIntegral
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral X]
    (U₀ : X.Opens) (hU₀ : (U₀ : Set X).Nonempty) [SmoothOfRelativeDimension 1 (U₀.ι ≫ f)]
    (V : X.Opens) [Smooth (V.ι ≫ f)] : SmoothOfRelativeDimension 1 (V.ι ≫ f) := by
  by_cases hV : (V : Set X).Nonempty
  · haveI : Nonempty (V : Scheme.{u}) := by
      obtain ⟨x, hx⟩ := hV; exact ⟨⟨x, hx⟩⟩
    haveI : IsIntegral (V : Scheme.{u}) := isIntegral_of_isOpenImmersion V.ι

    have hW : ((V.ι ⁻¹ᵁ U₀ : (V : Scheme.{u}).Opens) : Set (V : Scheme.{u})).Nonempty := by
      obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U₀.2 V.2 hU₀ hV
      exact ⟨⟨x, hxV⟩, hxU⟩

    haveI : SmoothOfRelativeDimension 1 ((V.ι ⁻¹ᵁ U₀).ι ≫ V.ι ≫ f) := by
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      have : SmoothOfRelativeDimension (0 + 1) (V.ι ∣_ U₀ ≫ U₀.ι ≫ f) := inferInstance
      simpa using this
    exact smoothOfRelativeDimension_of_irreducibleSpace 1 (V.ι ≫ f) (V.ι ⁻¹ᵁ U₀) hW
  ·
    have hE : ∀ x : (V : Scheme.{u}), False := fun x => hV ⟨x.1, x.2⟩
    exact ⟨fun x => (hE x).elim⟩

p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_ι_comp_of_smooth_of_smoothOfRelativeDimension_pullback_snd
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsIntegral X]
    [Flat f] [LocallyOfFinitePresentation f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd f x)] [Nonempty ↥(pullback f x)]
    (V : X.Opens) [Smooth (V.ι ≫ f)] : SmoothOfRelativeDimension 1 (V.ι ≫ f) := by
  obtain ⟨z⟩ := (inferInstance : Nonempty ↥(pullback f x))
  obtain ⟨W, hzW, hW⟩ :=
    AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd f x inferInstance
      ((pullback.fst f x).base z) ⟨z, rfl⟩
  haveI := hW
  exact AlgebraicGeometry.smoothOfRelativeDimension_one_ι_comp_of_smooth_of_isIntegral f W ⟨_, hzW⟩ V

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.sectionFibre XHDRLevel.fibreMap XHDRLevel.overOfIso XHDRModelAtP ssPlacesQExp infSubgroup neZero_div translation_mem_GammaH Gamma1_le_GammaH xHFunctionField xHFunctionFieldBar qExpFunctionFieldC qExpFunctionFieldC_mono qExpand qExpand_C jNumQ constantCoeff_jNumQ jq coeffMap coeffMap_coeff coeffMap_id coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qExpFrobeniusModL qExpFrobeniusPlaceModL QExpFrobeniusInputsModL jqModC jqModC_rat coeffMap_qExpand diamondAutHBar finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd transcendental_of_coe_eq_coeffEmb_jq exists_algEquiv_laurentBaseChange_cover exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar GammaH_le_GammaH_div_infSubgroup finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand qExpand_mem_xHFunctionField_of_mem_div XHDRLevel.retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL XHDRLevel.comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner XHDRLevel.comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime XHDRLevel.fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner XHDRLevel.eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero XHDRLevel.exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH XHDRLevel.range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one XHDRLevel.range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply algEquiv_diamondAutHBar_comm_of_qExpand_of_diamondAutHBar_div diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X toBase chartAlgFin chartAlgInf ιFin ιInf fibre sectionFibre fibreMap overOfIso ΓN ΓM isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id"
namespace CompInstances
p2m_open "ModularCurve.XHDRLevel ModularCurve~nodeEquiv"

theorem nontrivial_tensorProduct_of_mem_range
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (κ : Type u) [CommRing κ] [Algebra R κ]
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))
    (hx : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base x ∈ Set.range ι.base) :
    Nontrivial (κ ⊗[R] A) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, hι]; exact sq.w.symm
  set c := pullback.lift _ _ hcompat with hc
  have hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) := pullback.lift_snd _ _ _
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ι ≫ f) := by
    rw [hcsnd, hι]; exact sq
  have H : IsPullback c
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (pullback.fst _ _) ι :=
    IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip
  have hx' : x ∈ Set.range (pullback.fst (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) ι).base := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨t, -⟩ := hx'
  haveI : Nonempty (PrimeSpectrum (κ ⊗[R] A)) := ⟨(H.isoPullback.inv.base t : _)⟩
  exact PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem isIntegral_fibre_gammaN [NeZero (M / p)] (hpN : ¬ p ∣ M / p)
    (κ : Type) [Field κ] [CharP κ p] (toκ : R p →+* κ) :
    IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) toκ) := by
  letI : Algebra (R p) κ := toκ.toAlgebra
  exact ModularCurve.isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP (M / p) (ΓN p M H hpM)
    (Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM)) (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM))
    p hpN (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj) κ

theorem nontrivial_tensor_chartAlgFin_gammaN
    (κ : Type) [Field κ] (toκ : R p →+* κ)
    {C : Scheme.{0}} (efib : C ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) toκ)
    (hne : Nonempty (Scheme.Opens.toScheme ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)))) :
    letI : Algebra (R p) κ := toκ.toAlgebra
    Nontrivial (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := by
  letI : Algebra (R p) κ := toκ.toAlgebra
  obtain ⟨⟨y, hy⟩⟩ := hne
  obtain ⟨z, -, hz⟩ := hy
  refine nontrivial_tensorProduct_of_mem_range (toBase p (ΓN p M H hpM) hj) ↥(chartAlgFin p (ΓN p M H hpM) hj)
    (ιFin p (ΓN p M H hpM) hj) (TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))
    κ (efib.base y) ⟨z, ?_⟩
  rw [← Scheme.Hom.comp_apply]; exact hz

end ModularCurve.XHDRLevel.CompInstances

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.sectionFibre XHDRLevel.fibreMap XHDRLevel.overOfIso XHDRModelAtP ssPlacesQExp infSubgroup neZero_div translation_mem_GammaH Gamma1_le_GammaH xHFunctionField xHFunctionFieldBar qExpFunctionFieldC qExpFunctionFieldC_mono qExpand qExpand_C jNumQ constantCoeff_jNumQ jq coeffMap coeffMap_coeff coeffMap_id coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qExpFrobeniusModL qExpFrobeniusPlaceModL QExpFrobeniusInputsModL jqModC jqModC_rat coeffMap_qExpand diamondAutHBar finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd transcendental_of_coe_eq_coeffEmb_jq exists_algEquiv_laurentBaseChange_cover exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar GammaH_le_GammaH_div_infSubgroup finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand qExpand_mem_xHFunctionField_of_mem_div XHDRLevel.retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL XHDRLevel.comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner XHDRLevel.comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime XHDRLevel.fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner XHDRLevel.eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero XHDRLevel.exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH XHDRLevel.range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one XHDRLevel.range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply algEquiv_diamondAutHBar_comm_of_qExpand_of_diamondAutHBar_div diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X toBase chartAlgFin chartAlgInf ιFin ιInf fibre sectionFibre fibreMap overOfIso ΓN ΓM isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id"
namespace CompPairDock
p2m_open "ModularCurve.XHDRLevel ModularCurve~nodeEquiv"

theorem exists_chart
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X)
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (κ : Type u) [CommRing κ] [Algebra R κ] :
    ∃ c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      c ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom) ≫ ι ∧
      c ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, hι]
    exact sq.w.symm
  exact ⟨pullback.lift _ _ hcompat, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end ModularCurve.XHDRLevel.CompPairDock

namespace ModularCurve p2m_export "ModularCurve" "XHDRLevel.sectionFibre XHDRLevel.fibreMap XHDRLevel.overOfIso XHDRModelAtP ssPlacesQExp infSubgroup neZero_div translation_mem_GammaH Gamma1_le_GammaH xHFunctionField xHFunctionFieldBar qExpFunctionFieldC qExpFunctionFieldC_mono qExpand qExpand_C jNumQ constantCoeff_jNumQ jq coeffMap coeffMap_coeff coeffMap_id coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qExpFrobeniusModL qExpFrobeniusPlaceModL QExpFrobeniusInputsModL jqModC jqModC_rat coeffMap_qExpand diamondAutHBar finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd transcendental_of_coe_eq_coeffEmb_jq exists_algEquiv_laurentBaseChange_cover exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar GammaH_le_GammaH_div_infSubgroup finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand qExpand_mem_xHFunctionField_of_mem_div XHDRLevel.retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL XHDRLevel.comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner XHDRLevel.comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime XHDRLevel.fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner XHDRLevel.eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero XHDRLevel.exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH XHDRLevel.range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one XHDRLevel.range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply algEquiv_diamondAutHBar_comm_of_qExpand_of_diamondAutHBar_div diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one" namespace XHDRLevel p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X toBase chartAlgFin chartAlgInf ιFin ιInf fibre sectionFibre fibreMap overOfIso ΓN ΓM isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id" end ModularCurve.XHDRLevel
p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in
set_option maxHeartbeats 12800000 in
open ModularCurve.XHDRLevel.CompPairDock in

theorem ModularCurve.XHDRLevel.exists_comp_pair_fibre_of_retraction_of_minimalPrimes_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    [IsProper (toBase p (ΓM M H) hj)] [IsProper (toBase p (ΓN p M H hpM) hj)]
    [Algebra.FiniteType (R p) ↥(chartAlgInf p (ΓM M H) hj)]

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)

    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (w_over : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)

    (κ : Type) [Field κ] [Algebra (R p) κ]
    [IsIntegral (fibre (Γ := (ΓN p M H hpM)) (hj := hj) (algebraMap (R p) κ))]
    [SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))))]
    [Nontrivial (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))]
    (hniso : ∀ x : ↥(fibre (Γ := (ΓM M H)) (hj := hj) (algebraMap (R p) κ)), ¬ IsOpen ({x} : Set ↥(fibre (Γ := (ΓM M H)) (hj := hj) (algebraMap (R p) κ))))

    (σ₀ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (hσ₀ : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z)
    (hmin : minimalPrimes (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) =
      {RingHom.ker σ₀.toRingHom,
       Ideal.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) (theta : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))).toRingHom (RingHom.ker σ₀.toRingHom)})
    (hne : RingHom.ker σ₀.toRingHom ≠
      Ideal.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) (theta : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))).toRingHom (RingHom.ker σ₀.toRingHom)) :
    ∃ comp : Fin 2 → (fibre (Γ := (ΓN p M H hpM)) (hj := hj) (algebraMap (R p) κ) ⟶ fibre (Γ := (ΓM M H)) (hj := hj) (algebraMap (R p) κ)),
      (∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _) ∧
      (∀ i, IsClosedImmersion (comp i)) ∧
      (∀ y : ↥(fibre (Γ := (ΓM M H)) (hj := hj) (algebraMap (R p) κ)), y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base) ∧
      Set.range (comp 0).base ≠ Set.range (comp 1).base ∧
      comp 0 ≫ fibreMap π (algebraMap (R p) κ) = 𝟙 _ ∧
      comp 0 ≫ fibreMap (overOfIso w w_over) (algebraMap (R p) κ) = comp 1 ∧

      (∀ (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶ fibre (Γ := (ΓN p M H hpM)) (hj := hj) (algebraMap (R p) κ))
        (_ : c₀ ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
        (_ : c₀ ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))))
        (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ fibre (Γ := (ΓM M H)) (hj := hj) (algebraMap (R p) κ))
        (_ : c ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj)
        (_ : c ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))))),
        c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c ∧
        ∀ x, (comp 0).base x ∈ Set.range c.base → x ∈ Set.range c₀.base) := by
  classical

  obtain ⟨c₀, hc₀fst, hc₀snd⟩ := exists_chart (toBase p (ΓN p M H hpM) hj) ↥(chartAlgFin p (ΓN p M H hpM) hj) (ιFin p (ΓN p M H hpM) hj)
    (TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) κ
  obtain ⟨c, hcfst, hcsnd⟩ := exists_chart (toBase p (ΓM M H) hj) ↥(chartAlgFin p (ΓM M H) hj) (ιFin p (ΓM M H) hj)
    (TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) κ

  have hπfst : fibreMap π (algebraMap (R p) κ) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π.1 := by
    unfold XHDRLevel.fibreMap; rw [pullback.lift_fst]
  have hπsnd : fibreMap π (algebraMap (R p) κ) ≫ pullback.snd _ _ = pullback.snd _ _ := by
    unfold XHDRLevel.fibreMap; rw [pullback.lift_snd, Category.comp_id]
  have hwfst : fibreMap (overOfIso w w_over) (algebraMap (R p) κ) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ w.hom := by
    unfold XHDRLevel.fibreMap; rw [pullback.lift_fst]; rfl
  have hwsnd : fibreMap (overOfIso w w_over) (algebraMap (R p) κ) ≫ pullback.snd _ _ = pullback.snd _ _ := by
    unfold XHDRLevel.fibreMap; rw [pullback.lift_snd, Category.comp_id]

  obtain ⟨comp₀, hover, hci, hsec, hchart, hmatch⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_isClosedImmersion_comp_eq_id_of_retraction (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)
      π.1 π.2 iota0 pi_chart κ (fibreMap π (algebraMap (R p) κ)) hπfst hπsnd c₀ hc₀fst hc₀snd c hcfst hcsnd σ₀ hσ₀

  have hdense := AlgebraicCurve.TwoChartIntegralModel.dense_range_chart_pullback_of_not_isOpen_singleton (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
    κ c hcfst hcsnd hniso

  have hsurj : Function.Surjective σ₀ := fun z => ⟨_, hσ₀ z⟩
  obtain ⟨hcover, hneq⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.forall_mem_range_or_mem_range_comp_and_range_ne_of_minimalPrimes_eq (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)
      w w_over theta hwchart κ (fibreMap (overOfIso w w_over) (algebraMap (R p) κ)) hwfst hwsnd
      c₀ hc₀fst hc₀snd c hcfst hcsnd σ₀ hsurj hmin hne comp₀ hover hci hchart hmatch hdense

  refine ⟨![comp₀, comp₀ ≫ fibreMap (overOfIso w w_over) (algebraMap (R p) κ)], ?_, ?_, hcover, hneq, hsec, rfl, ?_⟩
  · intro i
    fin_cases i
    · exact hover
    · change (comp₀ ≫ _) ≫ _ = _
      rw [Category.assoc, hwsnd]; exact hover
  · intro i
    fin_cases i
    · exact hci
    · change IsClosedImmersion (comp₀ ≫ _)
      haveI := hci
      haveI : IsIso (overOfIso w w_over).1 := show IsIso w.hom from inferInstance
      haveI : IsIso (fibreMap (overOfIso w w_over) (algebraMap (R p) κ)) := by
        unfold XHDRLevel.fibreMap; infer_instance
      infer_instance
  ·
    intro c₀' h₁ h₂ c' h₃ h₄
    have e₀ : c₀' = c₀ := pullback.hom_ext (h₁.trans hc₀fst.symm) (h₂.trans hc₀snd.symm)
    have e : c' = c := pullback.hom_ext (h₃.trans hcfst.symm) (h₄.trans hcsnd.symm)
    subst e₀; subst e
    exact ⟨hchart, hmatch⟩

p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem ModularCurve.XHDRLevel.range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (εinf εzero : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    (rhoInf : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] R p)
    (rhoInf_spec : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      ((rhoInf b : R p) : ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ).coeff 0)
    (εinf_chart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ ιInf p (ΓM M H) hj)

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)

    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (iotaInf_spec : ∀ b, (((iotaInf b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chartInf : ιInf p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (w_over : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (w_sections : εinf.1 ≫ w.hom = εzero.1)

    (comp : Fin 2 → (fibre (Γ := (ΓN p M H hpM)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := (ΓM M H)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_jointly_surjective : ∀ y : ↥(fibre (Γ := (ΓM M H)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base)
    (comp_pi : comp 0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _)
    (comp_w : comp 0 ≫ fibreMap (overOfIso w w_over) ((IsLocalRing.residue ↥A).comp ρ) = comp 1) :
    Set.range (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range (comp 0).base ∧
    Set.range (sectionFibre εzero ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range (comp 1).base ∧
    (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)) ≫ comp 0 = sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ) ∧
    (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)) ≫ comp 1 = sectionFibre εzero ((IsLocalRing.residue ↥A).comp ρ) := by

  have hεz : sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap (overOfIso w w_over) ((IsLocalRing.residue ↥A).comp ρ) = sectionFibre εzero ((IsLocalRing.residue ↥A).comp ρ) := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      unfold XHDRLevel.fibreMap XHDRLevel.sectionFibre
      rw [pullback.lift_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc]
      congr 1
    · rw [Category.assoc]
      unfold XHDRLevel.fibreMap XHDRLevel.sectionFibre
      rw [pullback.lift_snd, ← Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]

  haveI := comp_isClosedImmersion 0
  haveI := comp_isClosedImmersion 1
  have h1 : Set.range (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range (comp 0).base :=
    (ModularCurve.XHDRLevel.range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id p M H hpM hpM2 hHp hj
      εinf rhoInf rhoInf_spec εinf_chart π iota0 iota0_spec pi_chart theta htheta iotaInf iotaInf_spec pi_chartInf
      A hA ρ hρ (comp 0) (comp_over 0) comp_pi (comp 1) (comp_over 1) comp_jointly_surjective).2

  obtain ⟨g, hg, -⟩ := AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
    (comp 0) (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ)) h1
  have hg' : g = sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) := by
    have := congrArg (· ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)) hg
    simpa only [Category.assoc, comp_pi, Category.comp_id] using this
  have h3 : (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)) ≫ comp 0 = sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ) := by
    rw [← hg', hg]

  have h4 : (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)) ≫ comp 1 = sectionFibre εzero ((IsLocalRing.residue ↥A).comp ρ) := by
    rw [← comp_w, ← Category.assoc, h3, hεz]

  have h2 : Set.range (sectionFibre εzero ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range (comp 1).base := by
    rw [← h4]
    rintro _ ⟨x, rfl⟩
    exact ⟨(sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)).base x, rfl⟩
  exact ⟨h1, h2, h3, h4⟩

namespace F9R

private lemma isPullback_chart (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (κ : Type) [Field κ] [Algebra (R p) κ]
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p Γ hj))) ⟶
      pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj))).toRingHom) ≫ ιFin p Γ hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj))))) :
    IsPullback c (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj))).toRingHom))
      (pullback.fst _ _) (ιFin p Γ hj) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (R p) κ ↥(chartAlgFin p Γ hj))

  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj))).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))
      (ιFin p Γ hj ≫ toBase p Γ hj) := by
    rw [hcsnd]
    erw [TwoChartIntegralModel.ιFin_toBase]
    exact sq
  exact IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip

private lemma isOpenImmersion_chart (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (κ : Type) [Field κ] [Algebra (R p) κ]
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p Γ hj))) ⟶
      pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj))).toRingHom) ≫ ιFin p Γ hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj))))) :
    IsOpenImmersion c ∧ Set.range c.base = (pullback.fst (toBase p Γ hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))).base ⁻¹' Set.range (ιFin p Γ hj).base := by
  have H := isPullback_chart p Γ hj κ c hcfst hcsnd
  have hc : c = H.isoPullback.hom ≫ pullback.fst _ _ := (H.isoPullback_hom_fst).symm
  refine ⟨by rw [hc]; infer_instance, ?_⟩
  rw [← Scheme.Pullback.range_fst, hc]
  ext x; constructor
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.hom.base y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩

end F9R

namespace F9R

private lemma chart_fibreMap (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (κ : Type) [Field κ] [Algebra (R p) κ]
    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hw : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj)
    (hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))))) :
    c ≫ fibreMap (overOfIso w hw) (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom) ≫ c := by
    apply pullback.hom_ext
    · simp only [Category.assoc, XHDRLevel.fibreMap, XHDRLevel.overOfIso, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [reassoc_of% hcfst, hwchart, hcfst]
      simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
      have hring : (Algebra.TensorProduct.includeRight (R := R p) (A := κ)
            (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom.comp theta.toRingEquiv.toRingHom =
          (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := R p) (A := κ)
              (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom :=
        RingHom.ext fun b => by simp [Algebra.TensorProduct.map_tmul]
      rw [hring]
    · simp only [Category.assoc, XHDRLevel.fibreMap, XHDRLevel.overOfIso, pullback.lift_snd, Category.comp_id]
      try rw [hcsnd]
      try rw [hcsnd]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have hring : (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := κ)
            (B := ↥(chartAlgFin p (ΓM M H) hj))) =
          (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := κ)
              (B := ↥(chartAlgFin p (ΓM M H) hj))) :=
        RingHom.ext fun a => by simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [← hring]

private lemma chart_fibreMap0 (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (κ : Type) [Field κ] [Algebra (R p) κ]
    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hpichart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
    (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶
      fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
    (hc₀snd : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))))
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj)
    (hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))))) :
    c ≫ fibreMap π (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom) ≫ c₀ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, XHDRLevel.fibreMap, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [reassoc_of% hcfst, hpichart, hc₀fst]
      simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
      have hring : (Algebra.TensorProduct.includeRight (R := R p) (A := κ)
            (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom.comp iota0.toRingHom =
          (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := R p) (A := κ)
              (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom :=
        RingHom.ext fun b => by simp [Algebra.TensorProduct.map_tmul]
      rw [hring]
    · simp only [Category.assoc, XHDRLevel.fibreMap, pullback.lift_snd, Category.comp_id]
      try rw [hcsnd]
      try rw [hc₀snd]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have hring : (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := κ)
            (B := ↥(chartAlgFin p (ΓM M H) hj))) =
          (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := κ)
              (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))) :=
        RingHom.ext fun a => by simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [← hring]

end F9R

section F9HelpersSection

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic_chart.AlgebraicGeometry"

namespace F9Helpers

private theorem algebraMap_tensor_surjective
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (hB : Function.Surjective (algebraMap A B)) (hC : Function.Surjective (algebraMap A C)) :
    Function.Surjective (algebraMap A (B ⊗[A] C)) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b c =>
      obtain ⟨a, rfl⟩ := hB b
      obtain ⟨a', rfl⟩ := hC c
      refine ⟨a * a', ?_⟩
      rw [map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply' a',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add u v hu hv =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨a', rfl⟩ := hv
      exact ⟨a + a', map_add _ _ _⟩

private theorem ker_algebraMap_tensor
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (hB : Function.Surjective (algebraMap A B)) (hC : Function.Surjective (algebraMap A C)) :
    RingHom.ker (algebraMap A (B ⊗[A] C)) =
      RingHom.ker (algebraMap A B) ⊔ RingHom.ker (algebraMap A C) := by
  classical
  set K : Ideal A := RingHom.ker (algebraMap A B) ⊔ RingHom.ker (algebraMap A C) with hK
  have hkB : RingHom.ker (Algebra.ofId A B) ≤ K := le_sup_left
  have hkC : RingHom.ker (Algebra.ofId A C) ≤ K := le_sup_right
  let eB : (A ⧸ RingHom.ker (Algebra.ofId A B)) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hB
  let eC : (A ⧸ RingHom.ker (Algebra.ofId A C)) ≃ₐ[A] C :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A C) hC
  let fB : B →ₐ[A] A ⧸ K := (Ideal.Quotient.factorₐ A hkB).comp eB.symm.toAlgHom
  let fC : C →ₐ[A] A ⧸ K := (Ideal.Quotient.factorₐ A hkC).comp eC.symm.toAlgHom
  let ψ : B ⊗[A] C →ₐ[A] A ⧸ K := Algebra.TensorProduct.productMap fB fC
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    have h1 : ψ (algebraMap A (B ⊗[A] C) a) = 0 := by rw [ha, map_zero]
    rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  · apply sup_le
    · intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      rw [Algebra.TensorProduct.algebraMap_apply, ha, TensorProduct.zero_tmul]
    · intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      rw [Algebra.TensorProduct.algebraMap_apply', ha, TensorProduct.tmul_zero]

private noncomputable def quotientKerSupKerEquivTensor
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (hB : Function.Surjective (algebraMap A B)) (hC : Function.Surjective (algebraMap A C)) :
    (A ⧸ (RingHom.ker (algebraMap A B) ⊔ RingHom.ker (algebraMap A C))) ≃ₐ[A] B ⊗[A] C :=
  (Ideal.quotientEquivAlgOfEq A (ker_algebraMap_tensor hB hC).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A (B ⊗[A] C))
      (algebraMap_tensor_surjective hB hC))

private noncomputable def pullbackCompMonoIso {𝒞 : Type*} [Category 𝒞] {X Y W Z : 𝒞}
    (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    pullback (f ≫ i) (g ≫ i) ≅ pullback f g :=
  limit.isoLimitCone ⟨_, pullbackIsPullbackOfCompMono f g i⟩

private theorem nonempty_pullback_iso_Spec_quotient_ker_sup_ker
    {A B : Type u} [CommRing A] [CommRing B]
    (σ₀ σ₁ : A →+* B) (hσ₀ : Function.Surjective σ₀) (hσ₁ : Function.Surjective σ₁)
    {Y : Scheme.{u}} (c : Spec (CommRingCat.of A) ⟶ Y) [Mono c]
    (f₀ f₁ : Spec (CommRingCat.of B) ⟶ Y)
    (h₀ : f₀ = Spec.map (CommRingCat.ofHom σ₀) ≫ c) (h₁ : f₁ = Spec.map (CommRingCat.ofHom σ₁) ≫ c) :
    Nonempty (pullback f₀ f₁ ≅ Spec (CommRingCat.of (A ⧸ (RingHom.ker σ₀ ⊔ RingHom.ker σ₁)))) := by
  classical
  subst h₀ h₁

  let i1 : pullback (Spec.map (CommRingCat.ofHom σ₀) ≫ c) (Spec.map (CommRingCat.ofHom σ₁) ≫ c) ≅
      pullback (Spec.map (CommRingCat.ofHom σ₀)) (Spec.map (CommRingCat.ofHom σ₁)) :=
    pullbackCompMonoIso _ _ c

  let e₀ : (A ⧸ RingHom.ker σ₀) ≃+* B := RingHom.quotientKerEquivOfSurjective hσ₀
  let e₁ : (A ⧸ RingHom.ker σ₁) ≃+* B := RingHom.quotientKerEquivOfSurjective hσ₁
  have fac₀ : Spec.map (CommRingCat.ofHom σ₀) =
      Spec.map e₀.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ RingHom.ker σ₀))) := by
    rw [← Spec.map_comp]
    congr 1
  have fac₁ : Spec.map (CommRingCat.ofHom σ₁) =
      Spec.map e₁.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ RingHom.ker σ₁))) := by
    rw [← Spec.map_comp]
    congr 1
  let i2 : pullback (Spec.map (CommRingCat.ofHom σ₀)) (Spec.map (CommRingCat.ofHom σ₁)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ RingHom.ker σ₀))))
        (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ RingHom.ker σ₁)))) :=
    pullback.congrHom fac₀ fac₁ ≪≫
      asIso (pullback.map _ _ _ _ (Spec.map e₀.toCommRingCatIso.hom) (Spec.map e₁.toCommRingCatIso.hom) (𝟙 _)
        (by rw [Category.comp_id]) (by rw [Category.comp_id]))

  let i3 := pullbackSpecIso A (A ⧸ RingHom.ker σ₀) (A ⧸ RingHom.ker σ₁)

  have hk₀ : RingHom.ker (algebraMap A (A ⧸ RingHom.ker σ₀)) = RingHom.ker σ₀ := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  have hk₁ : RingHom.ker (algebraMap A (A ⧸ RingHom.ker σ₁)) = RingHom.ker σ₁ := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  let e : (A ⧸ (RingHom.ker σ₀ ⊔ RingHom.ker σ₁)) ≃ₐ[A]
      (A ⧸ RingHom.ker σ₀) ⊗[A] (A ⧸ RingHom.ker σ₁) :=
    (Ideal.quotientEquivAlgOfEq A (by rw [hk₀, hk₁])).trans
      (quotientKerSupKerEquivTensor (A := A) (B := A ⧸ RingHom.ker σ₀) (C := A ⧸ RingHom.ker σ₁)
        Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective)
  let i4 : Spec (CommRingCat.of ((A ⧸ RingHom.ker σ₀) ⊗[A] (A ⧸ RingHom.ker σ₁))) ≅
      Spec (CommRingCat.of (A ⧸ (RingHom.ker σ₀ ⊔ RingHom.ker σ₁))) :=
    asIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom)
  exact ⟨i1 ≪≫ i2 ≪≫ i3 ≪≫ i4⟩

end F9Helpers

private theorem F9R.forall_exists_eq_pow_of_forall_tmul_one
    {R κ M A : Type*} [CommRing R] [Field κ] [Algebra R κ] [CommRing M] [Algebra R M]
    [CommRing A] [Algebra κ A] (p : ℕ) [Fact p.Prime] [CharP κ p] [PerfectRing κ p] [CharP A p]
    (f : κ ⊗[R] M →ₐ[κ] A) (hf : ∀ m : M, ∃ c : A, f ((1 : κ) ⊗ₜ[R] m) = c ^ p) :
    ∀ z : κ ⊗[R] M, ∃ c : A, f z = c ^ p := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, zero_pow (Fact.out : p.Prime).ne_zero]⟩
  | tmul x m =>
      obtain ⟨c, hc⟩ := hf m
      refine ⟨algebraMap κ A ((frobeniusEquiv κ p).symm x) * c, ?_⟩
      have hx : x ⊗ₜ[R] m = x • ((1 : κ) ⊗ₜ[R] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hy : ((frobeniusEquiv κ p).symm x) ^ p = x := by
        rw [← frobenius_def]; exact frobenius_apply_frobeniusEquiv_symm κ p x
      rw [hx, map_smul, hc, mul_pow, ← map_pow, hy, Algebra.smul_def]
  | add u v hu hv =>
      obtain ⟨c, hc⟩ := hu
      obtain ⟨d, hd⟩ := hv
      exact ⟨c + d, by rw [map_add, hc, hd, add_pow_char]⟩

end F9HelpersSection

set_option maxHeartbeats 16000000 in
theorem isReduced_pullback_comp_pair
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hw : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hpichart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
    [Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓN p M H hpM) hj)]

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (R p) κ]

    (σ₀ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (hσ₀ : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z)

    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom ((1 : κ) ⊗ₜ[R p] iota0 b)) = ((1 : κ) ⊗ₜ[R p] b) ^ p)

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ)))
    (hcomp_pi : comp 0 ≫ fibreMap π (algebraMap (R p) κ) = 𝟙 _)
    (hcomp_w : comp 0 ≫ fibreMap (overOfIso w hw) (algebraMap (R p) κ) = comp 1)
    (hcomp_chart : ∀ (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶
        fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))
      (_ : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
      (_ : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))))
      (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
      (_ : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj)
      (_ : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))))),
      c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c)

    (hZ : ∀ n : ↥(pullback (comp 0) (comp 1)),
      (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))).base
        ((pullback.fst (comp 0) (comp 1)).base n) ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base) :
    IsReduced (pullback (comp 0) (comp 1)) := by

  have hcompat0 : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj) ≫
        toBase p (ΓN p M H hpM) hj =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)) := by
    rw [Category.assoc, TwoChartIntegralModel.ιFin_toBase, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (algebraMap (R p) κ r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  let c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ) :=
    pullback.lift _ _ hcompat0
  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj) ≫
        toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)) := by
    rw [Category.assoc, TwoChartIntegralModel.ιFin_toBase, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (algebraMap (R p) κ r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  let c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ) :=
    pullback.lift _ _ hcompat

  obtain ⟨hc₀_oi, hc₀_range⟩ := F9R.isOpenImmersion_chart p (ΓN p M H hpM) hj κ c₀ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨hc_oi, hc_range⟩ := F9R.isOpenImmersion_chart p (ΓM M H) hj κ c (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

  have hsq₀ : c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c :=
    hcomp_chart c₀ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) c (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

  have hc₀fst : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj :=
    pullback.lift_fst _ _ _
  have hc₀snd : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))) :=
    pullback.lift_snd _ _ _
  have hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj :=
    pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj)))) :=
    pullback.lift_snd _ _ _

  have hwsq : c ≫ fibreMap (overOfIso w hw) (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom) ≫ c :=
    F9R.chart_fibreMap p M H hpM hj κ w hw theta hwchart c hcfst hcsnd
  have hπsq : c ≫ fibreMap π (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom) ≫ c₀ :=
    F9R.chart_fibreMap0 p M H hpM hj κ π iota0 hpichart c₀ hc₀fst hc₀snd c hcfst hcsnd

  let σ₁ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) :=
    σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)
  have hσ₁ : σ₁.toRingHom = σ₀.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom := rfl
  have hsq₁ : c₀ ≫ comp 1 = Spec.map (CommRingCat.ofHom σ₁.toRingHom) ≫ c := by
    rw [← hcomp_w, reassoc_of% hsq₀, hwsq, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hσ₁]

  have hfst : ∀ n, (pullback.fst (comp 0) (comp 1)).base n ∈ Set.range c₀.base := by
    intro n; rw [hc₀_range]; exact hZ n

  have hw' : w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by rw [Iso.inv_comp_eq, hw]
  have hwchart' : ιFin p (ΓM M H) hj ≫ w.inv =
      Spec.map (CommRingCat.ofHom theta.symm.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj := by
    rw [Iso.comp_inv_eq, Category.assoc, hwchart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have : theta.symm.toRingEquiv.toRingHom.comp theta.toRingEquiv.toRingHom = RingHom.id _ :=
      RingHom.ext fun b => theta.symm_apply_apply b
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hwsq' : c ≫ fibreMap (overOfIso w.symm hw') (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom).toRingHom) ≫ c :=
    F9R.chart_fibreMap p M H hpM hj κ w.symm hw' theta.symm hwchart' c hcfst hcsnd
  have hwinv : fibreMap (overOfIso w hw) (algebraMap (R p) κ) ≫ fibreMap (overOfIso w.symm hw') (algebraMap (R p) κ) = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp [XHDRLevel.fibreMap, XHDRLevel.overOfIso, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]
  have hsnd : ∀ n, (pullback.snd (comp 0) (comp 1)).base n ∈ Set.range c₀.base := by
    intro n

    obtain ⟨y, hy⟩ := hfst n
    have h1 : (fibreMap (overOfIso w hw) (algebraMap (R p) κ)).base ((comp 0).base ((pullback.snd (comp 0) (comp 1)).base n)) ∈
        Set.range c.base := by
      rw [← Scheme.Hom.comp_apply, hcomp_w, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply,
        ← hy, ← Scheme.Hom.comp_apply, hsq₀]
      exact ⟨_, rfl⟩
    have h2 : (comp 0).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ Set.range c.base := by
      obtain ⟨u, hu⟩ := h1
      have hz : (fibreMap (overOfIso w hw) (algebraMap (R p) κ) ≫ fibreMap (overOfIso w.symm hw') (algebraMap (R p) κ)).base
          ((comp 0).base ((pullback.snd (comp 0) (comp 1)).base n)) = (c ≫ fibreMap (overOfIso w.symm hw') (algebraMap (R p) κ)).base u := by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hu]
      rw [hwinv, hwsq', Scheme.Hom.id_base] at hz
      exact ⟨_, hz.symm⟩

    obtain ⟨v, hv⟩ := h2
    have h3 : (pullback.snd (comp 0) (comp 1)).base n =
        (fibreMap π (algebraMap (R p) κ)).base ((comp 0).base ((pullback.snd (comp 0) (comp 1)).base n)) := by
      rw [← Scheme.Hom.comp_apply (comp 0), hcomp_pi, Scheme.Hom.id_base]; rfl
    rw [h3, ← hv, ← Scheme.Hom.comp_apply, hπsq]
    exact ⟨_, rfl⟩

  let e : pullback (c₀ ≫ comp 0) (c₀ ≫ comp 1) ⟶ pullback (comp 0) (comp 1) :=
    pullback.map _ _ _ _ c₀ c₀ (𝟙 _) (by simp) (by simp)
  let l₁ : pullback (comp 0) (comp 1) ⟶ Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) :=
    IsOpenImmersion.lift c₀ (pullback.fst (comp 0) (comp 1)) (by rintro _ ⟨n, rfl⟩; exact hfst n)
  let l₂ : pullback (comp 0) (comp 1) ⟶ Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) :=
    IsOpenImmersion.lift c₀ (pullback.snd (comp 0) (comp 1)) (by rintro _ ⟨n, rfl⟩; exact hsnd n)
  have hl₁ : l₁ ≫ c₀ = pullback.fst (comp 0) (comp 1) := IsOpenImmersion.lift_fac _ _ _
  have hl₂ : l₂ ≫ c₀ = pullback.snd (comp 0) (comp 1) := IsOpenImmersion.lift_fac _ _ _
  let einv : pullback (comp 0) (comp 1) ⟶ pullback (c₀ ≫ comp 0) (c₀ ≫ comp 1) :=
    pullback.lift l₁ l₂ (by rw [reassoc_of% hl₁, reassoc_of% hl₂, pullback.condition])
  have heinv_fst : einv ≫ pullback.fst _ _ = l₁ := pullback.lift_fst _ _ _
  have heinv_snd : einv ≫ pullback.snd _ _ = l₂ := pullback.lift_snd _ _ _
  have he_fst : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ c₀ := pullback.lift_fst _ _ _
  have he_snd : e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c₀ := pullback.lift_snd _ _ _
  have he₁ : e ≫ einv = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [← cancel_mono c₀]
      simp only [Category.assoc, Category.id_comp]
      rw [reassoc_of% heinv_fst, hl₁, he_fst]
    · rw [← cancel_mono c₀]
      simp only [Category.assoc, Category.id_comp]
      rw [reassoc_of% heinv_snd, hl₂, he_snd]
  have he₂ : einv ≫ e = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp]
      rw [he_fst, reassoc_of% heinv_fst, hl₁]
    · simp only [Category.assoc, Category.id_comp]
      rw [he_snd, reassoc_of% heinv_snd, hl₂]
  haveI : IsIso e := ⟨⟨einv, he₁, he₂⟩⟩

  let I : Ideal (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) :=
    RingHom.ker σ₁.toRingHom ⊔ RingHom.ker σ₀.toRingHom

  have hθθ : ∀ y, Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom
      (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [Algebra.TensorProduct.map_tmul]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  have hσ₀surj : Function.Surjective σ₀.toRingHom := fun z => ⟨_, hσ₀ z⟩
  have hσ₁surj : Function.Surjective σ₁.toRingHom := fun z =>
    ⟨Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z), by
      show σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom _) = z
      rw [hθθ, hσ₀]⟩
  obtain ⟨e''⟩ := F9Helpers.nonempty_pullback_iso_Spec_quotient_ker_sup_ker σ₁.toRingHom σ₀.toRingHom hσ₁surj hσ₀surj
    c (c₀ ≫ comp 1) (c₀ ≫ comp 0) hsq₁ hsq₀
  let e' : pullback (c₀ ≫ comp 0) (c₀ ≫ comp 1) ≅
      Spec (CommRingCat.of ((κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ⧸ I)) :=
    pullbackSymmetry _ _ ≪≫ e''

  haveI : Algebra.FiniteType κ (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := inferInstance
  haveI : IsNoetherianRing (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := Algebra.FiniteType.isNoetherianRing κ _
  let ι₀f : κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) → κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) :=
    fun b => Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 b
  let ι₁f : κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) → κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) :=
    fun b => Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom (ι₀f b)
  have h₀' : ∀ b, σ₁.toRingHom (ι₁f b) = b := fun b => by
    show σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom _) = b
    rw [hθθ, hσ₀]
  have h₁' : ∀ b, σ₀.toRingHom (ι₀f b) = b := fun b => hσ₀ b

  have hfrob1 : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      σ₁ ((1 : κ) ⊗ₜ[R p] iota0 b) = ((1 : κ) ⊗ₜ[R p] b) ^ p := fun b => hfrob b
  haveI hred : IsReduced ((κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ⧸ I) := by
    rcases subsingleton_or_nontrivial (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) with hB | hB
    ·
      have h01 : (0 : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) = 1 := by
        have := congrArg (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0)
          (Subsingleton.elim (0 : κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) 1)
        rwa [map_zero, map_one] at this
      haveI : Subsingleton (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) := subsingleton_of_zero_eq_one h01
      haveI : Subsingleton ((κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ⧸ I) :=
        Ideal.Quotient.mk_surjective.subsingleton
      infer_instance
    · haveI : CharP (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) p :=
        charP_of_injective_algebraMap (algebraMap κ _).injective p
      haveI : ExpChar κ p := ExpChar.prime Fact.out
      have hfrob : ∀ b, ∃ c, σ₁.toRingHom (ι₀f b) = c ^ p := by
        refine F9R.forall_exists_eq_pow_of_forall_tmul_one p
          (σ₁.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0)) fun b => ⟨(1 : κ) ⊗ₜ[R p] b, ?_⟩
        all_goals first
          | (show σ₁ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 ((1 : κ) ⊗ₜ[R p] b)) = _
             rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
             exact hfrob1 b)
          | skip
      exact RingHom.isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow σ₁.toRingHom σ₀.toRingHom ι₁f ι₀f h₀' h₁' p (Fact.out : p.Prime).two_le hfrob
  haveI : IsReduced (Spec (CommRingCat.of ((κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ⧸ I))) :=
    inferInstance
  exact isReduced_of_isOpenImmersion (inv e ≫ e'.hom)

theorem isReduced_pullback_comp_pair_place
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hw : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)
    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hpichart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
    [Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (σ₀ : letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
      (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (hσ₀ : letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
      ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) iota0 z) = z)
    (hfrob : letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
      ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
        σ₀ (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] iota0 b)) =
          ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) ^ p)

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hcomp_pi : comp 0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _)
    (hcomp_w : comp 0 ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) = comp 1)
    (hcomp_chart : letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
      ∀ (c₀ : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶
          fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
        (_ : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))))
        (c : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj)
        (_ : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))))),
        c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c)

    (hZ : ∀ n : ↥(pullback (comp 0) (comp 1)),
      (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((pullback.fst (comp 0) (comp 1)).base n) ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base) :
    IsReduced (pullback (comp 0) (comp 1)) := by
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  exact isReduced_pullback_comp_pair p M H hpM hj w hw theta hwchart π iota0 hpichart (IsLocalRing.ResidueField ↥A) σ₀ hσ₀ hfrob comp hcomp_pi hcomp_w
    hcomp_chart hZ

p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem ModularCurve.XHDRLevel.hfrob_place_of_retraction
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (σ₀ : letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
      (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A]
        (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (hσ₀ : letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
      ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) iota0 z) = z) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      σ₀ (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom
          ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] iota0 b)) =
        ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) ^ p := by
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  intro b
  exact ModularCurve.XHDRLevel.retraction_one_tmul_iota0_eq_pow_of_theta_iota0_eq_qExpand_of_liesOverPrime p M H hpM hpM2 hHp hj
    iota0 iota0_spec theta htheta A hA ρ hρ
    ![σ₀, σ₀.comp (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom)]
    hσ₀ (fun z => rfl) b

p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem ModularCurve.XHDRLevel.comp_dia_place
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (w_over : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (δ : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (δ_over : δ.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (δ0 : X p (ΓN p M H hpM) hj ≅ X p (ΓN p M H hpM) hj)
    (δ0_over : δ0.hom ≫ toBase p (ΓN p M H hpM) hj = toBase p (ΓN p M H hpM) hj)
    (hπδ : δ.hom ≫ π.1 = π.1 ≫ δ0.hom) (hwδ : w.hom ≫ δ.hom = δ.hom ≫ w.hom)
    (κ : Type) [Field κ] (toκ : R p →+* κ) [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) toκ)]
    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) toκ ⟶ fibre (Γ := ΓM M H) (hj := hj) toκ))
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_jointly_surjective : ∀ y : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ),
      y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base)
    (comp_pi : comp 0 ≫ fibreMap π toκ = 𝟙 _)
    (comp_w : comp 0 ≫ fibreMap (overOfIso w w_over) toκ = comp 1)
    (hnosec : ∀ β : fibre (Γ := ΓN p M H hpM) (hj := hj) toκ ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) toκ,
      β ≫ comp 1 ≫ fibreMap π toκ ≠ 𝟙 _) :
    ∀ i : Fin 2, comp i ≫ fibreMap (overOfIso δ δ_over) toκ = fibreMap (overOfIso δ0 δ0_over) toκ ≫ comp i := by

  haveI hδ : IsIso (fibreMap (overOfIso δ δ_over) toκ) := by
    haveI : IsIso (overOfIso δ δ_over).1 := show IsIso δ.hom from inferInstance
    unfold XHDRLevel.fibreMap; infer_instance
  haveI hδ0 : IsIso (fibreMap (overOfIso δ0 δ0_over) toκ) := by
    haveI : IsIso (overOfIso δ0 δ0_over).1 := show IsIso δ0.hom from inferInstance
    unfold XHDRLevel.fibreMap; infer_instance
  haveI := comp_isClosedImmersion 0

  have pfst : ∀ {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} (f : SchemeHomOver (toBase p Γ₁ hj) (toBase p Γ₂ hj)),
      fibreMap f toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.1 := by
    intro Γ₁ Γ₂ f; unfold XHDRLevel.fibreMap; rw [pullback.lift_fst]
  have pfst_assoc : ∀ {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} (f : SchemeHomOver (toBase p Γ₁ hj) (toBase p Γ₂ hj))
      {Z : Scheme.{0}} (h : X p Γ₂ hj ⟶ Z),
      fibreMap f toκ ≫ pullback.fst _ _ ≫ h = pullback.fst _ _ ≫ f.1 ≫ h := by
    intro Γ₁ Γ₂ f Z h; rw [← Category.assoc, pfst, Category.assoc]
  have psnd : ∀ {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} (f : SchemeHomOver (toBase p Γ₁ hj) (toBase p Γ₂ hj)),
      fibreMap f toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    intro Γ₁ Γ₂ f; unfold XHDRLevel.fibreMap; rw [pullback.lift_snd, Category.comp_id]

  have hπ' : (asIso (fibreMap (overOfIso δ δ_over) toκ)).hom ≫ fibreMap π toκ =
      fibreMap π toκ ≫ (asIso (fibreMap (overOfIso δ0 δ0_over) toκ)).hom := by
    simp only [asIso_hom]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pfst, pfst_assoc, pfst, pfst_assoc]
      show pullback.fst _ _ ≫ δ.hom ≫ π.1 = pullback.fst _ _ ≫ π.1 ≫ δ0.hom
      rw [hπδ]
    · simp only [Category.assoc, psnd]
  have hw' : fibreMap (overOfIso w w_over) toκ ≫ fibreMap (overOfIso δ δ_over) toκ =
      fibreMap (overOfIso δ δ_over) toκ ≫ fibreMap (overOfIso w w_over) toκ := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pfst, pfst_assoc, pfst, pfst_assoc]
      show pullback.fst _ _ ≫ w.hom ≫ δ.hom = pullback.fst _ _ ≫ δ.hom ≫ w.hom
      rw [hwδ]
    · simp only [Category.assoc, psnd]

  have h0 : comp 0 ≫ fibreMap (overOfIso δ δ_over) toκ = fibreMap (overOfIso δ0 δ0_over) toκ ≫ comp 0 :=
    AlgebraicGeometry.comp_hom_eq_hom_comp_of_unique_isClosedImmersion_section (fibreMap π toκ) (comp 0) comp_pi
      (fun s hs hsπ => ModularCurve.XHDRLevel.eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id p M H hpM hj π κ toκ comp
        comp_isClosedImmersion comp_jointly_surjective comp_pi hnosec s hs hsπ)
      (asIso (fibreMap (overOfIso δ δ_over) toκ)) (asIso (fibreMap (overOfIso δ0 δ0_over) toκ)) hπ'
  refine Fin.forall_fin_two.mpr ⟨h0, ?_⟩
  rw [← comp_w, Category.assoc, hw', ← Category.assoc, h0, Category.assoc]

namespace NodeWrapGen

section Chart
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (A : Type u) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X)
  (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (κ : Type u) [CommRing κ] [Algebra R κ]

include hι in

theorem exists_chart :
    ∃ c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      c ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom) ≫ ι ∧
      c ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, hι]; exact sq.w.symm
  exact ⟨pullback.lift _ _ hcompat, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

include hι in

theorem mem_range_chart
    (c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom) ≫ ι)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))))
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))
    (hx : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base x ∈ Set.range ι.base) :
    x ∈ Set.range c.base := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ι ≫ f) := by
    rw [hcsnd, hι]; exact sq
  have H : IsPullback c
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (pullback.fst _ _) ι :=
    IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip
  have hx' : x ∈ Set.range (pullback.fst (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) ι).base := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨t, rfl⟩ := hx'
  exact ⟨H.isoPullback.inv.base t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

end Chart

section Invol
variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
  (κ : Type u) [CommRing κ] [Algebra R κ]

theorem chart_comp_eq_specMap_tensor_comp_chart
    (w : TwoChartIntegralModel R F j ≅ TwoChartIntegralModel R F j)
    (theta : ↥(TwoChartIntegralModel.chartAlgFin R F j) ≃ₐ[R] ↥(TwoChartIntegralModel.chartAlgFin R F j))
    (hwchart : TwoChartIntegralModel.ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ TwoChartIntegralModel.ιFin R F j)
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(TwoChartIntegralModel.chartAlgFin R F j))) ⟶ pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(TwoChartIntegralModel.chartAlgFin R F j))).toRingHom) ≫ TwoChartIntegralModel.ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(TwoChartIntegralModel.chartAlgFin R F j)))))
    (wκ : pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
      pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hwκfst : wκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ w.hom)
    (hwκsnd : wκ ≫ pullback.snd _ _ = pullback.snd _ _) :
    c ≫ wκ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom) ≫ c := by
  apply pullback.hom_ext
  · rw [Category.assoc, hwκfst, ← Category.assoc, hcfst, Category.assoc, hwchart, Category.assoc, hcfst,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
  · rw [Category.assoc, hwκsnd, hcsnd, Category.assoc, hcsnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => by simp [Algebra.TensorProduct.includeLeftRingHom_apply]

end Invol

end NodeWrapGen

p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in
open NodeWrapGen in

theorem ModularCurve.XHDRLevel.exists_nodeEquiv_place
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)

    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hw : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_pi : comp 0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _)
    (comp_w : comp 0 ≫ fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) = comp 1)

    (Mfib : CurveModel (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))
    (efib : Mfib.C ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) [IsIso efib]
    (hefib : efib ≫ pullback.snd _ _ = Mfib.toBase)
    [Mfib_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
    (Mfib_pin : ∀ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
    coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) →
    ((Mfib.ffEquiv.symm
        (Mfib.C.germToFunctionField
          ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
            ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
          (((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app
              ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓN p M H hpM) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj))).inv b))))
        : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      coeffMap (IsLocalRing.residue ↥A) y)

    (hfrob : ∀ P : closedPoints Mfib.C,
      ∃ h : (inv efib).base ((efib ≫ comp 1 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)).base P.1) ∈ closedPoints Mfib.C,
        Mfib.placeOfPoint ⟨_, h⟩ =
          qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p (Mfib.placeOfPoint P))

    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)

    (hZsnd : ∀ n : ↥(pullback (comp 0) (comp 1)),
      (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((pullback.snd (comp 0) (comp 1)).base n) ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base) :
    ∃ nodeEquiv : ↥(pullback (comp 0) (comp 1)) ≃ ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p),
      ∀ n : ↥(pullback (comp 0) (comp 1)),
        (∃ h : (inv efib).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints Mfib.C,
            Mfib.placeOfPoint ⟨_, h⟩ =
              ((nodeEquiv n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)) :
                Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ∧
        (∃ h : (inv efib).base ((pullback.fst (comp 0) (comp 1)).base n) ∈ closedPoints Mfib.C,
            Mfib.placeOfPoint ⟨_, h⟩ =
              qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p
                ((nodeEquiv n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)) :
                  Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) := by
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  obtain ⟨c₀, hc₀fst, hc₀snd⟩ := exists_chart (toBase p (ΓN p M H hpM) hj) ↥(chartAlgFin p (ΓN p M H hpM) hj)
    (ιFin p (ΓN p M H hpM) hj) (TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) (IsLocalRing.ResidueField ↥A)
  obtain ⟨c, hcfst, hcsnd⟩ := exists_chart (toBase p (ΓM M H) hj) ↥(chartAlgFin p (ΓM M H) hj)
    (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) (IsLocalRing.ResidueField ↥A)
  have hwfst : fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ w.hom := by
    unfold XHDRLevel.fibreMap; rw [pullback.lift_fst]; rfl
  have hwsnd : fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.snd _ _ = pullback.snd _ _ := by
    unfold XHDRLevel.fibreMap; rw [pullback.lift_snd, Category.comp_id]
  have hcw := chart_comp_eq_specMap_tensor_comp_chart (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) (IsLocalRing.ResidueField ↥A)
    w theta hwchart c hcfst hcsnd (fibreMap (overOfIso w hw) ((IsLocalRing.residue ↥A).comp ρ)) hwfst hwsnd
  have hfin : ∀ n : ↥(pullback (comp 0) (comp 1)), (pullback.snd (comp 0) (comp 1)).base n ∈ Set.range c₀.base :=
    fun n => mem_range_chart (toBase p (ΓN p M H hpM) hj) ↥(chartAlgFin p (ΓN p M H hpM) hj) (ιFin p (ΓN p M H hpM) hj)
      (TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) (IsLocalRing.ResidueField ↥A)
      c₀ hc₀fst hc₀snd _ (hZsnd n)
  exact ModularCurve.XHDRLevel.exists_nodeEquiv_placeOfPoint_eq_and_eq_qExpFrobeniusPlaceModL p M H hpM hpM2 hHp hj
    π iota0 iota0_spec pi_chart w hw theta htheta A hA ρ hρ comp comp_over comp_isClosedImmersion comp_pi comp_w
    Mfib efib hefib Mfib_pin hfrob c₀ hc₀fst hc₀snd c hcfst hcsnd hcw hfin

p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in
set_option maxHeartbeats 6400000 in
theorem ModularCurve.XHDRLevel.exists_comp_pair_place
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    [NeZero (M / p)] (hpN : ¬ p ∣ M / p) [(ΓM M H).FiniteIndex] (hTM : ModularGroup.T ∈ ΓM M H)
    [IsProper (toBase p (ΓM M H) hj)] [IsProper (toBase p (ΓN p M H hpM) hj)]
    [SmoothOfRelativeDimension 1 (toBase p (ΓN p M H hpM) hj)]
    [Algebra.FiniteType (R p) ↥(chartAlgInf p (ΓM M H) hj)]
    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (w_over : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)
    (κ : Type) [Field κ] [CharP κ p] (toκ : R p →+* κ)
    {C : Scheme.{0}} (efib : C ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) toκ)
    (hne : Nonempty (Scheme.Opens.toScheme ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))))
    (σ₀ : letI := toκ.toAlgebra
      κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (hσ₀ : letI := toκ.toAlgebra
      ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z)
    (hmin : letI := toκ.toAlgebra
      minimalPrimes (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) =
        {RingHom.ker σ₀.toRingHom,
         Ideal.comap (Algebra.TensorProduct.map (AlgHom.id κ κ)
           (theta : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))).toRingHom (RingHom.ker σ₀.toRingHom)})
    (hne' : letI := toκ.toAlgebra
      RingHom.ker σ₀.toRingHom ≠
        Ideal.comap (Algebra.TensorProduct.map (AlgHom.id κ κ)
           (theta : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))).toRingHom (RingHom.ker σ₀.toRingHom)) :
    ∃ comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) toκ ⟶ fibre (Γ := ΓM M H) (hj := hj) toκ),
      (∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _) ∧
      (∀ i, IsClosedImmersion (comp i)) ∧
      (∀ y : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ), y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base) ∧
      Set.range (comp 0).base ≠ Set.range (comp 1).base ∧
      comp 0 ≫ fibreMap π toκ = 𝟙 _ ∧
      comp 0 ≫ fibreMap (overOfIso w w_over) toκ = comp 1 ∧
      (letI := toκ.toAlgebra
       ∀ (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) toκ)
        (_ : c₀ ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
        (_ : c₀ ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))))
        (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ fibre (Γ := ΓM M H) (hj := hj) toκ)
        (_ : c ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj)
        (_ : c ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := R p) (A := κ) (B := ↥(chartAlgFin p (ΓM M H) hj))))),
        c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c ∧
        ∀ x, (comp 0).base x ∈ Set.range c.base → x ∈ Set.range c₀.base) := by
  letI : Algebra (R p) κ := toκ.toAlgebra
  haveI : IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ)) :=
    ModularCurve.XHDRLevel.CompInstances.isIntegral_fibre_gammaN p M H hpM hj hpN κ toκ
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) :=
    have := AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : Nontrivial (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) :=
    ModularCurve.XHDRLevel.CompInstances.nontrivial_tensor_chartAlgFin_gammaN p M H hpM hj κ toκ efib hne
  have hniso : ∀ x : ↥(fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ)),
      ¬ IsOpen ({x} : Set ↥(fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))) := fun x =>
    ModularCurve.not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP p (ΓM M H) hTM
      (jAt (ΓM M H) hj) (coe_jAt _ hj) κ x
  exact ModularCurve.XHDRLevel.exists_comp_pair_fibre_of_retraction_of_minimalPrimes_eq p M H hpM hj π iota0 pi_chart
    w w_over theta hwchart κ hniso σ₀ hσ₀ hmin hne'

set_option maxHeartbeats 6400000 in
theorem solution (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ∃ (𝔛 : XHDRModelAtP p M H hpM hj) (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
      (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)),

      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) ∧

      (∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) ∧

      ιFin p (ΓM M H) hj ≫ 𝔛.w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj ∧
      𝔛.w.hom ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (ΓM M H) hj).opensRange ∧

      (∀ (b : ↥(chartAlgFin p (ΓM M H) hj)) (f : ↥(xHFunctionFieldBar M H)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := by
  classical
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hMp : NeZero (M / p) := neZero_div p M hpM
  have hpN : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)

  haveI hPID : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI hFrac : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

  have hTM : ModularGroup.T ∈ ΓM M H := translation_mem_GammaH M H
  have hTN : ModularGroup.T ∈ ΓN p M H hpM := translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  have hsub : ΓM M H ≤ ΓN p M H hpM := ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM
  haveI hFI_M : (ΓM M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  haveI hFI_N : (ΓN p M H hpM).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  have hjM : ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = jqModC ℚ := coe_jAt _ hj
  have hjN : ((jAt (ΓN p M H hpM) hj : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = jqModC ℚ := coe_jAt _ hj

  obtain ⟨hFTfin, hFTinf⟩ :=
    ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H) hTM (jAt (ΓM M H) hj) hjM
  obtain ⟨hFTfin0, hFTinf0⟩ :=
    ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓN p M H hpM) hTN (jAt (ΓN p M H hpM) hj) hjN
  haveI := hFTfin; haveI := hFTinf; haveI := hFTfin0; haveI := hFTinf0

  obtain ⟨hProper0, hSmooth0, -⟩ :=
    ModularCurve.isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd
      (M / p) (ΓN p M H hpM) (Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
      (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM)) p hpN (jAt (ΓN p M H hpM) hj) hjN

  have hjq : ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = coeffEmb ℚ ModularCurve.jq := by
    rw [hjM, jqModC_rat]; ext k; rw [coeffEmb_coeff]; simp
  haveI hIST : IsScalarTower (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have htjR : Transcendental (R p) (jAt (ΓM M H) hj) :=
    @ModularCurve.transcendental_of_coe_eq_coeffEmb_jq ℚ _ _ (qExpFunctionFieldC ℚ (ΓM M H)) (R p) _ _ _ hFrac _
      (@IsScalarTower.of_algebraMap_eq (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ _ _
        (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) _ fun x =>
          (IsScalarTower.algebraMap_apply (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) x).trans
            (RingHom.congr_fun (Subsingleton.elim _ _) _))
      (jAt (ΓM M H) hj) hjq
  have htjQ : Transcendental ℚ (jAt (ΓM M H) hj) := fun h =>
    htjR ((IsFractionRing.isAlgebraic_iff (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H))).mpr h)

  have hfdQ : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))))
      ↥(qExpFunctionFieldC ℚ (ΓM M H)) := by
    convert (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (ΓM M H) hTM (ΓM M H)
      le_rfl (fun γ hγ => Or.inl hγ) (jAt (ΓM M H) hj) hjM).1 <;> exact Subsingleton.elim _ _
  have hregQ : ∀ x : ↥(qExpFunctionFieldC ℚ (ΓM M H)), IsAlgebraic ℚ x → ∃ c : ℚ, x = algebraMap ℚ _ c :=
    fun x hx => ModularCurve.exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC (ΓM M H) x hx
  obtain ⟨Meta, eeta, heetaIso, heeta, hgal, hMetaNe, hMetaPin⟩ :=
    ModularCurve.exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
      (qExpFunctionFieldC ℚ (ΓM M H)) p (jAt (ΓM M H) hj) htjQ hfdQ hregQ

  have hsepQ : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))))
      ↥(qExpFunctionFieldC ℚ (ΓM M H)) := by
    haveI := hfdQ; infer_instance
  have hsmooth_generic : SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) :=
    AlgebraicCurve.TwoChartIntegralModel.smoothOfRelativeDimension_one_pullback_snd_toBase_of_charZero
      (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) htjR hfdQ hsepQ ℚ

  have hgeom : GeometricallyIntegral
      (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) :=
    ModularCurve.geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat (ΓM M H) p (jAt (ΓM M H) hj)

  have hjinv : ∀ n : ℤ, n ≤ 0 → (((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)⁻¹).coeff n = 0 :=
    fun n hn => by rw [hjM]; exact ModularCurve.XHDRLevel.coeff_inv_jqModC_eq_zero_of_nonpos n hn
  obtain ⟨rhoInf, hrho⟩ :=
    ModularCurve.exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero (qExpFunctionFieldC ℚ (ΓM M H)) p (jAt (ΓM M H) hj) hjinv

  have hεsec : (Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ ιInf p (ΓM M H) hj) ≫ toBase p (ΓM M H) hj = 𝟙 _ := by
    rw [Category.assoc]
    erw [TwoChartIntegralModel.ιInf_toBase]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : rhoInf.toRingHom.comp (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj)) = RingHom.id _ := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  let εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj) :=
    ⟨Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ ιInf p (ΓM M H) hj, by rw [hεsec]⟩

  obtain ⟨σ, hσq, hσdia⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  let σR : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[R p] ↥(qExpFunctionFieldC ℚ (ΓM M H)) := σ.restrictScalars (R p)
  haveI hσj : Fact (σR (jAt (ΓM M H) hj) ≠ 0) :=
    ⟨fun h => (Fact.out : jAt (ΓM M H) hj ≠ 0) (by simpa using congrArg σR.symm h)⟩

  obtain ⟨hFTinfσ, -, hSepσ, hSep⟩ := wFrame_at_sigma p M H hj σR
  haveI := hFTinfσ; haveI := hSepσ; haveI := hSep

  have hIST' : @IsScalarTower (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) Algebra.toSMul
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))).toSMul Algebra.toSMul :=
    @IsScalarTower.of_algebraMap_eq (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ _ _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) _ fun x =>
        (IsScalarTower.algebraMap_apply (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) x).trans
          (RingHom.congr_fun (Subsingleton.elim _ _) _)
  have hσj : ((σR (jAt (ΓM M H) hj) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ) := by
    have := hσq (jAt (ΓM M H) hj) (jAt (ΓN p M H hpM) hj) (by rw [hjM, hjN])
    rw [hjN] at this
    exact this
  obtain ⟨hWfin, hWfin', hWvis, hWvis'⟩ := wInt_at_sigma p M H hj σR (hST := hIST') hσj
  obtain ⟨w, θc, hwover, hθc, hwchart, hwpre⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv
      (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) σR hWfin hWfin' hWvis hWvis'

  let εzero : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj) :=
    ⟨εinf.1 ≫ w.hom, by rw [Category.assoc, hwover]; exact εinf.2⟩

  obtain ⟨πX, iota0, iotaInf, hπover, hiota0, hpichart, hiotaInf, hpichartInf, hπfinite, hπsurj, hπpre⟩ :=
    ModularCurve.exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le p (ΓM M H) (ΓN p M H hpM) hsub hTM
      (jAt (ΓM M H) hj) hjM (jAt (ΓN p M H hpM) hj) hjN
  let π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj) := ⟨πX, hπover⟩

  choose Mfib efib hefibIso hMfibNe hefib hMfibPin using
    (fun (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      (i1 : CharP (IsLocalRing.ResidueField ↥A) p) (i2 : IsAlgClosed (IsLocalRing.ResidueField ↥A))
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) =>
      ModularCurve.exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
        (M / p) (ΓN p M H hpM) (Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
        (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM)) p hpN (jAt (ΓN p M H hpM) hj) hjN A hA ρ hρ)

  haveI hProperM : IsProper (toBase p (ΓM M H) hj) :=
    AlgebraicCurve.TwoChartIntegralModel.isProper_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
  haveI := hProper0
  haveI := hSmooth0

  have htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((θc (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := fun b => by
    rw [hθc]
    exact hσq _ _ (hiota0 b)
  have hPQ := fun (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      (i1 : CharP (IsLocalRing.ResidueField ↥A) p) (i2 : IsAlgClosed (IsLocalRing.ResidueField ↥A))
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) =>
    ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_pair_and_retraction_pair_chartAlgFin_gammaH p M H hpM hpM2 hHp hj
      iota0 hiota0 θc htheta A hA ρ hρ
  choose θfr σ₀ hθfr1 hθfr2 hθfr_ne hθfr_min hθfr_frob hθfr_frob' hσ₀ hσ₀surj hmin hne hσ₀link using hPQ

  have hcomp := fun (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      (i1 : CharP (IsLocalRing.ResidueField ↥A) p) (i2 : IsAlgClosed (IsLocalRing.ResidueField ↥A))
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) =>
    ModularCurve.XHDRLevel.exists_comp_pair_place p M H hpM hj hpN hTM π iota0 hpichart w hwover θc hwchart
      (IsLocalRing.ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (efib A hA i1 i2 ρ hρ) (hMfibNe A hA i1 i2 ρ hρ)
      (σ₀ A hA i1 i2 ρ hρ) (hσ₀ A hA i1 i2 ρ hρ) (hmin A hA i1 i2 ρ hρ) (hne A hA i1 i2 ρ hρ)
  choose comp hcomp_over hcomp_ci hcomp_surj hcomp_ne hcomp_pi hcomp_w hcomp_chart using hcomp

  have hXF := fun (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      (i1 : CharP (IsLocalRing.ResidueField ↥A) p) (i2 : IsAlgClosed (IsLocalRing.ResidueField ↥A))
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) =>
    ModularCurve.XHDRLevel.fst_fst_pullback_comp_mem_range_iotaFin_and_fst_snd_pullback_comp_mem_range_iotaFin_of_chart_atkinLehner
      p M H hpM hpM2 hHp hj π iota0 hiota0 hpichart w hwover θc htheta hwchart A hA ρ hρ
      (comp A hA i1 i2 ρ hρ) (hcomp_over A hA i1 i2 ρ hρ) (hcomp_ci A hA i1 i2 ρ hρ) (hcomp_pi A hA i1 i2 ρ hρ) (hcomp_w A hA i1 i2 ρ hρ)
  have hZ := fun A hA i1 i2 ρ hρ => (hXF A hA i1 i2 ρ hρ).1
  have hZsnd := fun A hA i1 i2 ρ hρ => (hXF A hA i1 i2 ρ hρ).2

  have hfinFrob : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
      FiniteAlong (IsLocalRing.ResidueField ↥A) (qExpFrobeniusModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p) :=
    fun A hA _ _ ρ hρ => by
      obtain ⟨x, -, htx, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
        (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) hTN
      obtain ⟨⟨_, hfin, -, -⟩, -⟩ := ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
        (IsLocalRing.ResidueField ↥A) (ℓ := p) (ΓN p M H hpM) ⟨x, htx, hfd⟩
      exact hfin

  obtain ⟨hc1pp, hpiw⟩ :=
    ModularCurve.XHDRLevel.comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner p M H hpM hpM2 hHp hj π iota0 hiota0 hpichart
      w hwover θc hwchart htheta
      (fun A hA _ _ ρ hρ => Mfib A hA _ _ ρ hρ) (fun A hA _ _ ρ hρ => efib A hA _ _ ρ hρ)
      (efib_iso := fun A hA _ _ ρ hρ => hefibIso A hA _ _ ρ hρ) (fun A hA _ _ ρ hρ => hefib A hA _ _ ρ hρ)
      (Mfib_chart_nonempty := fun A hA _ _ ρ hρ => hMfibNe A hA _ _ ρ hρ) (fun A hA _ _ ρ hρ => hMfibPin A hA _ _ ρ hρ)
      (fun A hA _ _ ρ hρ => comp A hA _ _ ρ hρ) (fun A hA _ _ ρ hρ => hcomp_over A hA _ _ ρ hρ)
      (fun A hA _ _ ρ hρ => hcomp_ci A hA _ _ ρ hρ) (fun A hA _ _ ρ hρ => hcomp_pi A hA _ _ ρ hρ)
      (fun A hA _ _ ρ hρ => hcomp_w A hA _ _ ρ hρ) hfinFrob

  have hX2 := fun (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      (i1 : CharP (IsLocalRing.ResidueField ↥A) p) (i2 : IsAlgClosed (IsLocalRing.ResidueField ↥A))
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) =>
    @ModularCurve.XHDRLevel.exists_nodeEquiv_place p M _ _ H hpM hpM2 hHp hj π iota0 hiota0 hpichart w hwover θc htheta
      A hA i1 i2 ρ hρ (comp A hA i1 i2 ρ hρ) (hcomp_over A hA i1 i2 ρ hρ) (hcomp_ci A hA i1 i2 ρ hρ) (hcomp_pi A hA i1 i2 ρ hρ)
      (hcomp_w A hA i1 i2 ρ hρ) (Mfib A hA i1 i2 ρ hρ) (efib A hA i1 i2 ρ hρ) (hefibIso A hA i1 i2 ρ hρ) (hefib A hA i1 i2 ρ hρ)
      (hMfibNe A hA i1 i2 ρ hρ) (hMfibPin A hA i1 i2 ρ hρ) (hc1pp A hA ρ hρ) hwchart (hZsnd A hA i1 i2 ρ hρ)
  choose nodeEquiv hnode using hX2

  obtain ⟨ρMa, hρMa_H, -, hρMa_0, hρMa_slash⟩ :=
    ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ M H
  obtain ⟨ρNa, hρNa_H, -, hρNa_0, hρNa_slash⟩ :=
    ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ (M / p) (infSubgroup p M H hpM)
  let ρM := Ws19Glue.toRingAutHom ρMa
  let ρN := Ws19Glue.toRingAutHom ρNa
  have hρM_H : ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρM γ = 1 := fun γ hγ =>
    Ws19Glue.toRingAutHom_eq_one ρMa γ (hρMa_H γ hγ)
  have hρN_H : ∀ γ : CongruenceSubgroup.Gamma0 (M / p), (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) → ρN γ = 1 :=
    fun γ hγ => Ws19Glue.toRingAutHom_eq_one ρNa γ (hρNa_H γ hγ)
  have hρM_apply : ∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ↥(qExpFunctionFieldC ℚ (ΓM M H))), ρM γ x = ρMa γ x := fun _ _ => rfl
  have hρN_apply : ∀ (γ : CongruenceSubgroup.Gamma0 (M / p)) (x : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))), ρN γ x = ρNa γ x :=
    fun _ _ => rfl

  haveI hSep0 : IsSeparated (toBase p (ΓN p M H hpM) hj) := by haveI := hProper0; infer_instance
  obtain ⟨dia, diaFin, diaInf, hdia_over, hdia_mul, hdia_mem, hdia_pin⟩ :=
    ModularCurve.exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond M H p (jAt (ΓM M H) hj) hjM ρM hρM_H
      (fun γ x hx => by rw [hρM_apply]; exact hρMa_0 γ x hx)
  obtain ⟨dia0, dia0Fin, dia0Inf, hdia0_over, hdia0_mul, hdia0_mem, hdia0_pin⟩ :=
    ModularCurve.exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond (M / p) (infSubgroup p M H hpM) p
      (jAt (ΓN p M H hpM) hj) hjN ρN hρN_H (fun γ x hx => by rw [hρN_apply]; exact hρNa_0 γ x hx)

  have hpi_dia : ∀ d : (ZMod M)ˣ,
      (dia d).hom ≫ πX = πX ≫ (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).hom := by
    intro d
    obtain ⟨γ, hγ⟩ := Ws19Glue.exists_gamma0_apply_eq (M := M) d
    let γ' : CongruenceSubgroup.Gamma0 (M / p) :=
      ⟨γ, by
        have h := CongruenceSubgroup.Gamma0_mem.mp γ.2
        rw [CongruenceSubgroup.Gamma0_mem]
        have := congrArg (ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p))) h
        rwa [map_intCast, map_zero] at this⟩
    have hγ' : (((γ' : SL(2, ℤ)) 0 0 : ℤ) : ZMod (M / p)) = ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) := by
      rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ← hγ]
      show (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod (M / p)) = ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p)) ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))
      rw [map_intCast]
    obtain ⟨hFv, -, hFp, -⟩ := hdia_pin d γ hγ
    obtain ⟨hFv0, -, hFp0, -⟩ := hdia0_pin (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) γ' hγ'

    have hchart : ∀ x, diaFin d (iota0 x) = iota0 (dia0Fin (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) x) := by
      intro x
      apply Subtype.ext; apply Subtype.ext
      rw [hFv, hiota0]
      show ((ρM γ (iota0 x : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        (((dia0Fin (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) x : ↥(chartAlgFin p (ΓN p M H hpM) hj)) :
          ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)
      rw [hFv0]
      exact ModularCurve.coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup p M H hpM ρM hρM_H
        (fun γ k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hf₁' hg₁' hg0 hg₁0 => by
          rw [hρM_apply]
          exact hρMa_slash γ f g f₁ g₁ c hc hf hg hf₁ hg₁ hf₁' hg₁' hg0 hg₁0)
        ρN hρN_H
        (fun γ k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hf₁' hg₁' hg0 hg₁0 => by
          rw [hρN_apply]
          exact hρNa_slash γ f g f₁ g₁ c hc hf hg hf₁ hg₁ hf₁' hg₁' hg0 hg₁0)
        γ γ' rfl _ _ (hiota0 x)

    have P : (dia d).inv ≫ πX = πX ≫ (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).inv := by
      refine AlgebraicCurve.TwoChartIntegralModel.hom_ext_of_iotaFin_comp_eq (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
        _ _ (toBase p (ΓN p M H hpM) hj) ?_ ?_
      · have hdinv : (dia d).inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by rw [Iso.inv_comp_eq, hdia_over]
        have hd0inv : (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).inv ≫ toBase p (ΓN p M H hpM) hj = toBase p (ΓN p M H hpM) hj := by
          rw [Iso.inv_comp_eq, hdia0_over]
        rw [Category.assoc, hπover, hdinv, Category.assoc, hd0inv, hπover]
      · rw [← Category.assoc, ← hFp, Category.assoc, hpichart, ← Category.assoc, ← Spec.map_comp,
          ← Category.assoc, hpichart, Category.assoc, ← hFp0, ← Category.assoc, ← Spec.map_comp]
        congr 2
        rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        congr 1
        exact RingHom.ext fun x => hchart x
    calc (dia d).hom ≫ πX
        = (dia d).hom ≫ ((dia d).inv ≫ πX) ≫ (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).hom := by
          rw [P, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = πX ≫ (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).hom := by rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

  obtain ⟨hCRfin, hCRinf⟩ :=
    ModularCurve.XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH p M H hpM hpM2 hHp hj

  haveI hIntX : IsIntegral (X p (ΓM M H) hj) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegral (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
  have hinj : Function.Injective (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
    intro a b h
    rw [IsScalarTower.algebraMap_apply (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) a,
      IsScalarTower.algebraMap_apply (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) b] at h
    exact Subtype.ext ((algebraMap ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H))).injective h)
  haveI hFlatX : Flat (toBase p (ΓM M H) hj) :=
    AlgebraicCurve.TwoChartIntegralModel.flat_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) hinj
  haveI hLfpX : LocallyOfFinitePresentation (toBase p (ΓM M H) hj) :=
    AlgebraicCurve.TwoChartIntegralModel.locallyOfFinitePresentation_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
  haveI hIntQ := ModularCurve.isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero (ΓM M H) p (jAt (ΓM M H) hj) ℚ
  have hdim : ∀ V : (X p (ΓM M H) hj).Opens, Smooth (V.ι ≫ toBase p (ΓM M H) hj) →
      SmoothOfRelativeDimension 1 (V.ι ≫ toBase p (ΓM M H) hj) := fun V hV => by
    haveI := hsmooth_generic; haveI := hV
    exact AlgebraicGeometry.smoothOfRelativeDimension_one_ι_comp_of_smooth_of_smoothOfRelativeDimension_pullback_snd
      (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))) V
  obtain ⟨U, hUrel, hUmax, hUimg, hUstab⟩ :=
    AlgebraicGeometry.exists_smooth_maximal_and_image_eq_of_iso_over (toBase p (ΓM M H) hj) 1 hdim

  have hINFOFF : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [i1 : CharP (IsLocalRing.ResidueField ↥A) p] [i2 : IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
      Set.range (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ (Set.range (comp A hA i1 i2 ρ hρ 1).base)ᶜ :=
    fun A hA i1 i2 ρ hρ => by
      haveI := hcomp_ci A hA i1 i2 ρ hρ 0; haveI := hcomp_ci A hA i1 i2 ρ hρ 1
      exact (ModularCurve.XHDRLevel.range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id
        p M H hpM hpM2 hHp hj εinf rhoInf (fun b => (hrho b).2) rfl π iota0 hiota0 hpichart θc htheta iotaInf hiotaInf hpichartInf
        A hA ρ hρ (comp A hA i1 i2 ρ hρ 0) (hcomp_over A hA i1 i2 ρ hρ 0) (hcomp_pi A hA i1 i2 ρ hρ)
        (comp A hA i1 i2 ρ hρ 1) (hcomp_over A hA i1 i2 ρ hρ 1) (hcomp_surj A hA i1 i2 ρ hρ)).1
  have hεU : Set.range εinf.1.base ⊆ (U : Set (X p (ΓM M H) hj)) :=
    ModularCurve.XHDRLevel.range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one p M H hpM hj U hUmax
      (fun A hA _ _ ρ hρ =>
        AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast
          p ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) hCRfin hCRinf (IsLocalRing.ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ))
      (fun A hA i1 i2 ρ hρ => comp A hA i1 i2 ρ hρ) (fun A hA i1 i2 ρ hρ => hcomp_over A hA i1 i2 ρ hρ)
      (fun A hA i1 i2 ρ hρ => hcomp_ci A hA i1 i2 ρ hρ) (fun A hA i1 i2 ρ hρ => hcomp_surj A hA i1 i2 ρ hρ) εinf
      (fun A hA i1 i2 ρ hρ => hINFOFF A hA ρ hρ)
  have hε0U : Set.range εzero.1.base ⊆ (U : Set (X p (ΓM M H) hj)) := hUstab w hwover _ εinf.1 hεU

  obtain ⟨θ, hθσ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ) (xHFunctionField M H) σ.toRingEquiv

  let ι : ↥(chartAlgFin p (ΓM M H) hj) → ↥(xHFunctionFieldBar M H) := fun a =>
    ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩
  have hι : ∀ a : ↥(chartAlgFin p (ΓM M H) hj), ((ι a : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := fun _ => rfl
  have hread : ∀ a : ↥(chartAlgFin p (ΓM M H) hj), θ (ι a) = ι (θc a) := by
    intro a
    apply Subtype.ext
    show ((θ (ι a) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) _
    rw [hθc a]
    exact hθσ (a : ↥(qExpFunctionFieldC ℚ (ΓM M H)))
  have hint : θ.toAlgHom.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ θ.surjective
  have hfinAlong : FiniteAlong (AlgebraicClosure ℚ) θ.toAlgHom := by
    unfold FiniteAlong
    exact RingHom.Finite.of_surjective θ.toAlgHom.toRingHom θ.surjective

  have hθ : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
      ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) :=
    htheta_bc p M H hpM σ hσq θ hθσ

  have hθβ : ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
            LaurentSeries (AlgebraicClosure ℚ)) :=
    htheta_bc2 p M H hpM σ hσdia θ hθσ
  have hbar1 : ∀ (d : (ZMod M)ˣ) (z : ↥(xHFunctionFieldBar M H)), θ (diamondAutHBar M H d z) = diamondAutHBar M H d (θ z) :=
    fun d z => ModularCurve.algEquiv_diamondAutHBar_comm_of_qExpand_of_diamondAutHBar_div p M H hpM hpM2 hHp θ hθ hθβ d z
  have hbar2 : ∀ (d : (ZMod M)ˣ), ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 →
      ∀ z : ↥(xHFunctionFieldBar M H), diamondAutHBar M H d (θ (θ z)) = z :=
    fun d hd z => ModularCurve.diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one
      p M H hpM hpM2 hHp θ hθ hθβ d hd z

  have hcinj : Function.Injective (coeffEmb (AlgebraicClosure ℚ) : LaurentSeries ℚ → LaurentSeries (AlgebraicClosure ℚ)) := by
    intro x y hxy
    ext k
    have := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => z.coeff k) hxy
    simp only [coeffEmb, coeffMap_coeff] at this
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective this
  have hDFF : ∀ (d : (ZMod M)ˣ) (γ : CongruenceSubgroup.Gamma0 M), (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∀ x : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
        ((diamondAutHBar M H d ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) ((ρM γ x : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) :=
    fun d γ hγ x => ModularCurve.diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply M H ρM hρM_H
      (fun γ k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hf₁' hg₁' hg0 hg₁0 =>
        hρMa_slash γ f g f₁ g₁ c hc hf hg hf₁ hg₁ hf₁' hg₁' hg0 hg₁0) d γ hγ x

  let emb : ↥(qExpFunctionFieldC ℚ (ΓM M H)) → ↥(xHFunctionFieldBar M H) := fun x =>
    ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩
  have hemb_σ : ∀ x, θ (emb x) = emb (σ x) := fun x => Subtype.ext (hθσ x)
  have hemb_ρ : ∀ (d : (ZMod M)ˣ) (γ : CongruenceSubgroup.Gamma0 M), (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∀ x, diamondAutHBar M H d (emb x) = emb (ρM γ x) := fun d γ hγ x => Subtype.ext (hDFF d γ hγ x)
  have hemb_inj : Function.Injective emb := fun x y h => Subtype.ext (hcinj (congrArg Subtype.val h))

  have hWDIA : ∀ (d : (ZMod M)ˣ) (γ : CongruenceSubgroup.Gamma0 M), (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∀ x, σ (ρM γ x) = ρM γ (σ x) := by
    intro d γ hγ x
    apply hemb_inj
    rw [← hemb_σ, ← hemb_ρ d γ hγ, hbar1, hemb_σ, hemb_ρ d γ hγ]
  have hWSQ : ∀ (d : (ZMod M)ˣ), ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 →
      ∀ (γ : CongruenceSubgroup.Gamma0 M), (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) → ∀ x, ρM γ (σ (σ x)) = x := by
    intro d hd γ hγ x
    apply hemb_inj
    rw [← hemb_ρ d γ hγ, ← hemb_σ, ← hemb_σ, hbar2 d hd]
  have hwchart' : ιFin p (ΓM M H) hj ≫ w.hom =
      Spec.map (CommRingCat.ofHom (θc : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)).toRingHom) ≫ ιFin p (ΓM M H) hj :=
    hwchart
  have hw_dia : ∀ d : (ZMod M)ˣ, w.hom ≫ (dia d).hom = (dia d).hom ≫ w.hom := by
    intro d
    obtain ⟨γ, hγ⟩ := Ws19Glue.exists_gamma0_apply_eq (M := M) d
    obtain ⟨hFv, -, hFp, -⟩ := hdia_pin d γ hγ
    refine (AlgebraicCurve.TwoChartIntegralModel.hom_comm_and_hom_comp_hom_eq_of_chartPins (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H))
      (jAt (ΓM M H) hj) w hwover _ hwchart' (dia d) (hdia_over d) (diaFin d) hFp).1 fun x => ?_
    apply Subtype.ext
    show ((θc (diaFin d x) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) =
      ((diaFin d (θc x) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    rw [hθc, hFv, hFv, hθc, hρM_apply]
    exact hWDIA d γ hγ _
  have hw_sq : ∀ d : (ZMod M)ˣ,
      ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 →
        w.hom ≫ w.hom = (dia d).hom := by
    intro d hd
    obtain ⟨γ, hγ⟩ := Ws19Glue.exists_gamma0_apply_eq (M := M) d
    obtain ⟨hFv, -, hFp, -⟩ := hdia_pin d γ hγ
    refine (AlgebraicCurve.TwoChartIntegralModel.hom_comm_and_hom_comp_hom_eq_of_chartPins (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H))
      (jAt (ΓM M H) hj) w hwover _ hwchart' (dia d) (hdia_over d) (diaFin d) hFp).2 fun x => ?_
    apply Subtype.ext
    show ((diaFin d (θc (θc x)) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = (x : ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    rw [hFv, hθc, hθc, hρM_apply]
    exact hWSQ d hd γ hγ _

  haveI := heetaIso

  let MetaX : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := Meta

  have hρM_eq : ∀ γ γ' : CongruenceSubgroup.Gamma0 M,
      (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (((γ' : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) → ρM γ = ρM γ' := by
    intro γ γ' h
    have hmem := Ws19Glue.Gamma1_le_GammaH' H (Ws19Glue.mul_inv_mem_Gamma1 γ γ' h)
    have := hρM_H _ hmem
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have pinM : ∀ a : ↥(chartAlgFin p (ΓM M H) hj),
      MetaX.ffEquiv.symm
        (MetaX.C.germToFunctionField
          ((eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
          (((eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓM M H) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv a)))) = ι a :=
    fun a => Subtype.ext ((hMetaPin a).trans (hι a).symm)
  have hdia_generic : ∀ (d : (ZMod M)ˣ)
      (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ MetaX.C // s ≫ MetaX.toBase = 𝟙 _}),
      x'.1 ≫ eeta ≫ pullback.fst _ _ = x.1 ≫ eeta ≫ pullback.fst _ _ ≫ (dia d).hom →
      MetaX.pointEquivPlace x' = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • MetaX.pointEquivPlace x := by
    intro d x x' hxx'
    obtain ⟨γ', hγ'⟩ := Ws19Glue.exists_gamma0_apply_eq (M := M) d⁻¹
    obtain ⟨γd, hγd⟩ := Ws19Glue.exists_gamma0_apply_eq (M := M) d
    obtain ⟨hFv, -, hFp, -⟩ := hdia_pin d⁻¹ γ' hγ'

    have h1d : dia 1 = Iso.refl _ := hdia_mem 1 (one_mem H)
    have hhom : (dia d⁻¹).hom ≫ (dia d).hom = 𝟙 _ := by
      rw [← hdia_mul, inv_mul_cancel, h1d]; rfl
    have hinv : (dia d⁻¹).inv = (dia d).hom := by
      calc (dia d⁻¹).inv = (dia d⁻¹).inv ≫ ((dia d⁻¹).hom ≫ (dia d).hom) := by rw [hhom, Category.comp_id]
        _ = (dia d).hom := by rw [Iso.inv_hom_id_assoc]

    have hchart : ιFin p (ΓM M H) hj ≫ (dia d).hom = Spec.map (CommRingCat.ofHom (diaFin d⁻¹).toRingHom) ≫ ιFin p (ΓM M H) hj := by
      rw [← hinv]; exact hFp.symm

    obtain ⟨Φ, hΦ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ) (xHFunctionField M H) (ρM γ')
    have hΦemb : ∀ y, Φ (emb y) = emb (ρM γ' y) := fun y => Subtype.ext (hΦ y)
    have hΦθ : ∀ a : ↥(chartAlgFin p (ΓM M H) hj), Φ (ι a) = ι (diaFin d⁻¹ a) := by
      intro a
      apply Subtype.ext
      show ((Φ (emb (a : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((diaFin d⁻¹ a : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)
      rw [hΦemb, hFv]
    have hintΦ : Φ.toAlgHom.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ Φ.surjective
    have hfinΦ : FiniteAlong (AlgebraicClosure ℚ) Φ.toAlgHom := by
      unfold FiniteAlong
      exact RingHom.Finite.of_surjective Φ.toAlgHom.toRingHom Φ.surjective
    have h1 := AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin
      (R p) (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
      ι ι MetaX eeta heeta hMetaNe pinM MetaX eeta heeta hMetaNe pinM
      (dia d).hom (hdia_over d) (diaFin d⁻¹) hchart Φ.toAlgHom hΦθ hintΦ hfinΦ
      x x' (by simpa only [Category.assoc] using hxx')
    rw [h1, AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul]

    have hgen : ∀ (φ ψ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)),
        (∀ y : ↥(qExpFunctionFieldC ℚ (ΓM M H)), φ (emb y) = ψ (emb y)) → φ = ψ := by
      intro φ ψ hφψ
      refine IntermediateField.algHom_ext_of_eq_adjoin (F := AlgebraicClosure ℚ)
        (S := xHFunctionFieldBar M H) (s := ⇑(coeffEmb (AlgebraicClosure ℚ)) '' ((xHFunctionField M H : Set (LaurentSeries ℚ)))) rfl ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hφψ ⟨y, hy⟩
    have hΦD : Φ = diamondAutHBar M H d⁻¹ := by
      apply AlgEquiv.ext
      intro z
      exact AlgHom.congr_fun (hgen (Φ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (diamondAutHBar M H d⁻¹)
        (fun y => by rw [AlgEquiv.coe_algHom, AlgEquiv.coe_algHom, hΦemb, hemb_ρ d⁻¹ γ' hγ'])) z
    have hDD : ∀ z, diamondAutHBar M H d (diamondAutHBar M H d⁻¹ z) = z := by
      have key := hgen ((diamondAutHBar M H d : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] _).comp (diamondAutHBar M H d⁻¹))
        (AlgHom.id _ _) (fun y => by
          rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.coe_algHom, hemb_ρ d⁻¹ γ' hγ', hemb_ρ d γd hγd, AlgHom.id_apply]
          have hprod : ρM (γd * γ') = 1 := by
            rw [hρM_eq (γd * γ') 1 ?_, map_one]
            have h10' : (((γ' : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := CongruenceSubgroup.Gamma0_mem.mp γ'.2
            show ((((γd : SL(2, ℤ)) * (γ' : SL(2, ℤ))) 0 0 : ℤ) : ZMod M) = ((((1 : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)
            rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
            push_cast
            rw [h10', mul_zero, add_zero, hγd, hγ']
            show (d : ZMod M) * ((d⁻¹ : (ZMod M)ˣ) : ZMod M) = ((((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M)
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
            simp
          show emb ((ρM γd * ρM γ') y) = emb y
          rw [← map_mul, hprod]
          rfl)
      intro z
      exact AlgHom.congr_fun key z
    have hsymm : Φ.symm = diamondAutHBar M H d := by
      rw [hΦD]
      apply AlgEquiv.ext
      intro z
      calc (diamondAutHBar M H d⁻¹).symm z
          = diamondAutHBar M H d (diamondAutHBar M H d⁻¹ ((diamondAutHBar M H d⁻¹).symm z)) := (hDD _).symm
        _ = diamondAutHBar M H d z := by rw [AlgEquiv.apply_symm_apply]
    rw [hsymm]

  have hnosec := fun (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      (i1 : CharP (IsLocalRing.ResidueField ↥A) p) (i2 : IsAlgClosed (IsLocalRing.ResidueField ↥A))
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) =>
    @ModularCurve.XHDRLevel.comp_one_comp_fibreMap_ne_id_of_theta_iota0_eq_qExpand_of_liesOverPrime p M _ _ H hpM hpM2 hHp hj
      π iota0 hiota0 hpichart w hwover θc hwchart htheta A hA i1 i2 ρ hρ
      (ModularCurve.XHDRLevel.CompInstances.isIntegral_fibre_gammaN p M H hpM hj hpN (IsLocalRing.ResidueField ↥A)
        ((IsLocalRing.residue ↥A).comp ρ))
      (comp A hA i1 i2 ρ hρ) (hcomp_over A hA i1 i2 ρ hρ) (hcomp_ci A hA i1 i2 ρ hρ) (hcomp_pi A hA i1 i2 ρ hρ) (hcomp_w A hA i1 i2 ρ hρ)

  have hcomp_dia := fun (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      (i1 : CharP (IsLocalRing.ResidueField ↥A) p) (i2 : IsAlgClosed (IsLocalRing.ResidueField ↥A))
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (d : (ZMod M)ˣ) =>
    @ModularCurve.XHDRLevel.comp_dia_place p M _ _ H hpM hj π w hwover (dia d) (hdia_over d)
      (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)) (hdia0_over _) (hpi_dia d) (hw_dia d)
      (IsLocalRing.ResidueField ↥A) _ ((IsLocalRing.residue ↥A).comp ρ)
      (ModularCurve.XHDRLevel.CompInstances.isIntegral_fibre_gammaN p M H hpM hj hpN (IsLocalRing.ResidueField ↥A)
        ((IsLocalRing.residue ↥A).comp ρ))
      (comp A hA i1 i2 ρ hρ) (hcomp_ci A hA i1 i2 ρ hρ) (hcomp_surj A hA i1 i2 ρ hρ) (hcomp_pi A hA i1 i2 ρ hρ)
      (hcomp_w A hA i1 i2 ρ hρ) (hnosec A hA i1 i2 ρ hρ)

  let 𝔛 : XHDRModelAtP p M H hpM hj :=
  {
    isProper := hProperM
    flat := hFlatX
    isIntegral := hIntX
    lfp := hLfpX
    normal := fun U' hU' =>
      AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_sections_of_isAffineOpen (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) U' hU'
    isProper0 := hProper0
    smooth0 := hSmooth0

    Meta := Meta
    eeta := eeta
    eeta_iso := heetaIso
    heeta := heeta
    hgal := hgal
    Meta_chart_nonempty := hMetaNe
    Meta_pin := hMetaPin
    smooth_generic := hsmooth_generic
    geomIntegral_generic := hgeom

    εinf := εinf
    εzero := εzero
    rhoInf := rhoInf
    rhoInf_spec := fun b => (hrho b).2
    εinf_chart := rfl
    w := w
    w_over := hwover
    w_sections := rfl
    dia := dia
    dia_over := hdia_over
    dia_mul := hdia_mul
    dia_mem := hdia_mem
    dia_generic := hdia_generic
    w_dia := hw_dia
    w_sq := hw_sq
    π := π
    iota0 := iota0
    iota0_spec := hiota0
    pi_chart := hpichart
    iotaInf := iotaInf
    iotaInf_spec := hiotaInf
    pi_chartInf := hpichartInf
    dia0 := dia0
    dia0_over := hdia0_over
    pi_dia := hpi_dia

    smoothLocus := U
    smoothLocus_relDim := hUrel
    smoothLocus_maximal := hUmax
    εinf_mem_smoothLocus := hεU
    εzero_mem_smoothLocus := hε0U

    fibre_reduced := @fun A hA i1 i2 ρ hρ =>
      AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast
        p ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) hCRfin hCRinf (IsLocalRing.ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)
    Mfib := @fun A hA i1 i2 ρ hρ => Mfib A hA i1 i2 ρ hρ
    efib := @fun A hA i1 i2 ρ hρ => efib A hA i1 i2 ρ hρ
    efib_iso := @fun A hA i1 i2 ρ hρ => hefibIso A hA i1 i2 ρ hρ
    hefib := @fun A hA i1 i2 ρ hρ => hefib A hA i1 i2 ρ hρ
    Mfib_chart_nonempty := @fun A hA i1 i2 ρ hρ => hMfibNe A hA i1 i2 ρ hρ
    Mfib_pin := @fun A hA i1 i2 ρ hρ => hMfibPin A hA i1 i2 ρ hρ
    comp := @fun A hA i1 i2 ρ hρ => comp A hA i1 i2 ρ hρ
    comp_over := @fun A hA i1 i2 ρ hρ => hcomp_over A hA i1 i2 ρ hρ
    comp_isClosedImmersion := @fun A hA i1 i2 ρ hρ => hcomp_ci A hA i1 i2 ρ hρ
    comp_jointly_surjective := @fun A hA i1 i2 ρ hρ => hcomp_surj A hA i1 i2 ρ hρ
    range_comp_ne := @fun A hA i1 i2 ρ hρ => hcomp_ne A hA i1 i2 ρ hρ
    comp_pi := @fun A hA i1 i2 ρ hρ => hcomp_pi A hA i1 i2 ρ hρ
    comp1_pi_place := @fun A hA i1 i2 ρ hρ => hc1pp A hA ρ hρ
    comp_w := @fun A hA i1 i2 ρ hρ => hcomp_w A hA i1 i2 ρ hρ
    pi_w_comp0_place := @fun A hA i1 i2 ρ hρ => hpiw A hA ρ hρ
    comp_dia := @fun A hA i1 i2 ρ hρ i d => hcomp_dia A hA i1 i2 ρ hρ d i
    εinf_mem_comp0 := @fun A hA i1 i2 ρ hρ =>
      (ModularCurve.XHDRLevel.range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective p M H hpM hpM2 hHp hj
        εinf εzero rhoInf (fun b => (hrho b).2) rfl π iota0 hiota0 hpichart θc htheta iotaInf hiotaInf hpichartInf A hA ρ hρ
        w hwover rfl (comp A hA i1 i2 ρ hρ) (hcomp_over A hA i1 i2 ρ hρ) (hcomp_ci A hA i1 i2 ρ hρ) (hcomp_surj A hA i1 i2 ρ hρ)
        (hcomp_pi A hA i1 i2 ρ hρ) (hcomp_w A hA i1 i2 ρ hρ)).1
    εzero_mem_comp1 := @fun A hA i1 i2 ρ hρ =>
      (ModularCurve.XHDRLevel.range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective p M H hpM hpM2 hHp hj
        εinf εzero rhoInf (fun b => (hrho b).2) rfl π iota0 hiota0 hpichart θc htheta iotaInf hiotaInf hpichartInf A hA ρ hρ
        w hwover rfl (comp A hA i1 i2 ρ hρ) (hcomp_over A hA i1 i2 ρ hρ) (hcomp_ci A hA i1 i2 ρ hρ) (hcomp_surj A hA i1 i2 ρ hρ)
        (hcomp_pi A hA i1 i2 ρ hρ) (hcomp_w A hA i1 i2 ρ hρ)).2.1

    crossing_reduced := @fun A hA i1 i2 ρ hρ =>
      isReduced_pullback_comp_pair_place p M H hpM hj w hwover θc hwchart π iota0 hpichart A hA ρ hρ
        (σ₀ A hA i1 i2 ρ hρ) (hσ₀ A hA i1 i2 ρ hρ)
        (ModularCurve.XHDRLevel.hfrob_place_of_retraction p M H hpM hpM2 hHp hj iota0 hiota0 θc htheta A hA ρ hρ
          (σ₀ A hA i1 i2 ρ hρ) (hσ₀ A hA i1 i2 ρ hρ))
        (comp A hA i1 i2 ρ hρ) (hcomp_pi A hA i1 i2 ρ hρ) (hcomp_w A hA i1 i2 ρ hρ)
        (fun c₀ h1 h2 c h3 h4 => (hcomp_chart A hA i1 i2 ρ hρ c₀ h1 h2 c h3 h4).1) (hZ A hA i1 i2 ρ hρ)
    nodeEquiv := @fun A hA i1 i2 ρ hρ => nodeEquiv A hA i1 i2 ρ hρ
    node_pin := @fun A hA i1 i2 ρ hρ => hnode A hA i1 i2 ρ hρ
  }

  have hread' : ∀ (b : ↥(chartAlgFin p (ΓM M H) hj)) (f : ↥(xHFunctionFieldBar M H)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((θc b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
    intro b f hf
    have hfb : f = ι b := Subtype.ext hf
    rw [hfb, hread b]
  refine ⟨𝔛, θ, θc, hθ, ?_, hwchart, hwpre, hread'⟩

  intro y y' h
  have pin : ∀ a : ↥(chartAlgFin p (ΓM M H) hj),
      𝔛.Meta.ffEquiv.symm
        (𝔛.Meta.C.germToFunctionField
          ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
          (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓM M H) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv a)))) = ι a :=
    fun a => Subtype.ext ((𝔛.Meta_pin a).trans (hι a).symm)
  have hwchart' : ιFin p (ΓM M H) hj ≫ 𝔛.w.hom = Spec.map (CommRingCat.ofHom θc.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj := hwchart
  have h1 := AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin
    (R p) (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
    ι ι 𝔛.Meta 𝔛.eeta 𝔛.heeta 𝔛.Meta_chart_nonempty pin 𝔛.Meta 𝔛.eeta 𝔛.heeta 𝔛.Meta_chart_nonempty pin
    𝔛.w.hom 𝔛.w_over (θc : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)) hwchart' θ.toAlgHom hread hint hfinAlong
    y' y (by simpa only [Category.assoc] using h.symm)
  rw [h1, AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul, smul_smul, ← map_mul, AlgEquiv.aut_mul,
    AlgEquiv.symm_trans_self, ← AlgEquiv.aut_one, map_one, one_smul]

example (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ∃ (𝔛 : XHDRModelAtP p M H hpM hj) (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)),

      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) ∧

      (∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) := by
  obtain ⟨𝔛, θ, -, hθ, hwgen, -, -, -⟩ := solution p M H hpM hpM2 hHp hj
  exact ⟨𝔛, θ, hθ, hwgen⟩

end

end S_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic_chart
end P2MW
export P2MW.S_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic_chart (solution)
