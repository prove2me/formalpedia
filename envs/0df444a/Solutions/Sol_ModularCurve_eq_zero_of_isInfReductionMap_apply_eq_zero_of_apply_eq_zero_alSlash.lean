-- Prove2me | solution 1 for ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/cd5662ba-0308-53cd-bc11-e8419e42d363

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

import Theorems.Thm_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH
import Theorems.Thm_CuspForm_forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap
import Theorems.Thm_ModularForm_alSlash_eq_alSlash_of_gammaH
import Theorems.Thm_Submodule_baseChange_inf
import Theorems.Thm_CuspForm_exists_mem_twoCuspLattice_eq_smul_of_forall_qCoeff_eq_mul_of_forall_qCoeff_alSlash_eq_mul
import Theorems.Thm_ModularCurve_IsInfReductionMap_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq"
p2m_attr_erase "simp" "NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ"
p2m_attr_erase "simp" "ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one"
p2m_attr_erase "simp" "Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped ModularForm

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "infSubgroup IsInfReductionMap Gamma1_le_GammaH IsIntegralQExp intSeriesC qExpFunctionFieldC diffQExp mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH IsInfReductionMap.mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero"
namespace InjAux
p2m_open "ModularCurve"

def toZ (a : (⊥ : Subring ℂ)) : ℤ := (Subring.mem_bot.mp a.2).choose

theorem cast_toZ (a : (⊥ : Subring ℂ)) : ((toZ a : ℤ) : ℂ) = (a : ℂ) := (Subring.mem_bot.mp a.2).choose_spec

theorem toZ_add (a b : (⊥ : Subring ℂ)) : toZ (a + b) = toZ a + toZ b := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_add, cast_toZ, cast_toZ, cast_toZ, Subring.coe_add]

theorem toZ_mul (a b : (⊥ : Subring ℂ)) : toZ (a * b) = toZ a * toZ b := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_mul, cast_toZ, cast_toZ, cast_toZ, Subring.coe_mul]

theorem toZ_one : toZ 1 = 1 := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_toZ, Int.cast_one, Subring.coe_one]

theorem toZ_zero : toZ 0 = 0 := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_toZ, Int.cast_zero, Subring.coe_zero]

theorem toZ_natCast (n : ℕ) : toZ (n : (⊥ : Subring ℂ)) = n := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_toZ, Int.cast_natCast]; rfl

def toZHom : (⊥ : Subring ℂ) →+* ℤ where
  toFun := toZ
  map_one' := toZ_one
  map_mul' := toZ_mul
  map_zero' := toZ_zero
  map_add' := toZ_add

theorem smul_eq_toZ_zsmul {V : Type*} [AddCommGroup V] [Module ℂ V] (a : (⊥ : Subring ℂ)) (v : V) :
    a • v = toZ a • v := by
  rw [Subring.smul_def, ← cast_toZ, Int.cast_smul_eq_zsmul]

section Main

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)

local notation "Γ" => CohCarrier.GammaH M H
local notation "A" => (⊥ : Subring ℂ)
local notation "L" => CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)
local notation "Ω₀" => CuspForm.IntTwoCuspForms M H p

theorem Gamma1_le_GammaH : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro g hg
  rw [CongruenceSubgroup.Gamma1_mem] at hg
  obtain ⟨h00, h11, h10⟩ := hg
  have hg0 : g ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hg0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨g, hg0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have h1 : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    show (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 M)).strictPeriods
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples _
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  exact Subgroup.map_mono (Gamma1_le_GammaH M H) h1

theorem qExpansion_coe_add (f g : CuspForm Γ 2) :
    UpperHalfPlane.qExpansion 1 ⇑(f + g) = UpperHalfPlane.qExpansion 1 ⇑f + UpperHalfPlane.qExpansion 1 ⇑g :=
  ModularFormClass.qExpansion_add one_pos (one_mem_strictPeriods M H) f g

theorem qExpansion_coe_smul (c : ℂ) (f : CuspForm Γ 2) :
    UpperHalfPlane.qExpansion 1 ⇑(c • f) = c • UpperHalfPlane.qExpansion 1 ⇑f :=
  ModularFormClass.qExpansion_smul one_pos (one_mem_strictPeriods M H) c f

theorem qCoeff_add (f g : CuspForm Γ 2) (n : ℕ) :
    ModularFormClass.qCoeff ⇑(f + g) n = ModularFormClass.qCoeff ⇑f n + ModularFormClass.qCoeff ⇑g n := by
  show PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑(f + g)) = _
  rw [qExpansion_coe_add, map_add]; rfl

theorem qCoeff_smul (c : ℂ) (f : CuspForm Γ 2) (n : ℕ) :
    ModularFormClass.qCoeff ⇑(c • f) n = c * ModularFormClass.qCoeff ⇑f n := by
  show PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑(c • f)) = _
  rw [qExpansion_coe_smul, map_smul, smul_eq_mul]; rfl

omit [Fact p.Prime] in
theorem qCoeff_zero' (n : ℕ) : ModularFormClass.qCoeff ⇑(0 : CuspForm Γ 2) n = 0 := by
  show PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑(0 : CuspForm Γ 2)) = 0
  rw [CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]

variable (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ)

include hHp in
omit [Fact p.Prime] in

theorem exists_Xf (hp : p.Prime) (F : CuspForm Γ 2) :
    ∃ X : CuspForm Γ 2, ⇑X = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e F) := by
  have hHp' : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H := by
    obtain ⟨R, hM, a, b, bez⟩ := W
    have hR : R = M / p := by
      subst hM
      exact (Nat.mul_div_cancel_left R hp.pos).symm
    subst hR
    exact hHp
  exact CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHp' 2 (CuspForm.diamondLinH 2 e F)

def Xf (F : CuspForm Γ 2) : CuspForm Γ 2 := (exists_Xf p M hpM H hHp W e Fact.out F).choose

theorem coe_Xf (F : CuspForm Γ 2) : ⇑(Xf p M hpM H hHp W e F) = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e F) :=
  (exists_Xf p M hpM H hHp W e Fact.out F).choose_spec

theorem Xf_add (F G : CuspForm Γ 2) : Xf p M hpM H hHp W e (F + G) = Xf p M hpM H hHp W e F + Xf p M hpM H hHp W e G := by
  apply DFunLike.ext'
  rw [CuspForm.coe_add, coe_Xf, coe_Xf, coe_Xf, map_add, CuspForm.coe_add, ModularForm.alSlash_add]

theorem Xf_smul (c : ℂ) (F : CuspForm Γ 2) : Xf p M hpM H hHp W e (c • F) = c • Xf p M hpM H hHp W e F := by
  apply DFunLike.ext'
  have h1 : ⇑(c • Xf p M hpM H hHp W e F) = c • ⇑(Xf p M hpM H hHp W e F) := by
    funext z; rfl
  have h2 : ⇑(c • CuspForm.diamondLinH 2 e F) = c • ⇑(CuspForm.diamondLinH 2 e F) := by
    funext z; rfl
  rw [h1, coe_Xf, coe_Xf, map_smul, h2, ModularForm.alSlash_smul]

theorem Xf_zsmul (n : ℤ) (F : CuspForm Γ 2) : Xf p M hpM H hHp W e (n • F) = n • Xf p M hpM H hHp W e F := by
  rw [← Int.cast_smul_eq_zsmul ℂ n F, Xf_smul, Int.cast_smul_eq_zsmul]

theorem Xf_zero : Xf p M hpM H hHp W e 0 = 0 := by
  have h := Xf_smul p M hpM H hHp W e 0 0
  rwa [zero_smul, zero_smul] at h

theorem diamondLinH_inv_apply (d : (ZMod M)ˣ) (F : CuspForm Γ 2) :
    CuspForm.diamondLinH 2 d⁻¹ (CuspForm.diamondLinH 2 d F) = F := by
  have hD := CuspForm.stableD M H 2
  apply DFunLike.ext'
  rw [CuspForm.coe_diamondLinH_apply 2 hD, CuspForm.coe_diamondLinH_apply 2 hD, ← SlashAction.slash_mul, ← map_mul]
  apply SlashInvariantForm.slash_action_eqn
  apply Subgroup.mem_map_of_mem
  rw [← Subgroup.coe_mul]
  refine CohCarrier.mem_GammaH_iff.mpr ⟨(CuspForm.gammaLift M d * CuspForm.gammaLift M d⁻¹).2, ?_⟩
  have h1 : CohCarrier.gamma0Units M (CuspForm.gammaLift M d * CuspForm.gammaLift M d⁻¹) = 1 := by
    rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift, mul_inv_cancel]
  rw [Subtype.coe_eta, h1]
  exact one_mem H

def Pinf (F : CuspForm Γ 2) : Prop := ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff ⇑F n = (p : ℂ) * m

def PW (F : CuspForm Γ 2) : Prop :=
  ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e F)) n = (p : ℂ) * m

theorem PW_iff (F : CuspForm Γ 2) :
    PW p M H W e F ↔ ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff ⇑(Xf p M hpM H hHp W e F) n = (p : ℂ) * m := by
  unfold PW; rw [coe_Xf]

theorem Pinf_zero : Pinf p M H 0 := fun n => ⟨0, by rw [qCoeff_zero']; simp⟩

theorem Pinf_add {F G : CuspForm Γ 2} (hF : Pinf p M H F) (hG : Pinf p M H G) : Pinf p M H (F + G) := by
  intro n
  obtain ⟨a, ha⟩ := hF n
  obtain ⟨b, hb⟩ := hG n
  exact ⟨a + b, by rw [qCoeff_add, ha, hb]; push_cast; ring⟩

theorem Pinf_zsmul {F : CuspForm Γ 2} (hF : Pinf p M H F) (k : ℤ) : Pinf p M H (k • F) := by
  intro n
  obtain ⟨a, ha⟩ := hF n
  exact ⟨k * a, by rw [← Int.cast_smul_eq_zsmul ℂ k F, qCoeff_smul, ha]; push_cast; ring⟩

include hpM hHp in
theorem PW_zero : PW p M H W e 0 := by
  rw [PW_iff p M hpM H hHp W e, Xf_zero]; exact fun n => ⟨0, by rw [qCoeff_zero']; simp⟩

include hpM hHp in
theorem PW_add {F G : CuspForm Γ 2} (hF : PW p M H W e F) (hG : PW p M H W e G) :
    PW p M H W e (F + G) := by
  rw [PW_iff p M hpM H hHp W e] at hF hG ⊢
  intro n
  obtain ⟨a, ha⟩ := hF n
  obtain ⟨b, hb⟩ := hG n
  exact ⟨a + b, by rw [Xf_add, qCoeff_add, ha, hb]; push_cast; ring⟩

include hpM hHp in
theorem PW_zsmul {F : CuspForm Γ 2} (hF : PW p M H W e F) (k : ℤ) : PW p M H W e (k • F) := by
  rw [PW_iff p M hpM H hHp W e] at hF ⊢
  intro n
  obtain ⟨a, ha⟩ := hF n
  exact ⟨k * a, by rw [Xf_zsmul, ← Int.cast_smul_eq_zsmul ℂ k, qCoeff_smul, ha]; push_cast; ring⟩

theorem exists_int_qCoeff_Xf (w : CuspForm Γ 2) (hw : w ∈ L) (n : ℕ) :
    ∃ k : ℤ, ModularFormClass.qCoeff ⇑(Xf p M hpM H hHp W e w) n = k := by
  induction hw using Submodule.span_induction with
  | mem f hfS =>
    have h := ((CuspForm.mem_twoCuspIntegralSet_iff f).mp hfS) (CuspForm.diamondLinH 2 e)
      (CuspForm.heckeGenH_mem_heckeRingH (∅ : Set ℕ) 2 (CohCarrier.Gen.dia e)) W n
    rw [coe_Xf]
    exact ⟨toZ ⟨_, h.2⟩, by rw [cast_toZ]⟩
  | zero => exact ⟨0, by rw [Xf_zero, qCoeff_zero']; simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a + b, by rw [Xf_add, qCoeff_add, ha, hb]; push_cast; ring⟩
  | smul a f _ hf =>
    obtain ⟨b, hb⟩ := hf
    refine ⟨toZ a * b, ?_⟩
    rw [smul_eq_toZ_zsmul, Xf_zsmul, ← Int.cast_smul_eq_zsmul ℂ, qCoeff_smul, hb]; push_cast; ring

include hpM hHp in

theorem PW_of_mem_smul (w : L) : PW p M H W e ((((p : A) • w : L) : CuspForm Γ 2)) := by
  rw [PW_iff p M hpM H hHp W e]
  intro n
  obtain ⟨k, hk⟩ := exists_int_qCoeff_Xf p M hpM H hHp W e (w : CuspForm Γ 2) w.2 n
  refine ⟨k, ?_⟩
  rw [Submodule.coe_smul, smul_eq_toZ_zsmul, toZ_natCast, Xf_zsmul, ← Int.cast_smul_eq_zsmul ℂ, qCoeff_smul, hk]
  push_cast; ring

theorem exists_of_mem_span {P : CuspForm Γ 2 → Prop} (hP0 : P 0) (hPadd : ∀ {F G}, P F → P G → P (F + G))
    (hPsmul : ∀ {F} (k : ℤ), P F → P (k • F))
    {c : Ω₀} (hc : c ∈ Submodule.span (ZMod p) {c : Ω₀ | ∃ y : L, P (y : CuspForm Γ 2) ∧ c = CuspForm.intTwoCuspReduce M H p y}) :
    ∃ y : L, P (y : CuspForm Γ 2) ∧ c = CuspForm.intTwoCuspReduce M H p y := by
  induction hc using Submodule.span_induction with
  | mem c hcS => exact hcS
  | zero => exact ⟨0, by simpa using hP0, by rw [map_zero]⟩
  | add c c' _ _ hc hc' =>
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨y', hy', rfl⟩ := hc'
    exact ⟨y + y', by simpa using hPadd hy hy', by rw [map_add]⟩
  | smul r c _ hc =>
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨k • y, ?_, ?_⟩
    · have : ((k • y : L) : CuspForm Γ 2) = k • (y : CuspForm Γ 2) := by rw [Submodule.coe_smul_of_tower]
      rw [this]; exact hPsmul k hy
    · rw [Int.cast_smul_eq_zsmul, map_zsmul]

end Main

end ModularCurve.InjAux

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash.ModularCurve ModularCurve.InjAux in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (W : ModularForm.AtkinLehnerDatum M p)
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (ρinf ρzero : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hzero : (∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (pfW : PowerSeries ℤ), ModularCurve.IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW →
            ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
                (ρzero ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) =
              ModularCurve.intSeriesC K pfW))
    (x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p) (hx : ρinf x = 0) (hx' : ρzero x = 0) : x = 0 := by
  classical

  have hp : p.Prime := Fact.out

  have h1 := ModularCurve.IsInfReductionMap.mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero p M hpM H W K hinf x hx
  have h2 := ModularCurve.mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH
    p M hpM H hHp W e K hzero x hx'

  let Sinf : Set (CuspForm.IntTwoCuspForms M H p) := {c | ∃ y : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)),
    Pinf p M H (y : CuspForm (CohCarrier.GammaH M H) 2) ∧ c = CuspForm.intTwoCuspReduce M H p y}
  let SW : Set (CuspForm.IntTwoCuspForms M H p) := {c | ∃ y : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)),
    PW p M H W e (y : CuspForm (CohCarrier.GammaH M H) 2) ∧ c = CuspForm.intTwoCuspReduce M H p y}
  have hS1 : {z : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p |
      ∃ y : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)),
        (∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑(y : CuspForm (CohCarrier.GammaH M H) 2)) n = (p : ℂ) * m) ∧
        z = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y} = (TensorProduct.mk (ZMod p) K _ 1) '' Sinf := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image, TensorProduct.mk_apply, Sinf, Pinf]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨c, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩
  have hS2 : {z : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p |
      ∃ y : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)),
        (∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff
            (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e (y : CuspForm (CohCarrier.GammaH M H) 2))) n = (p : ℂ) * m) ∧
        z = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y} = (TensorProduct.mk (ZMod p) K _ 1) '' SW := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image, TensorProduct.mk_apply, SW, PW]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨c, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩
  rw [hS1, ← Submodule.baseChange_span] at h1
  rw [hS2, ← Submodule.baseChange_span] at h2

  have h12 : x ∈ (Submodule.span (ZMod p) Sinf ⊓ Submodule.span (ZMod p) SW).baseChange K := by
    rw [Submodule.baseChange_inf]; exact ⟨h1, h2⟩

  have hbot : Submodule.span (ZMod p) Sinf ⊓ Submodule.span (ZMod p) SW = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_bot]
    obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.mp hc
    obtain ⟨y₁, hy₁, rfl⟩ := exists_of_mem_span p M H (P := Pinf p M H) (Pinf_zero p M H)
      (fun hF hG => Pinf_add p M H hF hG) (fun k hF => Pinf_zsmul p M H hF k) hc1
    obtain ⟨y₂, hy₂, hy12⟩ := exists_of_mem_span p M H (P := PW p M H W e) (PW_zero p M hpM H hHp W e)
      (fun hF hG => PW_add p M hpM H hHp W e hF hG) (fun k hF => PW_zsmul p M hpM H hHp W e hF k) hc2

    have hdiff : y₁ - y₂ ∈ (CuspForm.intIdeal p • ⊤ : Submodule (⊥ : Subring ℂ) ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ))) := by
      rw [← CuspForm.twoCuspReduce_eq_zero_iff]
      have : CuspForm.intTwoCuspReduce M H p (y₁ - y₂) = 0 := by rw [map_sub, ← hy12, sub_self]
      exact this
    rw [CuspForm.intIdeal, Submodule.ideal_span_singleton_smul] at hdiff
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hdiff
    have hy1W : PW p M H W e (y₁ : CuspForm (CohCarrier.GammaH M H) 2) := by
      have heq : (y₁ : CuspForm (CohCarrier.GammaH M H) 2) =
          (y₂ : CuspForm (CohCarrier.GammaH M H) 2) + ((((p : (⊥ : Subring ℂ)) • w :
            ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ))) : CuspForm (CohCarrier.GammaH M H) 2)) := by
        rw [hw, Submodule.coe_sub, add_sub_cancel]
      rw [heq]
      exact PW_add p M hpM H hHp W e hy₂ (PW_of_mem_smul p M hpM H hHp W e w)

    have hzL : CuspForm.diamondLinH 2 e (y₁ : CuspForm (CohCarrier.GammaH M H) 2) ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) :=
      CuspForm.heckeRingH_apply_mem_twoCuspLattice (CuspForm.heckeGenH_mem_heckeRingH (∅ : Set ℕ) 2 (CohCarrier.Gen.dia e)) y₁.2
    have hzinf := CuspForm.forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap
      p M hpM hpM2 H hHp K W e he ⟨ρinf, hinf⟩ e (y₁ : CuspForm (CohCarrier.GammaH M H) 2) y₁.2 hy₁
    have hzW : ∀ (W' : ModularForm.AtkinLehnerDatum M p) (n : ℕ), ∃ m : ℤ,
        ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(CuspForm.diamondLinH 2 e (y₁ : CuspForm (CohCarrier.GammaH M H) 2))) n = (p : ℂ) * m := by
      intro W' n
      rw [ModularForm.alSlash_eq_alSlash_of_gammaH M p H 2 W W']
      exact hy1W n
    obtain ⟨z', hz'L, hz'⟩ := CuspForm.exists_mem_twoCuspLattice_eq_smul_of_forall_qCoeff_eq_mul_of_forall_qCoeff_alSlash_eq_mul
      M p hpM hpM2 H hHp _ hzL hzinf hzW

    have hmem' : CuspForm.diamondLinH 2 e⁻¹ z' ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) :=
      CuspForm.heckeRingH_apply_mem_twoCuspLattice (CuspForm.heckeGenH_mem_heckeRingH (∅ : Set ℕ) 2 (CohCarrier.Gen.dia e⁻¹)) hz'L
    have hy1eq : y₁ = (p : (⊥ : Subring ℂ)) • (⟨_, hmem'⟩ : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ))) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Subring.smul_def, ← diamondLinH_inv_apply M H e (y₁ : CuspForm (CohCarrier.GammaH M H) 2), hz',
        map_smul]
      rfl
    rw [hy1eq, CuspForm.intTwoCuspReduce_apply]
    show CuspForm.twoCuspReduce (CuspForm.intIdeal p) _ = 0
    rw [CuspForm.twoCuspReduce_eq_zero_iff]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  rw [hbot, Submodule.baseChange_bot] at h12
  exact (Submodule.mem_bot K).mp h12

end S_ModularCurve_eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash (solution)
