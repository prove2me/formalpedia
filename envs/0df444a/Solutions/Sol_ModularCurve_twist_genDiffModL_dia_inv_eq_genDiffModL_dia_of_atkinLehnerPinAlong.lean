-- Prove2me | solution 1 for ModularCurve.twist_genDiffModL_dia_inv_eq_genDiffModL_dia_of_atkinLehnerPinAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/fd40c506-b7f4-5118-b95c-83c49dfa4aa4

import Theorems.Thm_ModularCurve_IsInfReductionMap_comp_baseChange_genDia_eq_genDiffModL_comp
import Theorems.Thm_CuspForm_exists_not_dvd_and_coe_eq_smul_alSlash_diamond_and_mem_twoCuspIntegralSet_integralClosure
import Theorems.Thm_CuspForm_twoCuspLattice_integralClosure_eq_span_twoCuspIntegralSet_bot
import Theorems.Thm_ModularCurve_diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_twist_genDiffModL_dia_inv_eq_genDiffModL_dia_of_atkinLehnerPinAlong
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 CohCarrier.GammaHLower_finiteIndex"
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
p2m_attr_erase "simp" "Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

set_option autoImplicit false

namespace Ws47
namespace AL

p2m_open "ModularForm CuspForm ModularForm.CuspForm CongruenceSubgroup Matrix"
open scoped ModularForm

variable {M q : ℕ} [NeZero M]

theorem coprime_of_atkinLehnerDatum (W : AtkinLehnerDatum M q) : Nat.Coprime q W.R := by
  rw [← Nat.isCoprime_iff_coprime]
  exact ⟨W.a, -W.b, by linear_combination W.bezout⟩

def conjMat (W : AtkinLehnerDatum M q) (α β γ δ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a * (α - β * W.R) + W.b * ((M : ℤ) * γ) - W.b * W.R * δ,
      W.a * ((q : ℤ) * W.a * β - α * W.b) + W.b * (δ * W.a - W.R * γ * W.b);
    (q : ℤ) * W.R * (α - β * W.R - δ) + (q : ℤ) * ((M : ℤ) * γ),
      W.R * ((q : ℤ) * W.a * β - α * W.b) + (q : ℤ) * (δ * W.a - W.R * γ * W.b)]

theorem mat_mul_eq_conjMat_mul (W : AtkinLehnerDatum M q) (α β γ δ : ℤ) :
    W.mat * !![α, β; (M : ℤ) * γ, δ] = conjMat W α β γ δ * W.mat := by
  have hM : (M : ℤ) = (q : ℤ) * (W.R : ℤ) := W.hM_int
  have hb : (q : ℤ) * W.a - (W.R : ℤ) * W.b = 1 := W.bezout
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [AtkinLehnerDatum.mat, conjMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_fin_const, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;> rw [hM]
  · linear_combination (-((q : ℤ) * W.a * α + (q : ℤ) * W.b * W.R * γ)) * hb
  · linear_combination (-((q : ℤ) * W.a * β + W.b * δ)) * hb
  · linear_combination (-((q : ℤ) * W.R * α + (q : ℤ) ^ 2 * W.R * γ)) * hb
  · linear_combination (-((q : ℤ) * W.R * β + (q : ℤ) * δ)) * hb

end Ws47.AL

namespace Ws47
namespace AL

p2m_open "ModularForm CuspForm ModularForm.CuspForm CongruenceSubgroup Matrix"
open scoped ModularForm

variable {M q : ℕ} [NeZero M]

theorem exists_lowerLeft_eq (τ : Gamma0 M) : ∃ γ : ℤ, ((τ : SL(2, ℤ)) 1 0 : ℤ) = (M : ℤ) * γ := by
  have h : (((τ : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp τ.2
  obtain ⟨γ, hγ⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp h
  exact ⟨γ, hγ⟩

theorem coe_eq_of_lowerLeft (τ : Gamma0 M) (γ : ℤ) (hγ : ((τ : SL(2, ℤ)) 1 0 : ℤ) = (M : ℤ) * γ) :
    ((τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(τ : SL(2, ℤ)) 0 0, (τ : SL(2, ℤ)) 0 1; (M : ℤ) * γ, (τ : SL(2, ℤ)) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hγ]

noncomputable def conj (W : AtkinLehnerDatum M q) (τ : Gamma0 M) : Gamma0 M :=
  let γ := Classical.choose (exists_lowerLeft_eq τ)
  have hγ := Classical.choose_spec (exists_lowerLeft_eq τ)
  have hmul := mat_mul_eq_conjMat_mul W ((τ : SL(2, ℤ)) 0 0) ((τ : SL(2, ℤ)) 0 1) γ ((τ : SL(2, ℤ)) 1 1)
  have hdet : (conjMat W ((τ : SL(2, ℤ)) 0 0) ((τ : SL(2, ℤ)) 0 1) γ ((τ : SL(2, ℤ)) 1 1)).det = 1 := by
    have h := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_mul, AtkinLehnerDatum.det_mat, ← coe_eq_of_lowerLeft τ γ hγ,
      Matrix.SpecialLinearGroup.det_coe, mul_one] at h
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (W.q_pos (M := M)).ne'
    have h' : (conjMat W ((τ : SL(2, ℤ)) 0 0) ((τ : SL(2, ℤ)) 0 1) γ ((τ : SL(2, ℤ)) 1 1)).det * (q : ℤ) = 1 * (q : ℤ) := by
      rw [one_mul]; exact h.symm
    exact mul_right_cancel₀ hq0 h'
  ⟨⟨conjMat W ((τ : SL(2, ℤ)) 0 0) ((τ : SL(2, ℤ)) 0 1) γ ((τ : SL(2, ℤ)) 1 1), hdet⟩, by
    rw [Gamma0_mem]
    show (((conjMat W ((τ : SL(2, ℤ)) 0 0) ((τ : SL(2, ℤ)) 0 1) γ ((τ : SL(2, ℤ)) 1 1)) 1 0 : ℤ) : ZMod M) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨((τ : SL(2, ℤ)) 0 0 - (τ : SL(2, ℤ)) 0 1 * W.R - (τ : SL(2, ℤ)) 1 1) + (q : ℤ) * γ, ?_⟩
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_fin_const,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [W.hM_int]; ring⟩

theorem mat_mul_coe_eq_conj_mul (W : AtkinLehnerDatum M q) (τ : Gamma0 M) :
    W.mat * ((τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (((conj W τ : Gamma0 M) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * W.mat := by
  rw [coe_eq_of_lowerLeft τ _ (Classical.choose_spec (exists_lowerLeft_eq τ))]
  exact mat_mul_eq_conjMat_mul W _ _ _ _

theorem conj_apply_one_one (W : AtkinLehnerDatum M q) (τ : Gamma0 M) :
    (((conj W τ : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) =
      W.R * ((q : ℤ) * W.a * (τ : SL(2, ℤ)) 0 1 - (τ : SL(2, ℤ)) 0 0 * W.b) +
        (q : ℤ) * ((τ : SL(2, ℤ)) 1 1 * W.a - W.R * Classical.choose (exists_lowerLeft_eq τ) * W.b) := by
  show (conjMat W _ _ _ _) 1 1 = _
  simp [conjMat]

theorem det_entries (τ : Gamma0 M) :
    ((τ : SL(2, ℤ)) 0 0 : ℤ) * (τ : SL(2, ℤ)) 1 1 - (τ : SL(2, ℤ)) 0 1 * ((M : ℤ) * Classical.choose (exists_lowerLeft_eq τ)) = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe (τ : SL(2, ℤ))
  rw [Matrix.det_fin_two, Classical.choose_spec (exists_lowerLeft_eq τ)] at h
  linear_combination h

theorem q_dvd_conj_one_one_mul_sub_one (W : AtkinLehnerDatum M q) (τ : Gamma0 M) :
    (q : ℤ) ∣ (((conj W τ : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) * (τ : SL(2, ℤ)) 1 1 - 1 := by
  have hdet := det_entries τ
  have hb : (q : ℤ) * W.a - (W.R : ℤ) * W.b = 1 := W.bezout
  have hM : (M : ℤ) = (q : ℤ) * (W.R : ℤ) := W.hM_int
  rw [conj_apply_one_one]
  set γ := Classical.choose (exists_lowerLeft_eq τ)
  set α := ((τ : SL(2, ℤ)) 0 0 : ℤ); set β := ((τ : SL(2, ℤ)) 0 1 : ℤ); set δ := ((τ : SL(2, ℤ)) 1 1 : ℤ)
  have hdet' : α * δ - β * ((q : ℤ) * W.R * γ) = 1 := by rw [← hdet, hM]
  refine ⟨W.R * δ * β * W.a - W.R ^ 2 * W.b * β * γ + δ ^ 2 * W.a - W.R * γ * W.b * δ - W.a, ?_⟩
  linear_combination (-(W.R : ℤ) * W.b) * hdet' + hb

theorem R_dvd_conj_one_one_sub (W : AtkinLehnerDatum M q) (τ : Gamma0 M) :
    (W.R : ℤ) ∣ (((conj W τ : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) - (τ : SL(2, ℤ)) 1 1 := by
  have hb : (q : ℤ) * W.a - (W.R : ℤ) * W.b = 1 := W.bezout
  rw [conj_apply_one_one]
  set γ := Classical.choose (exists_lowerLeft_eq τ)
  set α := ((τ : SL(2, ℤ)) 0 0 : ℤ); set β := ((τ : SL(2, ℤ)) 0 1 : ℤ); set δ := ((τ : SL(2, ℤ)) 1 1 : ℤ)
  refine ⟨(q : ℤ) * W.a * β - α * W.b - (q : ℤ) * γ * W.b + δ * W.b, ?_⟩
  linear_combination δ * hb

theorem unitsMap_q_gamma0Units_conj_mul (W : AtkinLehnerDatum M q) (hqM : q ∣ M) (τ : Gamma0 M) :
    ZMod.unitsMap hqM (CohCarrier.gamma0Units M (conj W τ) * CohCarrier.gamma0Units M τ) = 1 := by
  apply Units.ext
  rw [map_mul, Units.val_mul, Units.val_one]
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units, Gamma0Map,
    MonoidHom.coe_mk, OneHom.coe_mk, ZMod.castHom_apply]
  rw [ZMod.cast_intCast hqM, ZMod.cast_intCast hqM]
  obtain ⟨w, hw⟩ := q_dvd_conj_one_one_mul_sub_one W τ
  have : ((((conj W τ : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) * (τ : SL(2, ℤ)) 1 1 : ℤ) = 1 + (q : ℤ) * w := by linear_combination hw
  rw [← Int.cast_mul, this]
  simp

theorem unitsMap_R_gamma0Units_conj (W : AtkinLehnerDatum M q) (hRM : W.R ∣ M) (τ : Gamma0 M) :
    ZMod.unitsMap hRM (CohCarrier.gamma0Units M (conj W τ)) = ZMod.unitsMap hRM (CohCarrier.gamma0Units M τ) := by
  apply Units.ext
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units, Gamma0Map,
    MonoidHom.coe_mk, OneHom.coe_mk, ZMod.castHom_apply]
  rw [ZMod.cast_intCast hRM, ZMod.cast_intCast hRM]
  obtain ⟨w, hw⟩ := R_dvd_conj_one_one_sub W τ
  have : ((((conj W τ : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ)) = (τ : SL(2, ℤ)) 1 1 + (W.R : ℤ) * w := by linear_combination hw
  rw [this]
  simp

end Ws47.AL

namespace Ws47
namespace AL

p2m_open "ModularForm CuspForm ModularForm.CuspForm CongruenceSubgroup Matrix"
open scoped ModularForm

variable {M q : ℕ} [NeZero M]

theorem eq_of_cast_eq_of_cast_eq (W : AtkinLehnerDatum M q) (hqM : q ∣ M) (hRM : W.R ∣ M) (x y : ZMod M)
    (h1 : (ZMod.castHom hqM (ZMod q)) x = (ZMod.castHom hqM (ZMod q)) y)
    (h2 : (ZMod.castHom hRM (ZMod W.R)) x = (ZMod.castHom hRM (ZMod W.R)) y) : x = y := by
  rw [← sub_eq_zero]
  set z := x - y with hz
  have h1' : (ZMod.castHom hqM (ZMod q)) z = 0 := by rw [hz, map_sub, h1, sub_self]
  have h2' : (ZMod.castHom hRM (ZMod W.R)) z = 0 := by rw [hz, map_sub, h2, sub_self]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at h1' h2'
  have hM : M = q * W.R := W.hM
  have hdvd : q * W.R ∣ z.val := (coprime_of_atkinLehnerDatum W).mul_dvd_of_dvd_of_dvd h1' h2'
  rw [← hM] at hdvd
  have := (ZMod.natCast_eq_zero_iff z.val M).mpr hdvd
  rwa [ZMod.natCast_zmod_val] at this

theorem units_eq_of_unitsMap_eq (W : AtkinLehnerDatum M q) (hqM : q ∣ M) (hRM : W.R ∣ M) (x y : (ZMod M)ˣ)
    (h1 : ZMod.unitsMap hqM x = ZMod.unitsMap hqM y) (h2 : ZMod.unitsMap hRM x = ZMod.unitsMap hRM y) : x = y := by
  apply Units.ext
  apply eq_of_cast_eq_of_cast_eq W hqM hRM
  · have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) h1
    simpa [ZMod.unitsMap_def] using this
  · have := congrArg (fun u : (ZMod W.R)ˣ => (u : ZMod W.R)) h2
    simpa [ZMod.unitsMap_def] using this

theorem exists_unitsMap_mul_eq_one_and_unitsMap_eq (W : AtkinLehnerDatum M q) (hqM : q ∣ M) (hRM : W.R ∣ M) (d : (ZMod M)ˣ) :
    ∃ d' : (ZMod M)ˣ, ZMod.unitsMap hqM (d' * d) = 1 ∧ ZMod.unitsMap hRM d' = ZMod.unitsMap hRM d := by

  refine ⟨(CohCarrier.gamma0Units M (conj W (gammaLift M d⁻¹)))⁻¹, ?_, ?_⟩
  · have h := unitsMap_q_gamma0Units_conj_mul W hqM (gammaLift M d⁻¹)
    rw [gamma0Units_gammaLift] at h

    have : (CohCarrier.gamma0Units M (conj W (gammaLift M d⁻¹)))⁻¹ * d = ((CohCarrier.gamma0Units M (conj W (gammaLift M d⁻¹))) * d⁻¹)⁻¹ := by
      rw [_root_.mul_inv_rev, inv_inv, mul_comm]
    rw [this, map_inv, h, inv_one]
  · have h := unitsMap_R_gamma0Units_conj W hRM (gammaLift M d⁻¹)
    rw [gamma0Units_gammaLift] at h
    rw [map_inv, h, map_inv, inv_inv]

theorem mapGL_mul_alGL_eq (W : AtkinLehnerDatum M q) (σ τ : SL(2, ℤ))
    (h : ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * W.mat = W.mat * ((τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * W.alGL = W.alGL * (Matrix.SpecialLinearGroup.mapGL ℝ τ : GL (Fin 2) ℝ) := by
  apply Units.ext
  have h' := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (Int.castRingHom ℝ)) h
  simp only [Matrix.map_mul] at h'
  exact h'

theorem alSlash_diamondLinH_eq_slash_gammaLift
    (M q : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (hD : CuspForm.StableD M H k)
    (W : ModularForm.AtkinLehnerDatum M q) (hqM : q ∣ M) (hRM : W.R ∣ M)
    (d d' : (ZMod M)ˣ) (hq : ZMod.unitsMap hqM (d' * d) = 1) (hR : ZMod.unitsMap hRM d' = ZMod.unitsMap hRM d)
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d f) =
      (ModularForm.alSlash W k ⇑f) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (CuspForm.gammaLift M d' : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by

  set C : Gamma0 M := conj W (gammaLift M d') with hC
  have hunits : CohCarrier.gamma0Units M (gammaLift M d) = CohCarrier.gamma0Units M C := by
    rw [gamma0Units_gammaLift]
    symm
    apply units_eq_of_unitsMap_eq W hqM hRM
    ·
      have h := unitsMap_q_gamma0Units_conj_mul W hqM (gammaLift M d')
      rw [gamma0Units_gammaLift] at h
      rw [map_mul] at h hq

      have e1 : ZMod.unitsMap hqM (CohCarrier.gamma0Units M C) = (ZMod.unitsMap hqM d')⁻¹ := eq_inv_of_mul_eq_one_left h
      have e2 : ZMod.unitsMap hqM d = (ZMod.unitsMap hqM d')⁻¹ := eq_inv_of_mul_eq_one_right hq
      rw [e1, e2]
    ·
      rw [unitsMap_R_gamma0Units_conj W hRM, gamma0Units_gammaLift, hR]

  have hγ := mul_inv_mem_GammaH_of_gamma0Units_eq (H := H) (gammaLift M d) C hunits

  have hCW : (((C : Gamma0 M) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * W.mat =
      W.mat * (((gammaLift M d' : Gamma0 M) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
    (mat_mul_coe_eq_conj_mul W (gammaLift M d')).symm
  have hGL := mapGL_mul_alGL_eq W _ _ hCW

  rw [coe_diamondLinH_apply k hD, ModularForm.alSlash, ModularForm.alSlash, ← SlashAction.slash_mul, ← SlashAction.slash_mul]
  have hsplit : ((Matrix.SpecialLinearGroup.mapGL ℝ ((gammaLift M d : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ)) * W.alGL =
      (Matrix.SpecialLinearGroup.mapGL ℝ (((gammaLift M d : Gamma0 M) : SL(2, ℤ)) * ((C : Gamma0 M) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) *
        (W.alGL * (Matrix.SpecialLinearGroup.mapGL ℝ ((gammaLift M d' : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
    rw [← hGL, ← mul_assoc, ← map_mul, inv_mul_cancel_right]
  rw [hsplit, SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)]

theorem alSlash_diamondLinH_diamondLinH_eq_slash_gammaLift
    (M q : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (hD : CuspForm.StableD M H k)
    (W : ModularForm.AtkinLehnerDatum M q) (hqM : q ∣ M) (hRM : W.R ∣ M)
    (d d' : (ZMod M)ˣ) (hq : ZMod.unitsMap hqM (d' * d) = 1) (hR : ZMod.unitsMap hRM d' = ZMod.unitsMap hRM d)
    (e : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k e (CuspForm.diamondLinH k d f)) =
      (ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k e f)) ∣[k]
        ((Matrix.SpecialLinearGroup.mapGL ℝ (CuspForm.gammaLift M d' : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by

  have hcomm : CuspForm.diamondLinH k e (CuspForm.diamondLinH k d f) = CuspForm.diamondLinH k d (CuspForm.diamondLinH k e f) := by
    apply DFunLike.coe_injective
    show ⇑(CuspForm.diamondLinH k e (CuspForm.diamondLinH k d f)) = ⇑(CuspForm.diamondLinH k d (CuspForm.diamondLinH k e f))
    rw [coe_diamondLinH_apply k hD, coe_diamondLinH_apply k hD, coe_diamondLinH_apply k hD, coe_diamondLinH_apply k hD,
      ← SlashAction.slash_mul, ← SlashAction.slash_mul, ← map_mul, ← map_mul]
    have hinv : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), (⇑f) ∣[k] γ = ⇑f := fun γ hγ =>
      SlashInvariantFormClass.slash_action_eq f γ hγ
    have h := slash_mapGL_eq_of_gamma0Units_eq (H := H) k hinv (gammaLift M d * gammaLift M e) (gammaLift M e * gammaLift M d)
      (by rw [map_mul, map_mul, mul_comm]) 1
    simpa using h
  rw [hcomm]
  exact alSlash_diamondLinH_eq_slash_gammaLift M q H k hD W hqM hRM d d' hq hR (CuspForm.diamondLinH k e f)

theorem alSlash_diamondLinH_eq_coe_diamondLinH
    (M q : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (hD : CuspForm.StableD M H k)
    (W : ModularForm.AtkinLehnerDatum M q) (hqM : q ∣ M) (hRM : W.R ∣ M)
    (d d' : (ZMod M)ˣ) (hq : ZMod.unitsMap hqM (d' * d) = 1) (hR : ZMod.unitsMap hRM d' = ZMod.unitsMap hRM d)
    (f G : CuspForm (CohCarrier.GammaH M H) k) (hG : (⇑G : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f) :
    ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d f) = ⇑(CuspForm.diamondLinH k d' G) := by
  rw [coe_diamondLinH_apply k hD d' G, hG]
  exact alSlash_diamondLinH_eq_slash_gammaLift M q H k hD W hqM hRM d d' hq hR f

end Ws47.AL

namespace Ws47
namespace C4

noncomputable def atkinLehnerDatum_of_not_sq_dvd (p M : ℕ) [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) :
    ModularForm.AtkinLehnerDatum M p where
  R := M / p
  hM := (Nat.mul_div_cancel' hpM).symm
  a := Nat.gcdA p (M / p)
  b := - Nat.gcdB p (M / p)
  bezout := by
    have hcop : Nat.Coprime p (M / p) := by
      refine (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr ?_
      intro h; apply hpM2
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by rw [pow_two, mul_assoc, ← hk, Nat.mul_div_cancel' hpM]⟩
    have h := Nat.gcd_eq_gcd_ab p (M / p)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at h
    linear_combination -h

theorem qCoeff_mem_of_mem_twoCuspIntegralSet
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (A : Subring ℂ) (g : CuspForm (CohCarrier.GammaH M H) 2) (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p A) (n : ℕ) :
    ModularFormClass.qCoeff (⇑g) n ∈ A := by
  have h := (hg 1 (CuspForm.heckeRingH M H 2).one_mem (atkinLehnerDatum_of_not_sq_dvd p M hpM hpM2) n).1
  simpa using h

theorem exists_map_eq_qExpansion
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (g : CuspForm (CohCarrier.GammaH M H) 2) (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (integralClosure ℤ ℂ).toSubring) :
    ∃ pg : PowerSeries ↥(integralClosure ℤ ℂ), pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ⇑g := by
  classical
  have hc : ∀ n, ModularFormClass.qCoeff (⇑g) n ∈ (integralClosure ℤ ℂ).toSubring :=
    qCoeff_mem_of_mem_twoCuspIntegralSet p M H hpM hpM2 _ g hg
  refine ⟨PowerSeries.mk (fun n => (⟨ModularFormClass.qCoeff (⇑g) n, hc n⟩ : ↥(integralClosure ℤ ℂ))), ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rfl

end Ws47.C4

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K] (S : Set ℕ)

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)

    (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)

    (W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) ≃ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hW :
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D)
          (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
          ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
            (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              HahnSeries.ofPowerSeries ℤ K (pfW.map φ))

    (hspan : Submodule.span K {ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D) (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) ∧
          ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)} = ⊤)
    :

      (∀ (d : (ZMod M)ˣ) (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d⁻¹) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) := by
  classical
  intro d

  set G : (ZMod M)ˣ → (Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) := fun c => ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia c) with hG

  have hpres : ∀ (c : (ZMod M)ˣ) (ξ : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), G c (ξ : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) ∈
      ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by
    intro c ξ
    have hξ : (ξ : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) ∈ LinearMap.range ρinf := by rw [hrange]; exact ξ.2
    obtain ⟨x, hx⟩ := hξ
    have h := LinearMap.congr_fun
      (ModularCurve.IsInfReductionMap.comp_baseChange_genDia_eq_genDiffModL_comp p M hpM hpM2 H hHp K S hρinf c) x
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    have hmem : G c (ξ : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) ∈ LinearMap.range ρinf := ⟨_, by rw [h, hx]⟩
    rwa [hrange] at hmem

  let G' : (ZMod M)ˣ → (↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) := fun c =>
    ((G c).comp (Submodule.subtype _)).codRestrict _ (fun ξ => hpres c ξ)
  have hG' : ∀ (c : (ZMod M)ˣ) (ξ : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((G' c ξ : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = G c (ξ : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) := fun c ξ => rfl

  let A : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] := (Submodule.subtype _).comp ((W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)).comp (G' d⁻¹))
  let B : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] := (G d).comp ((Submodule.subtype _).comp (W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)))
  suffices hAB : A = B by
    intro ω ω' hω'
    have hω'eq : ω' = G' d⁻¹ ω := Subtype.ext (by rw [hG']; exact hω')
    have h := LinearMap.congr_fun hAB ω
    simp only [A, B, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe] at h
    rw [hω'eq]
    exact h

  refine LinearMap.ext_on hspan ?_
  rintro ω ⟨f, hf, D, hD, pfW, hpfW, hω⟩
  simp only [A, B, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]

  set xf : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) := ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩ with hxf

  obtain ⟨D₀, hD₀, gW, hgW, hgWint⟩ :=
    CuspForm.exists_not_dvd_and_coe_eq_smul_alSlash_diamond_and_mem_twoCuspIntegralSet_integralClosure
      p M H hpM hpM2 hHp Wd e f hf

  have hgWspan : gW ∈ Submodule.span ↥(integralClosure ℤ ℂ).toSubring (CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) := by
    have h : gW ∈ (CuspForm.twoCuspLattice M H 2 p (integralClosure ℤ ℂ).toSubring : Set (CuspForm (CohCarrier.GammaH M H) 2)) :=
      CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p _ hgWint
    rw [CuspForm.twoCuspLattice_integralClosure_eq_span_twoCuspIntegralSet_bot p M hpM hpM2 H hHp] at h
    exact h
  obtain ⟨n, a, gs, hsum⟩ := Submodule.mem_span_set'.mp hgWspan
  let g : Fin n → CuspForm (CohCarrier.GammaH M H) 2 := fun i => (gs i : CuspForm (CohCarrier.GammaH M H) 2)
  have hg : ∀ i, g i ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := fun i => (gs i).2
  have hsum' : (∑ i, ((a i : ↥(integralClosure ℤ ℂ)) : ℂ) • g i) = gW := by
    rw [← hsum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (Subring.smul_def _ _).symm

  have hRM : Wd.R ∣ M := ⟨M / p, by rw [mul_comm]; exact Wd.hM⟩
  obtain ⟨ds, hds_q, hds_R⟩ := Ws47.AL.exists_unitsMap_mul_eq_one_and_unitsMap_eq Wd (Nat.div_dvd_of_dvd hpM) hRM d⁻¹

  set f' : CuspForm (CohCarrier.GammaH M H) 2 := CuspForm.diamondLinH 2 d⁻¹ f with hf'def
  have hf' : f' ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by
    have h := CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (CuspForm.heckeGenH_mem_heckeRingH S 2 (CohCarrier.Gen.dia d⁻¹)) hf
    rwa [CuspForm.heckeGenH_dia] at h
  have hω' : ((G' d⁻¹ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
      ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
        ⟨f', CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf'⟩) := by
    rw [hG', hω]
    have h := LinearMap.congr_fun
      (ModularCurve.IsInfReductionMap.comp_baseChange_genDia_eq_genDiffModL_comp p M hpM hpM2 H hHp K S hρinf d⁻¹)
      ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p xf)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul] at h
    rw [hG]
    show ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d⁻¹) (ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p xf)) = _
    rw [← h, CuspForm.intTwoCuspGenMod_reduce]
    congr 2
  have hD₀K : ((D₀ : ℕ) : K) ≠ 0 := by
    intro h0
    apply hD₀
    exact (CharP.cast_eq_zero_iff K p D₀).mp h0

  let x' : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p :=
    ∑ i, (φ (a i)) • ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
      ⟨g i, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (hg i)⟩)
  have hSD : CuspForm.StableD M H 2 := CuspForm.stableD M H 2
  have hΘinj := ModularCurve.diffQExp_qExpFunctionFieldC_injective K
    (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) (ModularCurve.translation_mem_GammaH _ _)

  have hρx' : ρinf x' = ∑ i, φ (a i) • ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
      ⟨g i, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (hg i)⟩) := by
    simp only [x', map_sum, map_smul]

  have hA : ((D₀ : ℕ) : K) • ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ρinf x' := by
    obtain ⟨pfW, hpfW⟩ := Ws47.C4.exists_map_eq_qExpansion p M H hpM hpM2 gW hgWint
    have hpin := hW f hf D₀ hD₀ pfW (by rw [hpfW, hgW]) ω hω
    have hLB := ModularCurve.diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
      p M H hpM hpM2 K ρinf hρinf φ a g hg pfW (by rw [hpfW, hsum'])
    apply hΘinj
    rw [LinearMap.map_smul_of_tower, hpin, ← hLB, hρx']

  have hB : ((D₀ : ℕ) : K) • ((W (G' d⁻¹ ω) : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
      ρinf ((CuspForm.intTwoCuspGenMod M H p S (CohCarrier.Gen.dia ds)).baseChange K x') := by

    set gW' : CuspForm (CohCarrier.GammaH M H) 2 := CuspForm.diamondLinH 2 ds gW with hgW'def
    have hgW'int : gW' ∈ CuspForm.twoCuspIntegralSet M H 2 p (integralClosure ℤ ℂ).toSubring := by
      have h := CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (CuspForm.heckeGenH_mem_heckeRingH S 2 (CohCarrier.Gen.dia ds)) hgWint
      rwa [CuspForm.heckeGenH_dia] at h
    have hgW' : (⇑gW' : UpperHalfPlane → ℂ) = (D₀ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f') := by
      rw [hgW'def, CuspForm.coe_diamondLinH_apply 2 hSD ds gW, hgW, hf'def,
        Ws47.AL.alSlash_diamondLinH_diamondLinH_eq_slash_gammaLift M (M / p) H 2 hSD Wd (Nat.div_dvd_of_dvd hpM) hRM d⁻¹ ds hds_q hds_R e f]
      exact ModularForm.SL_smul_slash 2 (CuspForm.gammaLift M ds : SL(2, ℤ)) _ (D₀ : ℂ)
    obtain ⟨pfW', hpfW'⟩ := Ws47.C4.exists_map_eq_qExpansion p M H hpM hpM2 gW' hgW'int
    have hpin' := hW f' hf' D₀ hD₀ pfW' (by rw [hpfW', hgW']) (G' d⁻¹ ω) hω'

    have hg' : ∀ i, CuspForm.diamondLinH 2 ds (g i) ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by
      intro i
      have h := CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (CuspForm.heckeGenH_mem_heckeRingH S 2 (CohCarrier.Gen.dia ds)) (hg i)
      rwa [CuspForm.heckeGenH_dia] at h
    have hsum'' : (∑ i, ((a i : ↥(integralClosure ℤ ℂ)) : ℂ) • CuspForm.diamondLinH 2 ds (g i)) = gW' := by
      rw [hgW'def, ← hsum', map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul]
    have hLB' := ModularCurve.diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
      p M H hpM hpM2 K ρinf hρinf φ a (fun i => CuspForm.diamondLinH 2 ds (g i)) hg' pfW' (by rw [hpfW', hsum''])

    have hbc : (CuspForm.intTwoCuspGenMod M H p S (CohCarrier.Gen.dia ds)).baseChange K x' =
        ∑ i, φ (a i) • ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨CuspForm.diamondLinH 2 ds (g i), CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (hg' i)⟩) := by
      simp only [x', map_sum, map_smul, LinearMap.baseChange_tmul, CuspForm.intTwoCuspGenMod_reduce]
      rfl
    have hρbc : ρinf ((CuspForm.intTwoCuspGenMod M H p S (CohCarrier.Gen.dia ds)).baseChange K x') =
        ∑ i, φ (a i) • ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨CuspForm.diamondLinH 2 ds (g i), CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (hg' i)⟩) := by
      rw [hbc, map_sum]
      simp only [map_smul]
    apply hΘinj
    rw [LinearMap.map_smul_of_tower, hpin', ← hLB', hρbc]

  have hred := LinearMap.congr_fun
    (ModularCurve.IsInfReductionMap.comp_baseChange_genDia_eq_genDiffModL_comp p M hpM hpM2 H hHp K S hρinf ds) x'
  simp only [LinearMap.coe_comp, Function.comp_apply] at hred
  have hGds : ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia ds) =
      ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d) := by
    simp only [ModularCurve.genDiffModL]
    congr 1

    have h := hds_q
    rw [map_mul, map_inv, mul_inv_eq_one] at h
    exact h

  apply smul_right_injective Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] hD₀K
  change ((D₀ : ℕ) : K) • ((W (G' d⁻¹ ω) : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
    ((D₀ : ℕ) : K) • ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
  rw [hB, hred, hGds, ← LinearMap.map_smul, hA]

end S_ModularCurve_twist_genDiffModL_dia_inv_eq_genDiffModL_dia_of_atkinLehnerPinAlong
end P2MW
export P2MW.S_ModularCurve_twist_genDiffModL_dia_inv_eq_genDiffModL_dia_of_atkinLehnerPinAlong (solution)
