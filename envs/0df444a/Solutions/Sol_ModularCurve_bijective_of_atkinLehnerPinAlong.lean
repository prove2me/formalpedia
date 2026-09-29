-- Prove2me | solution 1 for ModularCurve.bijective_of_atkinLehnerPinAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7706f735-d7bf-5fae-93c0-edd849b44367

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_CuspForm_exists_not_dvd_and_coe_eq_smul_alSlash_diamond_and_mem_twoCuspIntegralSet_integralClosure
import Theorems.Thm_CuspForm_twoCuspLattice_integralClosure_eq_span_twoCuspIntegralSet_bot
import Theorems.Thm_ModularCurve_diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
import Theorems.Thm_ModularCurve_span_ssPolarDifferentials_atkinLehnerPinned_eq_top
import Theorems.Thm_ModularCurve_IsInfReductionMap_comp_baseChange_genDia_eq_genDiffModL_comp
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_bijective_of_atkinLehnerPinAlong
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.GammaHLower_finiteIndex ModularCurve.instIsElliptic_tateLaurent GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin"
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"
p2m_attr_erase "simp" "CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun"
p2m_attr_erase "simp" "KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CuspForm.coe_atkinLehnerLin_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single"
p2m_attr_erase "simp" "ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups ModularForm
open CongruenceSubgroup

namespace TW2K2

def alConjMat {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (A B c D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a * A + W.b * q * W.R * c - q * W.a * W.R * B - W.b * W.R * D,
     -(W.a * W.b * A) - W.b ^ 2 * W.R * c + q * W.a ^ 2 * B + W.a * W.b * D;
     (q : ℤ) * W.R * (A + q * c - W.R * B - D),
     -(W.R * W.b * A) - q * W.R * W.b * c + q * W.R * W.a * B + q * W.a * D]

theorem det_alConjMat {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (A B c D C : ℤ)
    (hdet : A * D - B * C = 1) (hC : C = q * W.R * c) : (alConjMat W A B c D).det = 1 := by
  have hb := W.bezout
  rw [alConjMat, Matrix.det_fin_two_of]
  linear_combination (-A*D*W.R*W.b + A*D*W.a*q + A*D + B*W.R^2*W.b*c*q - B*W.R*W.a*c*q^2 - B*W.R*c*q) * hb
    + hdet + B * hC

theorem exists_apply_10_eq {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (γ : Gamma0 M) :
    ∃ c : ℤ, ((γ : SL(2, ℤ)) 1 0 : ℤ) = q * W.R * c := by
  have h := Gamma0_mem.mp γ.2
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp h
  exact ⟨c, by rw [hc, W.hM_int]⟩

def alConj {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (σ : Gamma0 M) (c : ℤ)
    (hc : ((σ : SL(2, ℤ)) 1 0 : ℤ) = q * W.R * c) : Gamma0 M :=
  ⟨⟨alConjMat W ((σ : SL(2, ℤ)) 0 0) ((σ : SL(2, ℤ)) 0 1) c ((σ : SL(2, ℤ)) 1 1),
    det_alConjMat W _ _ c _ ((σ : SL(2, ℤ)) 1 0) (by
      have := Matrix.det_fin_two (σ : SL(2, ℤ)).1
      rw [Matrix.SpecialLinearGroup.det_coe] at this
      linear_combination -this) hc⟩, by
    rw [Gamma0_mem]
    show (((q : ℤ) * W.R * (((σ : SL(2, ℤ)) 0 0) + q * c - W.R * ((σ : SL(2, ℤ)) 0 1) - ((σ : SL(2, ℤ)) 1 1)) : ℤ) :
      ZMod M) = 0
    rw [← W.hM_int]; push_cast; simp⟩

theorem mapGL_alConj_mul_alGL {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (σ : Gamma0 M) (c : ℤ)
    (hc : ((σ : SL(2, ℤ)) 1 0 : ℤ) = q * W.R * c) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ((alConj W σ c hc : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) * W.alGL =
      W.alGL * (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  have hb : (q : ℝ) * (W.a : ℝ) - (W.R : ℝ) * (W.b : ℝ) = 1 := by exact_mod_cast W.bezout
  have hcR : ((((σ : SL(2, ℤ)) 1 0 : ℤ)) : ℝ) = (q : ℝ) * (W.R : ℝ) * (c : ℝ) := by exact_mod_cast hc
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alConj, alConjMat, ModularForm.AtkinLehnerDatum.mat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (((σ : SL(2, ℤ)) 0 0 : ℝ) * W.a * q + (W.R : ℝ) * W.b * c * q) * hb + (-(W.b : ℝ)) * hcR
  · linear_combination (((σ : SL(2, ℤ)) 0 1 : ℝ) * W.a * q + ((σ : SL(2, ℤ)) 1 1 : ℝ) * W.b) * hb
  · linear_combination (((σ : SL(2, ℤ)) 0 0 : ℝ) * W.R * q + (W.R : ℝ) * c * q ^ 2) * hb + (-(q : ℝ)) * hcR
  · linear_combination (((σ : SL(2, ℤ)) 0 1 : ℝ) * W.R * q + ((σ : SL(2, ℤ)) 1 1 : ℝ) * q) * hb

theorem exists_forall_dia_alSlash {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ)
    (k : ℤ) (d : (ZMod M)ˣ) :
    ∃ d' : (ZMod M)ˣ, ∀ (F X : CuspForm (CohCarrier.GammaH M H) k),
      (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑F →
      (⇑(CuspForm.diamondLinH k d X) : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d' F) := by
  have hD : CuspForm.StableD M H k := CuspForm.stableD M H k
  obtain ⟨c, hc⟩ := exists_apply_10_eq W (CuspForm.gammaLift M d)
  refine ⟨CohCarrier.gamma0Units M (alConj W (CuspForm.gammaLift M d) c hc), fun F X hX => ?_⟩
  rw [CuspForm.coe_diamondLinH_apply k hD d X, hX,
    CuspForm.coe_diamondLinH_eq_slash k hD _ (alConj W (CuspForm.gammaLift M d) c hc) rfl F,
    ModularForm.alSlash_def, ModularForm.alSlash_def, ← SlashAction.slash_mul, ← SlashAction.slash_mul,
    mapGL_alConj_mul_alGL]

theorem slash_two_scalar (u : ℝˣ) (f : UpperHalfPlane → ℂ) :
    f ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) ℝ) = f := by
  ext τ
  have hu : (u : ℝ) ≠ 0 := u.ne_zero
  have hdet : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) u) : ℝˣ) : ℝ) = (u : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.det_scalar]; simp
  have hσ : UpperHalfPlane.σ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = ContinuousAlgEquiv.refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos]
    show 0 < ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) u) : ℝˣ) : ℝ)
    rw [hdet]; positivity
  rw [ModularForm.slash_apply, UpperHalfPlane.denom_scalar, UpperHalfPlane.glScalar_smul, hσ, hdet]
  simp only [ContinuousAlgEquiv.refl_apply, abs_pow, sq_abs]
  have hu' : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu
  rw [show (2 : ℤ) - 1 = 1 from rfl, zpow_one, zpow_neg, zpow_two]
  push_cast
  field_simp

theorem alGL_mul_alGL {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) :
    W.alGL * W.alGL = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (q : ℝ) (by exact_mod_cast W.q_pos.ne')) *
      (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularForm.AtkinLehnerDatum.mat, ModularForm.AtkinLehnerDatum.sqUnitSL, ModularForm.AtkinLehnerDatum.sqUnit,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.natCast_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] <;> ring

theorem exists_forall_alSlash_alSlash_two {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ) :
    ∃ δ : (ZMod M)ˣ, ∀ F : CuspForm (CohCarrier.GammaH M H) 2,
      ModularForm.alSlash W 2 (ModularForm.alSlash W 2 ⇑F) = ⇑(CuspForm.diamondLinH 2 δ F) := by
  have hD : CuspForm.StableD M H 2 := CuspForm.stableD M H 2
  refine ⟨CohCarrier.gamma0Units M ⟨W.sqUnitSL, W.sqUnitSL_mem⟩, fun F => ?_⟩
  rw [ModularForm.alSlash_def, ModularForm.alSlash_def, ← SlashAction.slash_mul, alGL_mul_alGL, SlashAction.slash_mul,
    slash_two_scalar, CuspForm.coe_diamondLinH_eq_slash 2 hD _ ⟨W.sqUnitSL, W.sqUnitSL_mem⟩ rfl F]

theorem gammaLift_mem_GammaH_of_mem {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {u : (ZMod M)ˣ} (hu : u ∈ H) :
    ((CuspForm.gammaLift M u : Gamma0 M) : SL(2, ℤ)) ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  exact ⟨(CuspForm.gammaLift M u).2, by
    rw [show (⟨((CuspForm.gammaLift M u : Gamma0 M) : SL(2, ℤ)), (CuspForm.gammaLift M u).2⟩ : Gamma0 M) =
      CuspForm.gammaLift M u from rfl, CuspForm.gamma0Units_gammaLift]; exact hu⟩

theorem diamondLinH_of_mem {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (k : ℤ) {u : (ZMod M)ˣ} (hu : u ∈ H)
    (g : CuspForm (CohCarrier.GammaH M H) k) : CuspForm.diamondLinH k u g = g := by
  refine DFunLike.ext' ?_
  rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD M H k)]
  exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ (gammaLift_mem_GammaH_of_mem hu))

theorem diamondLinH_diamondLinH {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (k : ℤ) (d e : (ZMod M)ˣ)
    (g : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm.diamondLinH k d (CuspForm.diamondLinH k e g) = CuspForm.diamondLinH k (e * d) g := by
  have hD := CuspForm.stableD M H k
  refine DFunLike.ext' ?_
  rw [CuspForm.coe_diamondLinH_apply k hD d, CuspForm.coe_diamondLinH_apply k hD e, ← SlashAction.slash_mul,
    ← map_mul]
  have : ((CuspForm.gammaLift M e : Gamma0 M) : SL(2, ℤ)) * ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)) =
      ((CuspForm.gammaLift M e * CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)) := rfl
  rw [this, CuspForm.coe_diamondLinH_eq_slash k hD (e * d) (CuspForm.gammaLift M e * CuspForm.gammaLift M d)
    (by rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift])]

theorem diamondLinH_inv_diamondLinH {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (k : ℤ) (d : (ZMod M)ˣ)
    (g : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm.diamondLinH k d⁻¹ (CuspForm.diamondLinH k d g) = g := by
  rw [diamondLinH_diamondLinH, mul_inv_cancel]
  exact diamondLinH_of_mem k (one_mem H) g

theorem diamondLinH_diamondLinH_inv {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (k : ℤ) (d : (ZMod M)ˣ)
    (g : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm.diamondLinH k d (CuspForm.diamondLinH k d⁻¹ g) = g := by
  rw [diamondLinH_diamondLinH, inv_mul_cancel]
  exact diamondLinH_of_mem k (one_mem H) g

theorem one_mem_strictPeriods_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CohCarrier.GammaH M H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

theorem qExpansion_coe_smul {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} (a : ℂ)
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    UpperHalfPlane.qExpansion 1 (⇑(a • f)) = a • UpperHalfPlane.qExpansion 1 ⇑f := by
  have hcoe : (⇑(a • f) : UpperHalfPlane → ℂ) = a • ⇑f := rfl
  rw [hcoe]
  exact UpperHalfPlane.qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_GammaH M H)) a

theorem qExpansion_coe_add {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}
    (f g : CuspForm (CohCarrier.GammaH M H) k) :
    UpperHalfPlane.qExpansion 1 (⇑(f + g)) = UpperHalfPlane.qExpansion 1 ⇑f + UpperHalfPlane.qExpansion 1 ⇑g := by
  have hcoe : (⇑(f + g) : UpperHalfPlane → ℂ) = ⇑f + ⇑g := rfl
  rw [hcoe]
  exact UpperHalfPlane.qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_GammaH M H))
    (ModularFormClass.analyticAt_cuspFunction_zero g one_pos (one_mem_strictPeriods_GammaH M H))

theorem qExpansion_coe_sum_smul {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (f : ι → CuspForm (CohCarrier.GammaH M H) k) :
    UpperHalfPlane.qExpansion 1 (⇑(∑ i ∈ s, a i • f i)) = ∑ i ∈ s, a i • UpperHalfPlane.qExpansion 1 ⇑(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have : (⇑(0 : CuspForm (CohCarrier.GammaH M H) k) : UpperHalfPlane → ℂ) = 0 := rfl
    rw [this, UpperHalfPlane.qExpansion_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, qExpansion_coe_add, qExpansion_coe_smul, ih]

theorem coe_sum_smul {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (f : ι → CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(∑ i ∈ s, a i • f i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, a i • (⇑(f i) : UpperHalfPlane → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

noncomputable def alDatumP {p M : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) :
    ModularForm.AtkinLehnerDatum M p where
  R := M / p
  hM := (Nat.mul_div_cancel' hpM).symm
  a := Nat.gcdA p (M / p)
  b := -Nat.gcdB p (M / p)
  bezout := by
    have hcop : Nat.Coprime p (M / p) := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpM2 ?_
      obtain ⟨c, hc⟩ := h
      exact ⟨c, by rw [← Nat.mul_div_cancel' hpM, hc]; ring⟩
    have := Nat.gcd_eq_gcd_ab p (M / p)
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    simp only [Nat.cast_one] at this
    linear_combination (-1 : ℤ) * this

theorem exists_isIntegralQExp_of_mem {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ}
    (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    {g : CuspForm (CohCarrier.GammaH M H) 2} (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ pz : PowerSeries ℤ, ModularCurve.IsIntegralQExp ⇑g pz := by
  classical
  have hint : ∀ n : ℕ, ∃ m : ℤ, (m : ℂ) = PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑g) := by
    intro n
    have h := ((CuspForm.mem_twoCuspIntegralSet_iff g).mp hg 1 (Subring.one_mem _)
      (alDatumP (Fact.out) hpM hpM2) n).1
    rw [Module.End.one_apply] at h
    exact Subring.mem_bot.mp h
  refine ⟨PowerSeries.mk fun n => (hint n).choose, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]
  exact (hint n).choose_spec

theorem exists_series_of_mem_integralClosure {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ}
    (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) {g : CuspForm (CohCarrier.GammaH M H) 2}
    (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (integralClosure ℤ ℂ).toSubring) :
    ∃ pg : PowerSeries ↥(integralClosure ℤ ℂ), pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ⇑g := by
  have hcoef : ∀ n : ℕ, ModularFormClass.qCoeff (⇑g) n ∈ integralClosure ℤ ℂ := fun n => by
    have h := (hg 1 (Subring.one_mem _) (alDatumP (Fact.out) hpM hpM2) n).1
    rwa [Module.End.one_apply, Subalgebra.mem_toSubring] at h
  refine ⟨PowerSeries.mk fun n => ⟨ModularFormClass.qCoeff (⇑g) n, hcoef n⟩, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rfl

theorem algebraMap_comp_intCast_integralClosure :
    (algebraMap ↥(integralClosure ℤ ℂ) ℂ).comp (Int.castRingHom ↥(integralClosure ℤ ℂ)) = Int.castRingHom ℂ :=
  RingHom.ext_int _ _

section Frame

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
  (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
  (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
  (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
  (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
  (φ : ↥(integralClosure ℤ ℂ) →+* K)

noncomputable def red (s : CuspForm (CohCarrier.GammaH M H) 2) (hs : s ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] :=
  ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ⟨s, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hs⟩)

omit [NeZero (M / p)] [IsAlgClosed K] [CharP K p] in
theorem red_def (s : CuspForm (CohCarrier.GammaH M H) 2) (hs : s ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    red p M H hpM K ρinf s hs =
      ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ⟨s, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hs⟩) :=
  rfl

include hpM2 hHp hρinf in

theorem exists_decomp
    (s : CuspForm (CohCarrier.GammaH M H) 2) (hs : s ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ (Ds : ℕ) (_ : ¬ p ∣ Ds) (X : CuspForm (CohCarrier.GammaH M H) 2)
      (_ : (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e s))
      (n : ℕ) (a : Fin n → ↥(integralClosure ℤ ℂ)) (g : Fin n → CuspForm (CohCarrier.GammaH M H) 2)
      (hg : ∀ i, g i ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
      (pg : PowerSeries ↥(integralClosure ℤ ℂ)),
      (∑ i, ((a i : ℂ)) • g i) = (Ds : ℂ) • X ∧
      pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
        UpperHalfPlane.qExpansion 1 ((Ds : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e s)) ∧
      ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        (∑ i, φ (a i) • red p M H hpM K ρinf (g i) (hg i)) = HahnSeries.ofPowerSeries ℤ K (pg.map φ) := by
  classical
  obtain ⟨D₀, hD₀, gT, hgT, hgTmem⟩ :=
    CuspForm.exists_not_dvd_and_coe_eq_smul_alSlash_diamond_and_mem_twoCuspIntegralSet_integralClosure p M H hpM hpM2 hHp Wd e s hs
  obtain ⟨X, hX⟩ := CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one Wd H hHp 2
    (CuspForm.diamondLinH 2 e s)
  have hgTX : gT = (D₀ : ℂ) • X := by
    refine DFunLike.ext' ?_
    rw [hgT, CuspForm.IsGLPos.coe_smul, hX]
  have hgTspan : gT ∈ Submodule.span ↥(integralClosure ℤ ℂ).toSubring (CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) := by
    have h1 : gT ∈ (CuspForm.twoCuspLattice M H 2 p (integralClosure ℤ ℂ).toSubring : Set (CuspForm (CohCarrier.GammaH M H) 2)) :=
      CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p _ hgTmem
    rw [CuspForm.twoCuspLattice_integralClosure_eq_span_twoCuspIntegralSet_bot p M hpM hpM2 H hHp] at h1
    exact h1
  obtain ⟨n, a, gs, hsum⟩ := Submodule.mem_span_set'.mp hgTspan
  let g : Fin n → CuspForm (CohCarrier.GammaH M H) 2 := fun i => (gs i : CuspForm (CohCarrier.GammaH M H) 2)
  have hg : ∀ i, g i ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := fun i => (gs i).2
  have hsum' : (∑ i, ((a i : ↥(integralClosure ℤ ℂ)) : ℂ) • g i) = gT := by
    rw [← hsum]; rfl
  have hz : ∀ i, ∃ pz : PowerSeries ℤ, ModularCurve.IsIntegralQExp ⇑(g i) pz :=
    fun i => exists_isIntegralQExp_of_mem hpM hpM2 (hg i)
  choose pz hpz using hz
  let pg : PowerSeries ↥(integralClosure ℤ ℂ) :=
    ∑ i, PowerSeries.C (a i : ↥(integralClosure ℤ ℂ)) * (pz i).map (Int.castRingHom ↥(integralClosure ℤ ℂ))
  have hpg_sum : pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 (⇑(∑ i, ((a i : ↥(integralClosure ℤ ℂ)) : ℂ) • g i)) := by
    rw [qExpansion_coe_sum_smul]
    simp only [pg, map_sum, map_mul, PowerSeries.map_C]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmm : (PowerSeries.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ)) ((PowerSeries.map (Int.castRingHom ↥(integralClosure ℤ ℂ))) (pz i))
        = (pz i).map (Int.castRingHom ℂ) := by
      rw [← RingHom.comp_apply (PowerSeries.map _) (PowerSeries.map _), ← PowerSeries.map_comp,
        algebraMap_comp_intCast_integralClosure]
    rw [hmm, (hpz i), PowerSeries.smul_eq_C_mul]
    rfl
  have hpg : pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D₀ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e s)) := by
    rw [hpg_sum, hsum', hgT]
  refine ⟨D₀, hD₀, X, hX, n, (fun i => (a i : ↥(integralClosure ℤ ℂ))), g, hg, pg, ?_, hpg, ?_⟩
  · rw [hsum', hgTX]
  · exact ModularCurve.diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
      p M H hpM hpM2 K ρinf hρinf φ (fun i => (a i : ↥(integralClosure ℤ ℂ))) g hg pg hpg_sum

omit [IsAlgClosed K] [Algebra (ZMod p) K] in
theorem natCast_ne_zero_of_not_dvd {D : ℕ} (hD : ¬ p ∣ D) : (D : K) ≠ 0 := by
  intro h
  exact hD ((CharP.cast_eq_zero_iff K p D).mp h)

theorem diffQExp_injective :
    Function.Injective (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) :=
  ModularCurve.diffQExp_qExpFunctionFieldC_injective K _ (ModularCurve.translation_mem_GammaH _ _)

noncomputable def Gd (d : (ZMod M)ˣ) :
    Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] →ₗ[K]
      Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] :=
  ModularCurve.genDiffModL K p M H hpM (∅ : Set ℕ) (CohCarrier.Gen.dia d)

include hpM2 hHp hρinf in

theorem Gd_apply_rho (d : (ZMod M)ˣ) (y : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p) :
    Gd p M H hpM K d (ρinf y) = ρinf ((CuspForm.intTwoCuspGenMod M H p (∅ : Set ℕ) (CohCarrier.Gen.dia d)).baseChange K y) := by
  have h := ModularCurve.IsInfReductionMap.comp_baseChange_genDia_eq_genDiffModL_comp p M hpM hpM2 H hHp K (∅ : Set ℕ) hρinf d
  have h' := LinearMap.congr_fun h y
  simp only [LinearMap.comp_apply] at h'
  rw [Gd, ← h']

include hpM2 hHp hρinf in

theorem red_diamondLinH (d : (ZMod M)ˣ) (s : CuspForm (CohCarrier.GammaH M H) 2)
    (hs : s ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (hs' : CuspForm.diamondLinH 2 d s ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    red p M H hpM K ρinf (CuspForm.diamondLinH 2 d s) hs' = Gd p M H hpM K d (red p M H hpM K ρinf s hs) := by
  rw [red_def, red_def, Gd_apply_rho p M H hpM hpM2 hHp K ρinf hρinf, LinearMap.baseChange_tmul,
    CuspForm.intTwoCuspGenMod_reduce]
  congr 2

include hpM2 hHp hρinf in

theorem Gd_mem_range (d : (ZMod M)ˣ) {x : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hx : x ∈ LinearMap.range ρinf) : Gd p M H hpM K d x ∈ LinearMap.range ρinf := by
  obtain ⟨y, rfl⟩ := hx
  rw [Gd_apply_rho p M H hpM hpM2 hHp K ρinf hρinf]
  exact LinearMap.mem_range_self _ _

theorem intTwoCuspGenMod_inv_comp (d : (ZMod M)ˣ) :
    CuspForm.intTwoCuspGenMod M H p (∅ : Set ℕ) (CohCarrier.Gen.dia d⁻¹) ∘ₗ
      CuspForm.intTwoCuspGenMod M H p (∅ : Set ℕ) (CohCarrier.Gen.dia d) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := CuspForm.intTwoCuspReduce_surjective M H p x
  rw [LinearMap.comp_apply, LinearMap.id_apply, CuspForm.intTwoCuspGenMod_reduce, CuspForm.intTwoCuspGenMod_reduce]
  congr 1
  apply Subtype.ext
  show CuspForm.diamondLinH 2 d⁻¹ (CuspForm.diamondLinH 2 d (z : CuspForm (CohCarrier.GammaH M H) 2)) = z
  exact diamondLinH_inv_diamondLinH 2 d _

include hpM2 hHp hρinf in

theorem Gd_inv_Gd (d : (ZMod M)ˣ) {x : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hx : x ∈ LinearMap.range ρinf) : Gd p M H hpM K d⁻¹ (Gd p M H hpM K d x) = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [Gd_apply_rho p M H hpM hpM2 hHp K ρinf hρinf, Gd_apply_rho p M H hpM hpM2 hHp K ρinf hρinf,
    ← LinearMap.comp_apply (f := (CuspForm.intTwoCuspGenMod M H p ∅ (CohCarrier.Gen.dia d⁻¹)).baseChange K),
    ← LinearMap.baseChange_comp, intTwoCuspGenMod_inv_comp, LinearMap.baseChange_id, LinearMap.id_apply]

include hpM2 hHp hρinf in
theorem Gd_Gd_inv (d : (ZMod M)ˣ) {x : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hx : x ∈ LinearMap.range ρinf) : Gd p M H hpM K d (Gd p M H hpM K d⁻¹ x) = x := by
  have h := Gd_inv_Gd p M H hpM hpM2 hHp K ρinf hρinf d⁻¹ hx
  rwa [inv_inv] at h

def IsPinned
    (Wl : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K]
      ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Prop :=
  ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
      (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
      (D : ℕ) (_ : ¬ p ∣ D)
      (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
      pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
        UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
      ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p),
        ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) :
            Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
          ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
        (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
            ((Wl ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) :
              Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
          HahnSeries.ofPowerSeries ℤ K (pfW.map φ)

variable
  (Wl : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K]
    ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))

include hpM2 hHp in

theorem exists_theta_Wl_red (hWl : IsPinned p M H hpM K ρinf Wd e φ Wl)
    (g : CuspForm (CohCarrier.GammaH M H) 2) (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (ωg : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hωg : (ωg : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
      red p M H hpM K ρinf g hg) :
    ∃ (Dg : ℕ) (_ : ¬ p ∣ Dg) (gT : CuspForm (CohCarrier.GammaH M H) 2) (pg : PowerSeries ↥(integralClosure ℤ ℂ)),
      (⇑gT : UpperHalfPlane → ℂ) = (Dg : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e g) ∧
      pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ⇑gT ∧
      ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
          ((Wl ωg : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) :
            Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
        ((Dg : K))⁻¹ • HahnSeries.ofPowerSeries ℤ K (pg.map φ) := by
  obtain ⟨Dg, hDg, gT, hgT, hmem⟩ :=
    CuspForm.exists_not_dvd_and_coe_eq_smul_alSlash_diamond_and_mem_twoCuspIntegralSet_integralClosure p M H hpM hpM2 hHp Wd e g hg
  obtain ⟨pg, hpg⟩ := exists_series_of_mem_integralClosure hpM hpM2 hmem
  have hpin := hWl g hg Dg hDg pg (by rw [hpg, hgT]) ωg hωg
  refine ⟨Dg, hDg, gT, pg, hgT, hpg, ?_⟩
  rw [← hpin, smul_smul, inv_mul_cancel₀ (natCast_ne_zero_of_not_dvd p K hDg), one_smul]

omit [NeZero M] in
theorem alSlash_sum_smul {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (F : ι → UpperHalfPlane → ℂ) :
    ModularForm.alSlash W k (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i • ModularForm.alSlash W k (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ModularForm.alSlash_def, SlashAction.zero_slash]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ModularForm.alSlash_add, ModularForm.alSlash_smul, ih]

set_option synthInstance.maxHeartbeats 800000 in
include hpM2 hHp hρinf in

theorem coe_Wl_Wl_eq (hWl : IsPinned p M H hpM K ρinf Wd e φ Wl)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)
    (δ e' : (ZMod M)ˣ)
    (hδ : ∀ F : CuspForm (CohCarrier.GammaH M H) 2,
      ModularForm.alSlash Wd 2 (ModularForm.alSlash Wd 2 ⇑F) = ⇑(CuspForm.diamondLinH 2 δ F))
    (he' : ∀ F X : CuspForm (CohCarrier.GammaH M H) 2,
      (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑F →
      (⇑(CuspForm.diamondLinH 2 e X) : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e' F))
    (s : CuspForm (CohCarrier.GammaH M H) 2) (hs : s ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hω : (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = red p M H hpM K ρinf s hs)
    (hs₃ : CuspForm.diamondLinH 2 δ (CuspForm.diamondLinH 2 e' (CuspForm.diamondLinH 2 e s)) ∈
      CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ((Wl (Wl ω) : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
      red p M H hpM K ρinf (CuspForm.diamondLinH 2 δ (CuspForm.diamondLinH 2 e' (CuspForm.diamondLinH 2 e s))) hs₃ := by
  classical
  have hp : p.Prime := Fact.out
  have hinj := diffQExp_injective p M H hpM K
  obtain ⟨Ds, hDs, X, hX, n, a, g, hg, pg, hsum, hpg, hΘ⟩ := exists_decomp p M H hpM hpM2 hHp K ρinf hρinf Wd e φ s hs
  have hDsK : (Ds : K) ≠ 0 := natCast_ne_zero_of_not_dvd p K hDs
  have hmemV : ∀ i, red p M H hpM K ρinf (g i) (hg i) ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := fun i => by
    rw [← hrange]; exact LinearMap.mem_range_self _ _
  let ωg : Fin n → ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) := fun i => ⟨red p M H hpM K ρinf (g i) (hg i), hmemV i⟩
  have hωg : ∀ i, ((ωg i : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = red p M H hpM K ρinf (g i) (hg i) := fun i => rfl

  have h1 : ((Wl ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = (Ds : K)⁻¹ • ∑ i, φ (a i) • red p M H hpM K ρinf (g i) (hg i) := by
    have hpin := hWl s hs Ds hDs pg hpg ω hω
    rw [← hΘ, ← LinearMap.map_smul_of_tower] at hpin
    have h := hinj hpin
    rw [← h, smul_smul, inv_mul_cancel₀ hDsK, one_smul]
  have h1' : Wl ω = (Ds : K)⁻¹ • ∑ i, φ (a i) • ωg i := by
    apply Subtype.ext
    rw [h1, Submodule.coe_smul_of_tower, Submodule.coe_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Submodule.coe_smul_of_tower]

  have h2 : ∀ i, ∃ (Dg : ℕ) (_ : ¬ p ∣ Dg) (gT : CuspForm (CohCarrier.GammaH M H) 2) (pgT : PowerSeries ↥(integralClosure ℤ ℂ)),
      (⇑gT : UpperHalfPlane → ℂ) = (Dg : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e (g i)) ∧
      pgT.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ⇑gT ∧
      ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
          ((Wl (ωg i) : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ((Dg : K))⁻¹ • HahnSeries.ofPowerSeries ℤ K (pgT.map φ) :=
    fun i => exists_theta_Wl_red p M H hpM hpM2 hHp K ρinf Wd e φ Wl hWl (g i) (hg i) (ωg i) rfl
  choose Dg hDg gT pgT hgT hpgT hΘg using h2

  have h3 : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
      ((Wl (Wl ω) : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
      (Ds : K)⁻¹ • ∑ i, φ (a i) • (((Dg i : K))⁻¹ • HahnSeries.ofPowerSeries ℤ K ((pgT i).map φ)) := by
    rw [h1', map_smul, map_sum, Submodule.coe_smul_of_tower, Submodule.coe_sum, LinearMap.map_smul_of_tower, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.coe_smul_of_tower, LinearMap.map_smul_of_tower, hΘg]

  obtain ⟨ps₃, hps₃⟩ := exists_isIntegralQExp_of_mem hpM hpM2 hs₃
  have hφint : φ.comp (Int.castRingHom ↥(integralClosure ℤ ℂ)) = Int.castRingHom K := RingHom.ext_int _ _
  have htarget : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
      (red p M H hpM K ρinf _ hs₃) =
      HahnSeries.ofPowerSeries ℤ K ((ps₃.map (Int.castRingHom ↥(integralClosure ℤ ℂ))).map φ) := by
    rw [red_def, hρinf.diffQExp_apply hs₃ hps₃, ModularCurve.intSeriesC, ← RingHom.comp_apply (PowerSeries.map φ),
      ← PowerSeries.map_comp, hφint]

  let D' : ℕ := ∏ j, Dg j
  let Dc : Fin n → ℕ := fun i => ∏ j ∈ Finset.univ.erase i, Dg j
  have hDD : ∀ i, Dg i * Dc i = D' := fun i => Finset.mul_prod_erase Finset.univ Dg (Finset.mem_univ i)
  have hD'p : ¬ p ∣ D' := by
    intro h
    obtain ⟨j, _, hj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    exact hDg j hj
  have hD'K : (D' : K) ≠ 0 := natCast_ne_zero_of_not_dvd p K hD'p

  have hforms : (∑ i, ((a i : ℂ) * (Dc i : ℂ)) • gT i) =
      ((Ds * D' : ℕ) : ℂ) • CuspForm.diamondLinH 2 δ (CuspForm.diamondLinH 2 e' (CuspForm.diamondLinH 2 e s)) := by
    apply DFunLike.ext'
    rw [coe_sum_smul, CuspForm.IsGLPos.coe_smul]
    calc ∑ i, ((a i : ℂ) * (Dc i : ℂ)) • (⇑(gT i) : UpperHalfPlane → ℂ)
        = ∑ i, ((a i : ℂ) * (D' : ℂ)) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e (g i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hgT i, smul_smul]
          congr 1
          have : ((Dc i : ℕ) : ℂ) * (Dg i : ℂ) = (D' : ℂ) := by
            rw [mul_comm]; exact_mod_cast hDD i
          rw [mul_assoc, this]
      _ = (D' : ℂ) • ∑ i, (a i : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e (g i)) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, mul_comm]
      _ = (D' : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e (∑ i, (a i : ℂ) • g i)) := by
          rw [map_sum]
          simp only [map_smul]
          rw [coe_sum_smul, alSlash_sum_smul]
      _ = ((Ds * D' : ℕ) : ℂ) • ⇑(CuspForm.diamondLinH 2 δ (CuspForm.diamondLinH 2 e' (CuspForm.diamondLinH 2 e s))) := by
          rw [hsum, map_smul, CuspForm.IsGLPos.coe_smul, ModularForm.alSlash_smul, he' _ X hX, hδ, smul_smul]
          push_cast
          rw [mul_comm]

  have hZ : ∑ i, PowerSeries.C (a i * (Dc i : ↥(integralClosure ℤ ℂ))) * pgT i =
      PowerSeries.C ((Ds * D' : ℕ) : ↥(integralClosure ℤ ℂ)) * ps₃.map (Int.castRingHom ↥(integralClosure ℤ ℂ)) := by
    apply PowerSeries.map_injective (algebraMap ↥(integralClosure ℤ ℂ) ℂ) Subtype.val_injective
    have hmm : (PowerSeries.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ)) ((PowerSeries.map (Int.castRingHom ↥(integralClosure ℤ ℂ))) ps₃)
        = ps₃.map (Int.castRingHom ℂ) := by
      rw [← RingHom.comp_apply (PowerSeries.map _) (PowerSeries.map _), ← PowerSeries.map_comp,
        algebraMap_comp_intCast_integralClosure]
    rw [map_sum, map_mul, PowerSeries.map_C, hmm, hps₃]
    have hL : ∀ i, (PowerSeries.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ)) (PowerSeries.C (a i * (Dc i : ↥(integralClosure ℤ ℂ))) * pgT i) =
        ((a i : ℂ) * (Dc i : ℂ)) • UpperHalfPlane.qExpansion 1 ⇑(gT i) := by
      intro i
      rw [map_mul, PowerSeries.map_C, hpgT, PowerSeries.smul_eq_C_mul]
      congr 2
    rw [Finset.sum_congr rfl fun i _ => hL i, ← qExpansion_coe_sum_smul, hforms, qExpansion_coe_smul,
      PowerSeries.smul_eq_C_mul]
    congr 2

  have hK : ∑ i, (φ (a i) * (Dc i : K)) • HahnSeries.ofPowerSeries ℤ K ((pgT i).map φ) =
      ((Ds : K) * (D' : K)) • HahnSeries.ofPowerSeries ℤ K ((ps₃.map (Int.castRingHom ↥(integralClosure ℤ ℂ))).map φ) := by
    have h := congrArg (fun P : PowerSeries ↥(integralClosure ℤ ℂ) => HahnSeries.ofPowerSeries ℤ K (PowerSeries.map φ P)) hZ
    beta_reduce at h
    rw [map_sum, map_sum, map_mul, map_mul, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
      map_natCast, Nat.cast_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, map_mul, map_natCast]

  apply hinj
  rw [h3, htarget]
  have hinv : ∀ i, ((Dg i : K))⁻¹ = (Dc i : K) * ((D' : K))⁻¹ := by
    intro i
    have hDgK : (Dg i : K) ≠ 0 := natCast_ne_zero_of_not_dvd p K (hDg i)
    have hprod : (Dg i : K) * (Dc i : K) = (D' : K) := by rw [← Nat.cast_mul, hDD i]
    field_simp
    rw [← hprod]
  have hsum' : ∑ i, φ (a i) • (((Dg i : K))⁻¹ • HahnSeries.ofPowerSeries ℤ K ((pgT i).map φ)) =
      ((D' : K))⁻¹ • ∑ i, (φ (a i) * (Dc i : K)) • HahnSeries.ofPowerSeries ℤ K ((pgT i).map φ) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hinv i, smul_smul, smul_smul]
    congr 1
    ring
  rw [hsum', hK, smul_smul, smul_smul]
  have : (Ds : K)⁻¹ * ((D' : K))⁻¹ * ((Ds : K) * (D' : K)) = 1 := by
    field_simp
  rw [this, one_smul]

end Frame

end TW2K2

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)

    (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)
    (Wl : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hWl :
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D)
          (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
          ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
            (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ((Wl ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              HahnSeries.ofPowerSeries ℤ K (pfW.map φ))
    :
    Function.Bijective Wl := by
  classical
  obtain ⟨δ, hδ⟩ := TW2K2.exists_forall_alSlash_alSlash_two Wd H
  obtain ⟨e', he'⟩ := TW2K2.exists_forall_dia_alSlash Wd H 2 e
  have hWl' : TW2K2.IsPinned p M H hpM K ρinf Wd e φ Wl := hWl

  let Ec : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] := TW2K2.Gd p M H hpM K δ ∘ₗ TW2K2.Gd p M H hpM K e' ∘ₗ TW2K2.Gd p M H hpM K e
  let Eci : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] := TW2K2.Gd p M H hpM K e⁻¹ ∘ₗ TW2K2.Gd p M H hpM K e'⁻¹ ∘ₗ TW2K2.Gd p M H hpM K δ⁻¹
  have hG : ∀ (d : (ZMod M)ˣ) (x : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]), x ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p → TW2K2.Gd p M H hpM K d x ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by
    intro d x hx
    rw [← hrange] at hx ⊢
    exact TW2K2.Gd_mem_range p M H hpM hpM2 hHp K ρinf hρinf d hx
  have hEc : ∀ x ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p, Ec x ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := fun x hx => hG δ _ (hG e' _ (hG e _ hx))
  have hEci : ∀ x ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p, Eci x ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := fun x hx => hG e⁻¹ _ (hG e'⁻¹ _ (hG δ⁻¹ _ hx))
  have hEE : ∀ x ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p, Eci (Ec x) = x := by
    intro x hx
    rw [← hrange] at hx
    have h1 := TW2K2.Gd_mem_range p M H hpM hpM2 hHp K ρinf hρinf e hx
    have h2 := TW2K2.Gd_mem_range p M H hpM hpM2 hHp K ρinf hρinf e' h1
    show TW2K2.Gd p M H hpM K e⁻¹ (TW2K2.Gd p M H hpM K e'⁻¹ (TW2K2.Gd p M H hpM K δ⁻¹
      (TW2K2.Gd p M H hpM K δ (TW2K2.Gd p M H hpM K e' (TW2K2.Gd p M H hpM K e x))))) = x
    rw [TW2K2.Gd_inv_Gd p M H hpM hpM2 hHp K ρinf hρinf δ h2, TW2K2.Gd_inv_Gd p M H hpM hpM2 hHp K ρinf hρinf e' h1,
      TW2K2.Gd_inv_Gd p M H hpM hpM2 hHp K ρinf hρinf e hx]
  have hEE' : ∀ x ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p, Ec (Eci x) = x := by
    intro x hx
    rw [← hrange] at hx
    have h1 := TW2K2.Gd_mem_range p M H hpM hpM2 hHp K ρinf hρinf δ⁻¹ hx
    have h2 := TW2K2.Gd_mem_range p M H hpM hpM2 hHp K ρinf hρinf e'⁻¹ h1
    show TW2K2.Gd p M H hpM K δ (TW2K2.Gd p M H hpM K e' (TW2K2.Gd p M H hpM K e
      (TW2K2.Gd p M H hpM K e⁻¹ (TW2K2.Gd p M H hpM K e'⁻¹ (TW2K2.Gd p M H hpM K δ⁻¹ x))))) = x
    rw [TW2K2.Gd_Gd_inv p M H hpM hpM2 hHp K ρinf hρinf e h2, TW2K2.Gd_Gd_inv p M H hpM hpM2 hHp K ρinf hρinf e' h1,
      TW2K2.Gd_Gd_inv p M H hpM hpM2 hHp K ρinf hρinf δ hx]
  let E : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) := Ec.restrict hEc

  have hdia : ∀ (d : (ZMod M)ˣ) (g : CuspForm (CohCarrier.GammaH M H) 2),
      g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) →
      CuspForm.diamondLinH 2 d g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := fun d g hg =>
    CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (CuspForm.heckeGenH_mem_heckeRingH (∅ : Set ℕ) 2 (CohCarrier.Gen.dia d)) hg

  have hspan := ModularCurve.span_ssPolarDifferentials_atkinLehnerPinned_eq_top p M H hpM hpM2 hHp K ρinf hρinf hrange Wd e he
  have hWW : Wl ∘ₗ Wl = E := by
    refine LinearMap.ext_on hspan (fun ω hωG => ?_)
    obtain ⟨f, hf, D, hD, pfW, hpfW, hω⟩ := hωG
    apply Subtype.ext
    rw [LinearMap.comp_apply, LinearMap.restrict_apply]
    show ((Wl (Wl ω) : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = Ec (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    have hs₁ := hdia e f hf
    have hs₂ := hdia e' _ hs₁
    have hs₃ := hdia δ _ hs₂
    rw [TW2K2.coe_Wl_Wl_eq p M H hpM hpM2 hHp K ρinf hρinf Wd e φ Wl hWl' hrange δ e' hδ he' f hf ω hω hs₃,
      TW2K2.red_diamondLinH p M H hpM hpM2 hHp K ρinf hρinf δ _ hs₂ hs₃,
      TW2K2.red_diamondLinH p M H hpM hpM2 hHp K ρinf hρinf e' _ hs₁ hs₂,
      TW2K2.red_diamondLinH p M H hpM hpM2 hHp K ρinf hρinf e f hf hs₁,
      (TW2K2.red_def p M H hpM K ρinf f hf).trans hω.symm]
    rfl

  constructor
  · intro a b hab
    have h : E a = E b := by rw [← hWW, LinearMap.comp_apply, LinearMap.comp_apply, hab]
    have h' : Ec (a : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = Ec (b : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) := by
      have := congrArg Subtype.val h
      rwa [LinearMap.restrict_apply, LinearMap.restrict_apply] at this
    apply Subtype.ext
    rw [← hEE _ a.2, ← hEE _ b.2, h']
  · intro y
    refine ⟨Wl ⟨Eci (y : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]), hEci _ y.2⟩, ?_⟩
    have h := LinearMap.congr_fun hWW ⟨Eci (y : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]), hEci _ y.2⟩
    rw [LinearMap.comp_apply] at h
    rw [h]
    apply Subtype.ext
    rw [LinearMap.restrict_apply]
    exact hEE' _ y.2

end S_ModularCurve_bijective_of_atkinLehnerPinAlong
end P2MW
export P2MW.S_ModularCurve_bijective_of_atkinLehnerPinAlong (solution)
