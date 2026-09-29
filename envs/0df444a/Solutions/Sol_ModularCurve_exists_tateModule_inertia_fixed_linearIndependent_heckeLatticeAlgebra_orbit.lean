-- Prove2me | solution 1 for ModularCurve.exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/42ebba2e-446c-5532-b292-6d694b626738

import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two
import Theorems.Thm_ModularCurve_exists_linearEquiv_rationalTateModule_tensor_periodLattice
import Theorems.Thm_LinearIndependent_linearMap_baseChange_of_int
import Theorems.Thm_FixedPart_isReduced_of_linearIndependent_of_trace
import Theorems.Thm_FixedPart_exists_trace_mul_ne_zero
import Theorems.Thm_CuspForm_isReduced_heckeLatticeAlgebra
import Theorems.Thm_FixedPart_exists_smul_eq_zero_forall_of_comp_eq_zero
import Theorems.Thm_TensorProduct_exists_pow_smul_eq_one_tmul
import Theorems.Thm_ModularCurve_tateModule_rep_comp_tateHeckeRep_comm
import Theorems.Thm_ModularCurve_heckeProj_surjective
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply"

set_option autoImplicit false

open ModularCurve CuspForm
open scoped TensorProduct

namespace HEART

theorem heckeEvalForms_two_eq_heckeProj (p : ℕ) [NeZero p] : heckeEvalForms p 2 = heckeProj p := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [heckeEvalForms_C, heckeProj_C]
  · intro ℓ
    show heckeEvalForms p 2 (heckeGen ℓ) = heckeProj p (heckeGen ℓ)
    by_cases h : (ℓ : ℕ) ∣ p
    · rw [heckeEvalForms_heckeGen_of_dvd h, heckeProj_heckeGen_of_dvd ℓ h]
    · rw [heckeEvalForms_heckeGen_of_not_dvd h, heckeProj_heckeGen_of_not_dvd ℓ h]

theorem surjective_e (p : ℕ) [NeZero p] :
    Function.Surjective ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) := by
  rw [heckeEvalForms_two_eq_heckeProj]
  exact (latticeRestrictHom_surjective p ∅).comp (heckeProj_surjective p)

variable (N : ℕ) [NeZero N]

theorem cuspHeckeAeval_toRingHom_eq_heckeEvalForms :
    (cuspHeckeAeval N).toRingHom = heckeEvalForms N 2 := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [heckeEvalForms_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.algHom_C]
  · intro ℓ
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    show cuspHeckeAeval N (heckeGen ℓ) = heckeEvalForms N 2 (heckeGen ℓ)
    rw [cuspHeckeAeval_heckeGen, heckeEvalForms_heckeGen]
    apply Subtype.ext
    by_cases h : (ℓ : ℕ) ∣ N
    · rw [cuspHeckeGen_of_dvd N ℓ h, heckeFormsGen_of_dvd h]; rfl
    · rw [cuspHeckeGen_of_not_dvd N ℓ h, heckeFormsGen_of_not_dvd h]; rfl

theorem cuspHeckeRep_eq_coe_heckeEvalForms (t : HeckeAlg) :
    cuspHeckeRep N t = (heckeEvalForms N 2 t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by
  rw [cuspHeckeRep_apply, ← cuspHeckeAeval_toRingHom_eq_heckeEvalForms]
  rfl

theorem periodLatticeHeckeEnd_eq_zero_of_heckeEvalForms_eq_zero (t : HeckeAlg) (ht : heckeEvalForms N 2 t = 0) :
    periodLatticeHeckeEnd N t = 0 := by
  have hst := ModularCurve.periodLatticeHeckeStable N
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [coe_periodLatticeHeckeEnd_apply hst, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  apply LinearMap.ext
  intro f
  rw [dualHeckeRep_apply_apply, cuspHeckeRep_eq_coe_heckeEvalForms, ht, ZeroMemClass.coe_zero,
    LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

theorem heckeEvalForms_eq_zero_of_periodLatticeHeckeEnd_eq_zero (t : HeckeAlg) (ht : periodLatticeHeckeEnd N t = 0) :
    heckeEvalForms N 2 t = 0 := by
  have hst := ModularCurve.periodLatticeHeckeStable N

  have hΛ : ∀ x ∈ periodLattice N, dualHeckeRep N t x = 0 := fun x hx => by
    have h1 : periodLatticeHeckeEnd N t ⟨x, hx⟩ = 0 := by rw [ht, LinearMap.zero_apply]
    have h2 := congrArg (fun y : periodLattice N => (y : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) h1
    simpa only [coe_periodLatticeHeckeEnd_apply hst, ZeroMemClass.coe_zero] using h2

  obtain ⟨n, b, -, hspan⟩ := ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  have hall : ∀ φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2), dualHeckeRep N t φ = 0 := by
    intro φ
    have hφ : φ ∈ Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) := by
      rw [hspan]; trivial
    refine Submodule.span_induction (p := fun φ _ => dualHeckeRep N t φ = 0) ?_ ?_ ?_ ?_ hφ
    · rintro _ ⟨i, rfl⟩; exact hΛ _ (b i).2
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [← Complex.coe_smul, map_smul, hx, smul_zero]

  have hrep : cuspHeckeRep N t = 0 := by
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.zero_apply, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have := congrArg (fun ψ : Module.Dual ℂ _ => ψ f) (hall φ)
    simpa [dualHeckeRep_apply_apply] using this
  rw [cuspHeckeRep_eq_coe_heckeEvalForms] at hrep
  exact Subtype.ext hrep

end HEART

namespace TateModule
p2m_export "TateModule" "torsion compat_pow coe_zero smul_apply natCast_padicInt_smul_apply rep free"
p2m_open "TateModule"

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]

theorem eq_zero_of_pow_smul_eq_zero (k : ℕ) (x : TateModule p M) (hx : ((p : ℤ_[p]) ^ k) • x = 0) : x = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have h := congrArg (fun y : TateModule p M => (y : ℕ → M) (n + k)) hx
  rw [← Nat.cast_pow, natCast_padicInt_smul_apply, compat_pow] at h
  simpa using h

scoped instance : NoZeroSMulDivisors ℤ_[p] (TateModule p M) := by
  refine ⟨fun {a x} h => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  · right

    have hu : a = (PadicInt.unitCoeff ha : ℤ_[p]) * (p : ℤ_[p]) ^ a.valuation := PadicInt.unitCoeff_spec ha
    apply eq_zero_of_pow_smul_eq_zero a.valuation x
    have h1 : (PadicInt.unitCoeff ha : ℤ_[p]) • (((p : ℤ_[p]) ^ a.valuation) • x) = 0 := by
      rw [← mul_smul, ← hu, h]
    have h2 := congrArg (fun y => (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • y) h1
    simp only [smul_zero, ← mul_smul] at h2
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h2

theorem mk_one_injective :
    Function.Injective (fun x : TateModule p M => (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x : TateModule p M → ℚ_[p] ⊗[ℤ_[p]] TateModule p M) := by

  intro x y hxy
  have key : ∀ z : TateModule p M, (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] z = 0 → z = 0 := by
    intro z hz
    haveI : IsLocalizedModule (nonZeroDivisors ℤ_[p])
        (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1) :=
      (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[p]) ℚ_[p] _).mpr
        (TensorProduct.isBaseChange ℤ_[p] (TateModule p M) ℚ_[p])
    have h0 : TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1 z = 0 := hz
    rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[p])] at h0
    obtain ⟨s, hs⟩ := h0
    exact (smul_eq_zero.mp hs).resolve_left (nonZeroDivisors.ne_zero s.2)
  have : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (x - y) = 0 := by rw [TensorProduct.tmul_sub]; exact sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp (key _ this)

end TateModule
p2m_reactivate "P2MW.S_ModularCurve_exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit.TateModule"

namespace HEART

section Core

variable (q : ℕ) [Fact q.Prime]
  (J : Type) [AddCommGroup J] [Module HeckeAlg J]
  (G : Type) [Group G] [DistribMulAction G J]
  (R : Type) [CommRing R] [Module.Free ℤ R] [Module.Finite ℤ R] [IsReduced R]
  (eR : HeckeAlg →+* R) (heR : Function.Surjective eR)
  (ρ : R →+* Module.End ℤ_[q] (TateModule q J)) (hρ : ∀ t : HeckeAlg, ρ (eR t) = tateHeckeRep q J t)
  (tl : Module.Free.ChooseBasisIndex ℤ R → HeckeAlg) (htl : ∀ i, eR (tl i) = Module.Free.chooseBasis ℤ R i)
  (hLIV : LinearIndependent ℚ_[q] (fun i => rationalHeckeRep q J (tl i)))
  (T₆ : Type) [CommRing T₆] [Algebra ℚ_[q] T₆] (φ : HeckeAlg →+* T₆) (e₆ : (RationalTateModule q J) ≃ₗ[ℚ_[q]] (Fin 2 → T₆))
  (hspanφ : Algebra.adjoin ℚ_[q] (Set.range φ) = ⊤)
  (he₆ : ∀ (t : HeckeAlg) (v : (RationalTateModule q J)), e₆ (rationalHeckeRep q J t v) = φ t • e₆ v)
  (hcomm : ∀ (σ : G) (t : HeckeAlg),
    rationalGaloisRep q J G σ ∘ₗ rationalHeckeRep q J t = rationalHeckeRep q J t ∘ₗ rationalGaloisRep q J G σ)
  (I : Set G) (hN : ∀ σ ∈ I, ∀ τ ∈ I, (TateModule.rep q J G σ - 1) * (TateModule.rep q J G τ - 1) = 0)

include heR hρ htl hLIV hspanφ he₆ hcomm hN in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem core :
    ∃ v : (TateModule q J), (∀ σ ∈ I, TateModule.rep q J G σ v = v) ∧
      LinearIndependent ℤ_[q] (fun i => ρ (Module.Free.chooseBasis ℤ R i) v) := by
  classical
  let b := Module.Free.chooseBasis ℤ R

  have hrat0 : ∀ t : HeckeAlg, eR t = 0 → rationalHeckeRep q J t = 0 := by
    intro t ht
    rw [rationalHeckeRep_apply, ← hρ t]
    show ((ρ (eR t)).baseChange ℚ_[q]) = 0
    rw [ht, map_zero, LinearMap.baseChange_zero]
  have hφ0 : ∀ t : HeckeAlg, eR t = 0 → φ t = 0 := by
    intro t ht
    have h := he₆ t (e₆.symm (Pi.single 0 1))
    rw [hrat0 t ht, LinearMap.zero_apply, map_zero, LinearEquiv.apply_symm_apply] at h
    have h0 := congrFun h 0
    simp only [Pi.zero_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h0
    exact h0.symm

  have hle : RingHom.ker eR ≤ RingHom.ker φ := fun t ht => (RingHom.mem_ker).mpr (hφ0 t ((RingHom.mem_ker).mp ht))
  let f : R →+* T₆ := RingHom.liftOfSurjective eR heR ⟨φ, hle⟩
  have hf : ∀ t, f (eR t) = φ t := fun t => RingHom.liftOfRightInverse_comp_apply _ _ _ _ t
  have hfb : ∀ i, f (b i) = φ (tl i) := fun i => by rw [← htl i, hf]

  have hspanf : Algebra.adjoin ℚ_[q] (Set.range f) = ⊤ := by
    apply top_le_iff.mp
    rw [← hspanφ]
    apply Algebra.adjoin_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨eR t, hf t⟩

  let L : T₆ →ₗ[ℚ_[q]] Module.End ℚ_[q] (RationalTateModule q J) :=
    (e₆.symm.conj : Module.End ℚ_[q] (Fin 2 → T₆) ≃ₗ[ℚ_[q]] Module.End ℚ_[q] (RationalTateModule q J)).toLinearMap ∘ₗ
      (Algebra.lsmul ℚ_[q] ℚ_[q] (Fin 2 → T₆) : T₆ →ₐ[ℚ_[q]] Module.End ℚ_[q] (Fin 2 → T₆)).toLinearMap
  have hL : ∀ t v, L t v = e₆.symm (t • e₆ v) := fun t v => by
    show (e₆.symm.conj (Algebra.lsmul ℚ_[q] ℚ_[q] (Fin 2 → T₆) t)) v = _
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, Algebra.lsmul_coe]
  have hLφ : ∀ s, L (φ s) = rationalHeckeRep q J s := by
    intro s; apply LinearMap.ext; intro v
    rw [hL, ← he₆, LinearEquiv.symm_apply_apply]
  have hli : LinearIndependent ℚ_[q] (fun i => f (b i)) := by
    apply LinearIndependent.of_comp L
    simpa only [Function.comp_def, hfb, hLφ] using hLIV

  obtain ⟨hred, hart⟩ := FixedPart.isReduced_of_linearIndependent_of_trace R
    (fun r hr => FixedPart.exists_trace_mul_ne_zero R r hr) q T₆ f hspanf hli
  haveI := hred
  haveI := hart

  letI instT₆ : Module T₆ (RationalTateModule q J) :=
    { smul := fun t v => e₆.symm (t • e₆ v)
      one_smul := fun v => by show e₆.symm ((1 : T₆) • e₆ v) = v; rw [one_smul, LinearEquiv.symm_apply_apply]
      mul_smul := fun s t v => by
        show e₆.symm ((s * t) • e₆ v) = e₆.symm (s • e₆ (e₆.symm (t • e₆ v)))
        rw [LinearEquiv.apply_symm_apply, mul_smul]
      smul_zero := fun t => by show e₆.symm (t • e₆ 0) = 0; rw [map_zero, smul_zero, map_zero]
      smul_add := fun t v w => by
        show e₆.symm (t • e₆ (v + w)) = e₆.symm (t • e₆ v) + e₆.symm (t • e₆ w)
        rw [map_add, smul_add, map_add]
      add_smul := fun s t v => by
        show e₆.symm ((s + t) • e₆ v) = e₆.symm (s • e₆ v) + e₆.symm (t • e₆ v)
        rw [add_smul, map_add]
      zero_smul := fun v => by show e₆.symm ((0 : T₆) • e₆ v) = 0; rw [zero_smul, map_zero] }
  have hsmul : ∀ (t : T₆) (v : (RationalTateModule q J)), t • v = e₆.symm (t • e₆ v) := fun t v => rfl
  let eT : (RationalTateModule q J) ≃ₗ[T₆] (Fin 2 → T₆) :=
    { e₆ with
      map_smul' := fun t v => by
        show e₆ (e₆.symm (t • e₆ v)) = t • e₆ v
        rw [LinearEquiv.apply_symm_apply] }
  have hφsmul : ∀ (s : HeckeAlg) (v : (RationalTateModule q J)), φ s • v = rationalHeckeRep q J s v := fun s v => by
    rw [hsmul, ← he₆, LinearEquiv.symm_apply_apply]
  have halg : ∀ (c : ℚ_[q]) (v : (RationalTateModule q J)), algebraMap ℚ_[q] T₆ c • v = c • v := fun c v => by
    rw [hsmul, algebraMap_smul, LinearEquiv.map_smul, LinearEquiv.symm_apply_apply]

  have hlin : ∀ (σ : G) (t : T₆) (v : (RationalTateModule q J)),
      rationalGaloisRep q J G σ (t • v) = t • rationalGaloisRep q J G σ v := by
    intro σ t
    have ht : t ∈ Algebra.adjoin ℚ_[q] (Set.range φ) := by rw [hspanφ]; trivial
    refine Algebra.adjoin_induction (p := fun t _ => ∀ v, rationalGaloisRep q J G σ (t • v) =
        t • rationalGaloisRep q J G σ v) ?_ ?_ ?_ ?_ ht
    · rintro _ ⟨s, rfl⟩ v
      rw [hφsmul, hφsmul, ← LinearMap.comp_apply, ← LinearMap.comp_apply, hcomm]
    · intro c v
      rw [halg, halg, LinearMap.map_smul]
    · intro s t _ _ hs ht v
      rw [add_smul, map_add, hs, ht, add_smul]
    · intro s t _ _ hs ht v
      rw [mul_smul, hs, ht, mul_smul]
  let N : ↥I → (RationalTateModule q J) →ₗ[ℚ_[q]] (RationalTateModule q J) := fun σ => (TateModule.rep q J G σ - 1).baseChange ℚ_[q]
  have hNapp : ∀ (σ : ↥I) (v : (RationalTateModule q J)), N σ v = rationalGaloisRep q J G σ v - v := fun σ v => by
    show ((TateModule.rep q J G σ - 1).baseChange ℚ_[q]) v = _
    rw [LinearMap.baseChange_sub, LinearMap.sub_apply, ← rationalGaloisRep_apply, Module.End.one_eq_id,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have hNN : ∀ σ τ : ↥I, N σ ∘ₗ N τ = 0 := fun σ τ => by
    show ((TateModule.rep q J G σ - 1).baseChange ℚ_[q]) ∘ₗ ((TateModule.rep q J G τ - 1).baseChange ℚ_[q]) = 0
    rw [← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, hN σ σ.2 τ τ.2, LinearMap.baseChange_zero]
  have hNlin : ∀ (σ : ↥I) (t : T₆) (v : (RationalTateModule q J)), N σ (t • v) = t • N σ v := fun σ t v => by
    rw [hNapp, hNapp, hlin, smul_sub]
  let g : ↥I → (RationalTateModule q J) →ₗ[T₆] (RationalTateModule q J) := fun σ =>
    { toFun := N σ
      map_add' := (N σ).map_add
      map_smul' := fun t v => hNlin σ t v }
  have hg : ∀ (σ : ↥I) (v : (RationalTateModule q J)), g σ v = N σ v := fun σ v => rfl
  have hgg : ∀ σ τ : ↥I, g σ ∘ₗ g τ = 0 := fun σ τ => by
    apply LinearMap.ext
    intro v
    exact congrArg (fun F : (RationalTateModule q J) →ₗ[ℚ_[q]] (RationalTateModule q J) => F v) (hNN σ τ)

  obtain ⟨v₀, hv₀g, hv₀ann⟩ := FixedPart.exists_smul_eq_zero_forall_of_comp_eq_zero T₆ (RationalTateModule q J) eT g hgg
  have hv₀fix : ∀ σ ∈ I, rationalGaloisRep q J G σ v₀ = v₀ := fun σ hσ => by
    have h := hv₀g ⟨σ, hσ⟩
    rw [hg, hNapp] at h
    exact sub_eq_zero.mp h

  obtain ⟨k, v, hkv⟩ := TensorProduct.exists_pow_smul_eq_one_tmul q (TateModule q J) v₀
  refine ⟨v, ?_, ?_⟩
  · intro σ hσ
    apply TateModule.mk_one_injective
    show (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] (TateModule.rep q J G σ v) = (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] v
    rw [← LinearMap.baseChange_tmul, ← rationalGaloisRep_apply, ← hkv, LinearMap.map_smul, hv₀fix σ hσ]
  · show LinearIndependent ℤ_[q] (fun i => ρ (b i) v)
    apply LinearIndependent.of_comp ((TensorProduct.mk ℤ_[q] ℚ_[q] (TateModule q J) 1).restrictScalars ℤ_[q])
    have hcomp : ∀ i, (TensorProduct.mk ℤ_[q] ℚ_[q] (TateModule q J) 1) (ρ (b i) v) = ((q : ℚ_[q]) ^ k) • (φ (tl i) • v₀) := by
      intro i
      rw [TensorProduct.mk_apply, ← LinearMap.baseChange_tmul, ← htl i, hρ, ← rationalHeckeRep_apply, ← hkv,
        LinearMap.map_smul, hφsmul]
    let orb : T₆ →ₗ[ℚ_[q]] (RationalTateModule q J) :=
      { toFun := fun t => t • v₀
        map_add' := fun s t => add_smul s t v₀
        map_smul' := fun c t => by
          rw [RingHom.id_apply, hsmul, hsmul, smul_assoc, LinearEquiv.map_smul] }
    have horb : LinearMap.ker orb = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro t ht
      exact hv₀ann t ht
    have hLI1 : LinearIndependent ℚ_[q] (fun i => φ (tl i) • v₀) := by
      have := hli.map' orb horb
      first
        | simpa only [Function.comp_def, hfb] using this
        | (simp only [Function.comp_def, hfb] at this; exact this)
    have hLI2 : LinearIndependent ℚ_[q] (fun i => ((q : ℚ_[q]) ^ k) • (φ (tl i) • v₀)) := by
      have hq : ((q : ℚ_[q]) ^ k) ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
      have := hLI1.map' (LinearMap.lsmul ℚ_[q] (RationalTateModule q J) ((q : ℚ_[q]) ^ k)) (LinearMap.ker_lsmul hq)
      simpa only [Function.comp_def, LinearMap.lsmul_apply] using this
    have hLI3 : LinearIndependent ℤ_[q] (fun i => ((q : ℚ_[q]) ^ k) • (φ (tl i) • v₀)) :=
      hLI2.restrict_scalars (by
        intro a b h
        simpa using h)
    simpa only [Function.comp_def, LinearMap.restrictScalars_apply, hcomp] using hLI3

end Core
p2m_reactivate "P2MW.S_ModularCurve_exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit.TateModule"

section Main

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  (hN : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ,
    (TateModule.rep q (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ - 1) * (TateModule.rep q (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ - 1) = 0)
  (ρ : ↥(heckeLatticeAlgebra p ∅) →+* Module.End ℤ_[q] (TateModule q (JZero p)))
  (hρ : letI := heckeModuleBar p
    ∀ t : HeckeAlg, ρ (((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t) = tateHeckeRep q (JZero p) t)

include hN hρ in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main :
    ∃ v : (TateModule q (JZero p)),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, TateModule.rep q (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v = v) ∧
      LinearIndependent ℤ_[q] (fun i => ρ (Module.Free.chooseBasis ℤ ↥(heckeLatticeAlgebra p ∅) i) v) := by
  classical
  letI instJ : Module HeckeAlg (JZero p) := heckeModuleBar p
  have hesurj : Function.Surjective ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) := surjective_e p

  obtain ⟨T₆, instCR, instAlg, φ, e₆, hspanφ, he₆⟩ :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two p q
      (ModularCurve.heckeInputsAll p) (ModularCurve.heckeOperatorsCommuteBar p)

  let b := Module.Free.chooseBasis ℤ ↥(heckeLatticeAlgebra p ∅)
  choose tl htl using fun i => hesurj (b i)

  obtain ⟨n, bΛ, -, -⟩ := ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top p
  haveI : Module.Free ℤ ↥(periodLattice p) := Module.Free.of_basis bΛ
  haveI : Module.Finite ℤ ↥(periodLattice p) := Module.Finite.of_basis bΛ
  have hLIΛ : LinearIndependent ℤ (fun i => periodLatticeHeckeEnd p (tl i)) := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    have h1 : periodLatticeHeckeEnd p (∑ j ∈ s, c j • tl j) = 0 := by
      rw [map_sum]
      simpa only [map_zsmul] using hc
    have h2 : heckeEvalForms p 2 (∑ j ∈ s, c j • tl j) = 0 :=
      heckeEvalForms_eq_zero_of_periodLatticeHeckeEnd_eq_zero p _ h1
    have h3 : ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (∑ j ∈ s, c j • tl j) = 0 := by
      show (latticeRestrictHom p ∅) (heckeEvalForms p 2 _) = 0
      rw [h2, map_zero]
    have h4 : ∑ j ∈ s, c j • b j = 0 := by
      rw [map_sum] at h3
      simpa only [map_zsmul, htl] using h3
    exact (linearIndependent_iff'.mp b.linearIndependent) s c h4 i hi
  have hLIW : LinearIndependent ℚ_[q]
      (fun i => ((periodLatticeHeckeEnd p (tl i)).baseChange ℚ_[q] :
        Module.End ℚ_[q] (ℚ_[q] ⊗[ℤ] ↥(periodLattice p)))) :=
    LinearIndependent.linearMap_baseChange_of_int ℚ_[q] ↥(periodLattice p) _ hLIΛ
  obtain ⟨Φ, hΦ⟩ := ModularCurve.exists_linearEquiv_rationalTateModule_tensor_periodLattice p q
  have hLIV : LinearIndependent ℚ_[q] (fun i => rationalHeckeRep q (JZero p) (tl i)) := by
    have hconj : ∀ i, (Φ.symm.conj) ((periodLatticeHeckeEnd p (tl i)).baseChange ℚ_[q]) =
        rationalHeckeRep q (JZero p) (tl i) := by
      intro i
      apply LinearMap.ext
      intro v
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, ← hΦ, LinearEquiv.symm_apply_apply]
    have := hLIW.map' (Φ.symm.conj : Module.End ℚ_[q] (ℚ_[q] ⊗[ℤ] ↥(periodLattice p)) →ₗ[ℚ_[q]] Module.End ℚ_[q] (RationalTateModule q (JZero p)))
      (LinearEquiv.ker _)
    simpa only [Function.comp_def, LinearEquiv.coe_coe, hconj] using this
  haveI : IsReduced ↥(heckeLatticeAlgebra p ∅) := CuspForm.isReduced_heckeLatticeAlgebra p
  exact core q (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥(heckeLatticeAlgebra p ∅) ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) hesurj ρ hρ tl htl hLIV
    T₆ φ e₆ hspanφ he₆ (fun σ t => (ModularCurve.tateModule_rep_comp_tateHeckeRep_comm p q σ t).2)
    (A.inertiaSubgroupIn ℚ : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) hN

end Main
p2m_reactivate "P2MW.S_ModularCurve_exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit.TateModule"

end HEART
p2m_reactivate "P2MW.S_ModularCurve_exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit.TateModule"

open HEART in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hN : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      (TateModule.rep q (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ - 1) *
        (TateModule.rep q (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ - 1) = 0)
    (ρ : ↥(heckeLatticeAlgebra p ∅) →+* Module.End ℤ_[q] (TateModule q (JZero p)))
    (hρ : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ρ (((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t) =
        tateHeckeRep q (JZero p) t) :
    ∃ v : TateModule q (JZero p),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
        TateModule.rep q (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v = v) ∧
      LinearIndependent ℤ_[q]
        (fun i => ρ (Module.Free.chooseBasis ℤ ↥(heckeLatticeAlgebra p ∅) i) v) :=
  HEART.main p q A hN ρ hρ

end S_ModularCurve_exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit
end P2MW
export P2MW.S_ModularCurve_exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit (solution)
