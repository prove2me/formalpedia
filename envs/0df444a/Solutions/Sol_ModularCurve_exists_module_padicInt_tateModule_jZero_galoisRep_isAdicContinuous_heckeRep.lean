-- Prove2me | solution 1 for ModularCurve.exists_module_padicInt_tateModule_jZero_galoisRep_isAdicContinuous_heckeRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/abc98410-851c-58bd-a256-9735dd70fa38

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_W54_jZeroPPowTorsion_factorsThroughFiniteLevel
import Theorems.Thm_W54_finite_free_tateModule
import Theorems.Thm_ModularCurve_natCard_torsion_jZero_eq_pow_finrank_periodLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_module_padicInt_tateModule_jZero_galoisRep_isAdicContinuous_heckeRep
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk"
p2m_attr_erase "simp" "ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve TensorProduct

noncomputable section

namespace InstC3

attribute [local instance] ModularCurve.heckeModuleBar

variable (M : ℕ) [NeZero M] (lam : ℕ) [Fact lam.Prime]

abbrev T : Type := ↥(ModularCurve.TateModule lam (JZero M))

omit [NeZero M] [Fact lam.Prime] in

theorem nsmul_eq_of_zmod_eq {A : Type} [AddCommMonoid A] {q n c d : ℕ} {m : A}
    (hm : q ^ n • m = 0) (h : (c : ZMod (q ^ n)) = d) : c • m = d • m := by
  have hmod : ∀ e : ℕ, e • m = (e % q ^ n) • m := fun e => by
    conv_lhs => rw [← Nat.div_add_mod e (q ^ n)]
    rw [add_smul, mul_comm, mul_smul, hm, smul_zero, zero_add]
  rw [hmod c, hmod d, (ZMod.natCast_eq_natCast_iff' c d _).1 h]

omit [Fact lam.Prime] in
theorem apply_zero (x : T M lam) : (x : ℕ → JZero M) 0 = 0 := x.2.1

omit [Fact lam.Prime] in
theorem compat (x : T M lam) (n : ℕ) : lam • (x : ℕ → JZero M) (n + 1) = (x : ℕ → JZero M) n :=
  x.2.2 n

omit [Fact lam.Prime] in
private theorem _root_.InstC3.pow_smul_apply (x : T M lam) (n : ℕ) : lam ^ n • (x : ℕ → JZero M) n = 0 :=
  ModularCurve.TateModule.pow_smul_apply x.2 n

p2m_export "InstC3" "pow_smul_apply"
omit [Fact lam.Prime] in
theorem compat_pow (x : T M lam) (n k : ℕ) :
    lam ^ n • (x : ℕ → JZero M) (n + k) = (x : ℕ → JZero M) k := by
  induction n with
  | zero => rw [pow_zero, one_smul, Nat.zero_add]
  | succ n ih =>
    rw [pow_succ, mul_smul, Nat.add_right_comm, compat, ih]

theorem cast_val_toZModPow (n : ℕ) (a : ℤ_[lam]) :
    (((PadicInt.toZModPow n a).val : ℕ) : ZMod (lam ^ n)) = PadicInt.toZModPow n a :=
  ZMod.natCast_zmod_val _

theorem val_succ_smul_eq (a : ℤ_[lam]) (x : T M lam) (n : ℕ) :
    (PadicInt.toZModPow (n + 1) a).val • (x : ℕ → JZero M) n =
      (PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n := by
  refine nsmul_eq_of_zmod_eq (pow_smul_apply M lam x n) ?_
  rw [cast_val_toZModPow, ZMod.natCast_val, ← ZMod.castHom_apply (R := ZMod (lam ^ n))
    (h := pow_dvd_pow lam n.le_succ), ← RingHom.comp_apply,
    PadicInt.zmod_cast_comp_toZModPow n (n + 1) n.le_succ]

@[reducible] def smulT : SMul ℤ_[lam] (T M lam) :=
  ⟨fun a x => ⟨fun n => (PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n,
    ⟨by simp only [apply_zero, smul_zero], fun n => by
      simp only
      rw [smul_comm, compat, val_succ_smul_eq]⟩⟩⟩

attribute [local instance] smulT

private theorem _root_.InstC3.smul_apply (a : ℤ_[lam]) (x : T M lam) (n : ℕ) :
    ((a • x : T M lam) : ℕ → JZero M) n = (PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n :=
  rfl

p2m_export "InstC3" "smul_apply"

@[reducible] def moduleT : Module ℤ_[lam] (T M lam) where
  one_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply]
    have h : (((PadicInt.toZModPow n (1 : ℤ_[lam])).val : ℕ) : ZMod (lam ^ n)) =
        ((1 : ℕ) : ZMod (lam ^ n)) := by
      rw [cast_val_toZModPow, map_one, Nat.cast_one]
    rw [nsmul_eq_of_zmod_eq (pow_smul_apply M lam x n) h, one_smul]
  mul_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, smul_apply, smul_apply, ← mul_smul]
    refine nsmul_eq_of_zmod_eq (pow_smul_apply M lam x n) ?_
    rw [cast_val_toZModPow, map_mul, Nat.cast_mul, cast_val_toZModPow, cast_val_toZModPow]
  smul_zero a := Subtype.ext (funext fun n => by
    rw [smul_apply]
    exact smul_zero _)
  smul_add a x y := Subtype.ext (funext fun n => by
    rw [smul_apply, Submodule.coe_add, Pi.add_apply]
    exact smul_add ((PadicInt.toZModPow n a).val) ((x : ℕ → JZero M) n) ((y : ℕ → JZero M) n))
  add_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, Submodule.coe_add, Pi.add_apply, smul_apply, smul_apply, ← add_smul]
    refine nsmul_eq_of_zmod_eq (pow_smul_apply M lam x n) ?_
    rw [cast_val_toZModPow, map_add, Nat.cast_add, cast_val_toZModPow, cast_val_toZModPow]
  zero_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, Submodule.coe_zero, Pi.zero_apply]
    have h : (((PadicInt.toZModPow n (0 : ℤ_[lam])).val : ℕ) : ZMod (lam ^ n)) =
        ((0 : ℕ) : ZMod (lam ^ n)) := by
      rw [cast_val_toZModPow, map_zero, Nat.cast_zero]
    rw [nsmul_eq_of_zmod_eq (pow_smul_apply M lam x n) h]
    exact zero_nsmul _

attribute [local instance] moduleT

theorem natCast_smul_apply (c : ℕ) (x : T M lam) (n : ℕ) :
    (((c : ℤ_[lam]) • x : T M lam) : ℕ → JZero M) n = c • (x : ℕ → JZero M) n := by
  rw [smul_apply]
  refine nsmul_eq_of_zmod_eq (pow_smul_apply M lam x n) ?_
  rw [cast_val_toZModPow, map_natCast]

theorem finite_torsion : Set.Finite {v : JZero M | lam • v = 0} := by
  have hcard := ModularCurve.natCard_torsion_jZero_eq_pow_finrank_periodLattice M lam
    (Fact.out : lam.Prime).ne_zero
  have hfin : Finite (AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar M) lam) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ (Fact.out : lam.Prime).ne_zero
  have hset : {v : JZero M | lam • v = 0} =
      (AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar M) lam :
        Set (JZero M)) := by
    ext v
    rw [Set.mem_setOf_eq, SetLike.mem_coe, AlgebraicCurve.Pic0.mem_torsion, natCast_zsmul]
  rw [hset]
  exact Set.toFinite _

theorem finite_free : Module.Finite ℤ_[lam] (T M lam) ∧ Module.Free ℤ_[lam] (T M lam) :=
  W54.finite_free_tateModule (smul_apply M lam) (finite_torsion M lam)

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def rho0Lin (σ : Γ) : T M lam →ₗ[ℤ_[lam]] T M lam where
  toFun x := ⟨σ • (x : ℕ → JZero M), ModularCurve.TateModule.smul_mem σ x.2⟩
  map_add' x y := Subtype.ext (smul_add σ (x : ℕ → JZero M) (y : ℕ → JZero M))
  map_smul' a x := by
    refine Subtype.ext (funext fun n => ?_)
    show σ • ((PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n) =
      (PadicInt.toZModPow n a).val • (σ • (x : ℕ → JZero M) n)
    exact (smul_comm _ _ _).symm

theorem coe_rho0Lin (σ : Γ) (x : T M lam) :
    ((rho0Lin M lam σ x : T M lam) : ℕ → JZero M) = σ • (x : ℕ → JZero M) := rfl

def rho0 : Γ →* Module.End ℤ_[lam] (T M lam) where
  toFun := rho0Lin M lam
  map_one' := LinearMap.ext fun x => Subtype.ext (one_smul Γ (x : ℕ → JZero M))
  map_mul' σ τ := LinearMap.ext fun x => Subtype.ext (mul_smul σ τ (x : ℕ → JZero M))

theorem coe_rho0 (σ : Γ) (x : T M lam) :
    ((rho0 M lam σ x : T M lam) : ℕ → JZero M) = σ • (x : ℕ → JZero M) := rfl

theorem exists_pow_smul_eq_of_apply_eq_zero (z : T M lam) (n : ℕ) (hz : (z : ℕ → JZero M) n = 0) :
    ∃ y : T M lam, ((lam : ℤ_[lam]) ^ n) • y = z := by
  refine ⟨⟨fun k => (z : ℕ → JZero M) (n + k), ⟨hz, fun k => compat M lam z (n + k)⟩⟩, ?_⟩
  refine Subtype.ext (funext fun k => ?_)
  rw [← Nat.cast_pow, natCast_smul_apply]
  exact compat_pow M lam z n k

def hecke0Lin (t : ModularCurve.HeckeAlg) : T M lam →ₗ[ℤ_[lam]] T M lam where
  toFun x := t • x
  map_add' x y := smul_add t x y
  map_smul' a x := by
    refine Subtype.ext (funext fun n => ?_)
    show t • ((PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n) =
      (PadicInt.toZModPow n a).val • (t • (x : ℕ → JZero M) n)
    exact smul_comm _ _ _

def hecke0 : ModularCurve.HeckeAlg →+* Module.End ℤ_[lam] (T M lam) where
  toFun := hecke0Lin M lam
  map_one' := LinearMap.ext fun x => show (1 : ModularCurve.HeckeAlg) • x = x from one_smul _ x
  map_mul' s t := LinearMap.ext fun x => show (s * t) • x = s • (t • x) from mul_smul s t x
  map_zero' := LinearMap.ext fun x => show (0 : ModularCurve.HeckeAlg) • x = 0 from zero_smul _ x
  map_add' s t := LinearMap.ext fun x => show (s + t) • x = s • x + t • x from add_smul s t x

theorem hecke0_apply (t : ModularCurve.HeckeAlg) (x : T M lam) : hecke0 M lam t x = t • x := rfl

variable (O'' : Type) [CommRing O''] [IsLocalRing O''] [Algebra ℤ_[lam] O'']

def rhoM : Γ →* Module.End O'' (O'' ⊗[ℤ_[lam]] T M lam) where
  toFun σ := (rho0 M lam σ).baseChange O''
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' σ τ := by rw [map_mul, LinearMap.baseChange_mul]

omit [IsLocalRing O''] in
theorem rhoM_tmul (σ : Γ) (a : O'') (x : T M lam) :
    rhoM M lam O'' σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] rho0 M lam σ x :=
  LinearMap.baseChange_tmul _ _ _

def heckeM : ModularCurve.HeckeAlg →+* Module.End O'' (O'' ⊗[ℤ_[lam]] T M lam) where
  toFun t := (hecke0 M lam t).baseChange O''
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' s t := by rw [map_mul, LinearMap.baseChange_mul]
  map_zero' := by rw [map_zero, LinearMap.baseChange_zero]
  map_add' s t := by rw [map_add, LinearMap.baseChange_add]

omit [IsLocalRing O''] in
theorem heckeM_tmul (t : ModularCurve.HeckeAlg) (a : O'') (x : T M lam) :
    heckeM M lam O'' t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x) :=
  LinearMap.baseChange_tmul _ _ _

set_option maxHeartbeats 6400000 in

theorem rhoM_isAdicContinuous (hlam : (lam : O'') ∈ IsLocalRing.maximalIdeal O'') :
    GaloisActionIsAdicContinuous O'' (rhoM M lam O'') := by
  intro n
  obtain ⟨L, hL, hfix⟩ := W54.jZeroPPowTorsion_factorsThroughFiniteLevel M lam Fact.out n
  refine ⟨L, hL, fun σ hσ v => ?_⟩

  have key : ∀ x : T M lam, ∃ y : T M lam, ((lam : ℤ_[lam]) ^ n) • y = rho0 M lam σ x - x := by
    intro x
    apply exists_pow_smul_eq_of_apply_eq_zero
    rw [Submodule.coe_sub, Pi.sub_apply, coe_rho0, Pi.smul_apply, sub_eq_zero]
    refine hfix σ hσ _ (AlgebraicCurve.Pic0.mem_torsion.mpr ?_)
    rw [natCast_zsmul]
    exact pow_smul_apply M lam x n
  have hmem : ∀ (a : O'') (x : T M lam),
      rhoM M lam O'' σ (a ⊗ₜ[ℤ_[lam]] x) - a ⊗ₜ[ℤ_[lam]] x ∈
        (IsLocalRing.maximalIdeal O'' ^ n) • (⊤ : Submodule O'' (O'' ⊗[ℤ_[lam]] T M lam)) := by
    intro a x
    obtain ⟨y, hy⟩ := key x
    have hsub : a ⊗ₜ[ℤ_[lam]] (rho0 M lam σ x - x) =
        a ⊗ₜ[ℤ_[lam]] rho0 M lam σ x - a ⊗ₜ[ℤ_[lam]] x :=
      map_sub (TensorProduct.mk ℤ_[lam] O'' (T M lam) a) _ _
    rw [rhoM_tmul, ← hsub, ← hy, TensorProduct.tmul_smul,
      ← algebraMap_smul O'' ((lam : ℤ_[lam]) ^ n) (a ⊗ₜ[ℤ_[lam]] y), map_pow, map_natCast]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hlam n) Submodule.mem_top
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
  | tmul a x => exact hmem a x
  | add x y hx hy =>
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hx hy

end InstC3

end

theorem solution
    (M : ℕ) [NeZero M] (lam : ℕ) [Fact lam.Prime] :
    letI := ModularCurve.heckeModuleBar M
    ∃ (_ : Module ℤ_[lam] (ModularCurve.TateModule lam (JZero M))),
      (∀ (a : ℤ_[lam]) (x : ModularCurve.TateModule lam (JZero M)) (n : ℕ),
        ((a • x : ModularCurve.TateModule lam (JZero M)) : ℕ → JZero M) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n) ∧
      Module.Finite ℤ_[lam] (ModularCurve.TateModule lam (JZero M)) ∧
      Module.Free ℤ_[lam] (ModularCurve.TateModule lam (JZero M)) ∧
      ∀ (O'' : Type) [CommRing O''] [IsLocalRing O''] [Algebra ℤ_[lam] O''],
        (lam : O'') ∈ IsLocalRing.maximalIdeal O'' →
        ∃ (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M)))
          (TM : ModularCurve.HeckeAlg →+*
              Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M))),
          (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
              (x y : ModularCurve.TateModule lam (JZero M)),
            (y : ℕ → JZero M) = σ • (x : ℕ → JZero M) →
              ∀ a : O'', ρM σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] y) ∧
          GaloisActionIsAdicContinuous O'' ρM ∧
          (∀ (t : ModularCurve.HeckeAlg) (a : O'') (x : ModularCurve.TateModule lam (JZero M)),
            TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x)) := by
  letI := ModularCurve.heckeModuleBar M
  letI : Module ℤ_[lam] (ModularCurve.TateModule lam (JZero M)) := InstC3.moduleT M lam
  refine ⟨InstC3.moduleT M lam, InstC3.smul_apply M lam, (InstC3.finite_free M lam).1,
    (InstC3.finite_free M lam).2, ?_⟩
  intro O'' _ _ _ hlam
  refine ⟨InstC3.rhoM M lam O'', InstC3.heckeM M lam O'', ?_, InstC3.rhoM_isAdicContinuous M lam O'' hlam,
    InstC3.heckeM_tmul M lam O''⟩
  intro σ x y hxy a
  rw [InstC3.rhoM_tmul]
  congr 1
  exact Subtype.ext hxy.symm

end S_ModularCurve_exists_module_padicInt_tateModule_jZero_galoisRep_isAdicContinuous_heckeRep
end P2MW
export P2MW.S_ModularCurve_exists_module_padicInt_tateModule_jZero_galoisRep_isAdicContinuous_heckeRep (solution)
