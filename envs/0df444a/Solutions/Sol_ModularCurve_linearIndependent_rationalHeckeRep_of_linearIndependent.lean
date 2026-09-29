-- Prove2me | solution 1 for ModularCurve.linearIndependent_rationalHeckeRep_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/996d6d66-610f-5c9c-9a4d-5f9860272235

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
import Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_linearIndependent_rationalHeckeRep_of_linearIndependent
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

open scoped TensorProduct

noncomputable section

namespace W7U

open ModularCurve

section LinAlg

theorem linearIndependent_of_ker_le {R M M₁ M₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (f : M →ₗ[R] M₁) (g : M →ₗ[R] M₂) (hker : ∀ m, f m = 0 → g m = 0)
    {ι : Type*} (v : ι → M) (h : LinearIndependent R (fun i => g (v i))) :
    LinearIndependent R (fun i => f (v i)) := by
  rw [linearIndependent_iff] at h ⊢
  intro l hl
  apply h l
  have h1 : Finsupp.linearCombination R (fun i => f (v i)) l = f (Finsupp.linearCombination R v l) :=
    (Finsupp.apply_linearCombination R f v l).symm
  have h2 : Finsupp.linearCombination R (fun i => g (v i)) l = g (Finsupp.linearCombination R v l) :=
    (Finsupp.apply_linearCombination R g v l).symm
  rw [h2]
  exact hker _ (h1 ▸ hl)

variable {n : ℕ}

def flat (K : Type) [CommRing K] : Matrix (Fin n) (Fin n) K →ₗ[K] (Fin n × Fin n → K) where
  toFun A := fun ij => A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_flat (K : Type) [CommRing K] : LinearMap.ker (flat (n := n) K) = ⊥ := by
  refine LinearMap.ker_eq_bot.mpr ?_
  intro A B h
  ext i j
  exact congrFun h (i, j)

theorem linearIndependent_padic_of_int (p : ℕ) [Fact p.Prime] {ι : Type*}
    (v : ι → Matrix (Fin n) (Fin n) ℤ) (hv : LinearIndependent ℤ v) :
    LinearIndependent ℚ_[p] (fun i => (v i).map (Int.cast : ℤ → ℚ_[p])) := by
  have h1 : LinearIndependent ℤ (fun i => flat ℤ (v i)) := hv.map' (flat ℤ) (ker_flat ℤ)
  have h2 : LinearIndependent ℚ_[p] (fun i => (algebraMap ℤ ℚ_[p]) ∘ (flat ℤ (v i))) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ_[p])).mpr h1
  have h3 : (fun i => (algebraMap ℤ ℚ_[p]) ∘ (flat ℤ (v i))) =
      fun i => flat ℚ_[p] ((v i).map (Int.cast : ℤ → ℚ_[p])) := by
    funext i; funext ij; simp [flat]
  rw [h3] at h2
  exact LinearIndependent.of_comp (flat ℚ_[p]) h2

end LinAlg

section Tate

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
variable {Λ : Type} [AddCommGroup Λ] (ρΛ : HeckeAlg →+* Module.End ℤ Λ)
variable {n : ℕ} (bΛ : Module.Basis (Fin n) ℤ Λ)

def M : HeckeAlg →+* Matrix (Fin n) (Fin n) ℤ :=
  (LinearMap.toMatrixAlgEquiv bΛ).toRingEquiv.toRingHom.comp ρΛ

theorem M_apply (t : HeckeAlg) : M ρΛ bΛ t = LinearMap.toMatrix bΛ bΛ (ρΛ t) := rfl

def Mp : HeckeAlg →+* Matrix (Fin n) (Fin n) ℚ_[p] :=
  ((Int.castRingHom ℚ_[p]).mapMatrix).comp (M ρΛ bΛ)

theorem Mp_apply (t : HeckeAlg) : Mp p ρΛ bΛ t = (M ρΛ bΛ t).map (Int.cast : ℤ → ℚ_[p]) := rfl

variable (e₁ : TateModule p J ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] Λ)

def E1 : RationalTateModule p J ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] Λ) :=
  e₁.baseChange ℤ_[p] ℚ_[p] _ _

def E2 : ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] Λ) ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ] Λ :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℤ_[p] ℚ_[p] ℚ_[p] Λ

def E3 : ℚ_[p] ⊗[ℤ] Λ ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
  (Algebra.TensorProduct.basis ℚ_[p] bΛ).equivFun

def E : RationalTateModule p J ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
  (E1 p J e₁).trans ((E2 p).trans (E3 p bΛ))

theorem E1_equivariant (t : HeckeAlg)
    (he : ∀ t x, e₁ (tateHeckeRep p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x))
    (v : RationalTateModule p J) :
    E1 p J e₁ (rationalHeckeRep p J t v) =
      ((ρΛ t).baseChange ℤ_[p]).baseChange ℚ_[p] (E1 p J e₁ v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp [E1, rationalHeckeRep_tmul, LinearEquiv.baseChange, he]
  | add x y hx hy => simp [map_add, hx, hy]

theorem E2_equivariant (t : HeckeAlg) (v : ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] Λ)) :
    E2 p (((ρΛ t).baseChange ℤ_[p]).baseChange ℚ_[p] v) = (ρΛ t).baseChange ℚ_[p] (E2 p v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y => simp [E2]
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add]
  | add x y hx hy => simp [map_add, hx, hy]

theorem E3_equivariant (t : HeckeAlg) (v : ℚ_[p] ⊗[ℤ] Λ) :
    E3 p bΛ ((ρΛ t).baseChange ℚ_[p] v) = (Mp p ρΛ bΛ t).mulVec (E3 p bΛ v) := by
  have h := LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis ℚ_[p] bΛ)
    (Algebra.TensorProduct.basis ℚ_[p] bΛ) ((ρΛ t).baseChange ℚ_[p]) v
  rw [LinearMap.toMatrix_baseChange] at h
  simp only [E3, Module.Basis.equivFun_apply]
  rw [← h]
  congr 1

theorem E_equivariant
    (he : ∀ t x, e₁ (tateHeckeRep p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x))
    (t : HeckeAlg) (v : RationalTateModule p J) :
    E p J bΛ e₁ (rationalHeckeRep p J t v) = (Mp p ρΛ bΛ t).mulVec (E p J bΛ e₁ v) := by
  simp only [E, LinearEquiv.trans_apply]
  rw [E1_equivariant p J ρΛ e₁ t he, E2_equivariant, E3_equivariant]

def Δ : Module.End ℚ_[p] (RationalTateModule p J) →ₗ[ℚ_[p]] Matrix (Fin n) (Fin n) ℚ_[p] :=
  (LinearMap.toMatrix' : ((Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p])) ≃ₗ[ℚ_[p]] _).toLinearMap ∘ₗ
    ((E p J bΛ e₁).conj : Module.End ℚ_[p] (RationalTateModule p J) ≃ₗ[ℚ_[p]] _).toLinearMap

omit [Module HeckeAlg J] in
theorem Δ_apply (f : Module.End ℚ_[p] (RationalTateModule p J)) :
    Δ p J bΛ e₁ f =
      LinearMap.toMatrix' (((E p J bΛ e₁).toLinearMap ∘ₗ f) ∘ₗ (E p J bΛ e₁).symm.toLinearMap) := by
  simp only [Δ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.conj_apply]

theorem Δ_rationalHeckeRep
    (he : ∀ t x, e₁ (tateHeckeRep p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x)) (t : HeckeAlg) :
    Δ p J bΛ e₁ (rationalHeckeRep p J t) = Mp p ρΛ bΛ t := by
  have hconj : ((E p J bΛ e₁).toLinearMap ∘ₗ rationalHeckeRep p J t) ∘ₗ (E p J bΛ e₁).symm.toLinearMap
      = Matrix.toLin' (Mp p ρΛ bΛ t) := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Matrix.toLin'_apply]
    rw [E_equivariant p J ρΛ bΛ e₁ he, LinearEquiv.apply_symm_apply]
  rw [Δ_apply, hconj, LinearMap.toMatrix'_toLin']

theorem linearIndependent_rationalHeckeRep_of_matrix
    (he : ∀ t x, e₁ (tateHeckeRep p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x))
    {ι : Type*} (t : ι → HeckeAlg)
    (h : LinearIndependent ℚ_[p] (fun i => Mp p ρΛ bΛ (t i))) :
    LinearIndependent ℚ_[p] (fun i => rationalHeckeRep p J (t i)) := by
  have h' : LinearIndependent ℚ_[p] (fun i => Δ p J bΛ e₁ (rationalHeckeRep p J (t i))) := by
    have hfun : (fun i => Δ p J bΛ e₁ (rationalHeckeRep p J (t i))) = fun i => Mp p ρΛ bΛ (t i) := by
      funext i; exact Δ_rationalHeckeRep p J ρΛ bΛ e₁ he (t i)
    rw [hfun]; exact h
  exact LinearIndependent.of_comp (Δ p J bΛ e₁) h'

end Tate

section Annih

variable (N : ℕ) [NeZero N]

abbrev D := Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)

theorem dualHeckeRep_eq_zero_of_span {n : ℕ} (c : Fin n → D N)
    (hsp : Submodule.span ℝ (Set.range c) = ⊤) (s : HeckeAlg)
    (hs : ∀ i, dualHeckeRep N s (c i) = 0) : dualHeckeRep N s = 0 := by
  have h : (dualHeckeRep N s).restrictScalars ℝ = (0 : Module.End ℂ (D N)).restrictScalars ℝ := by
    apply LinearMap.ext_on_range hsp
    intro i
    rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, LinearMap.zero_apply]
    exact hs i
  apply LinearMap.ext
  intro φ
  have := LinearMap.congr_fun h φ
  simpa using this

theorem uniformization_heckeEvalBar (hcomm : HeckeOperatorsCommuteBar N)
    (u : JZero N →+ (D N ⧸ periodLattice N))
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ))
    (t : HeckeAlg) :
    ∀ (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeEvalBar hcomm t x) = Submodule.Quotient.mk (dualHeckeRep N t φ) := by
  induction t using MvPolynomial.induction_on with
  | C a =>
      intro x φ hx
      rw [heckeEvalBar_C, Module.End.intCast_apply, map_zsmul, hx, dualHeckeRep_C]
      exact (map_zsmul (Submodule.mkQ (periodLattice N)) a φ).symm
  | add s t hs ht =>
      intro x φ hx
      rw [RingHom.map_add, LinearMap.add_apply, u.map_add, hs x φ hx, ht x φ hx, RingHom.map_add,
        LinearMap.add_apply, Submodule.Quotient.mk_add]
  | mul_X q ℓ hq =>
      intro x φ hx
      have hX : (MvPolynomial.X ℓ : HeckeAlg) = heckeGen ℓ := rfl
      rw [RingHom.map_mul, Module.End.mul_apply, hX, heckeEvalBar_heckeGen, RingHom.map_mul,
        Module.End.mul_apply]
      exact hq _ _ (hu ℓ x φ hx)

theorem heckeEvalBar_eq_zero_of_periodLatticeHeckeEnd_eq_zero
    (hcomm : HeckeOperatorsCommuteBar N) (hst : PeriodLatticeHeckeStable N)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
    (u : JZero N →+ (D N ⧸ periodLattice N)) (hinj : Function.Injective u)
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ))
    (s : HeckeAlg) (hs : periodLatticeHeckeEnd N s = 0) (x : JZero N) :
    heckeEvalBar hcomm s x = 0 := by

  have hD : dualHeckeRep N s = 0 := by
    refine dualHeckeRep_eq_zero_of_span N (fun i => ((b i : periodLattice N) : D N)) hsp s ?_
    intro i
    rw [← coe_periodLatticeHeckeEnd_apply hst s (b i), hs, LinearMap.zero_apply,
      Submodule.coe_zero]

  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective (periodLattice N) (u x)
  have h1 : u (heckeEvalBar hcomm s x) = 0 := by
    rw [uniformization_heckeEvalBar N hcomm u hu s x φ hφ.symm, hD, LinearMap.zero_apply,
      Submodule.Quotient.mk_zero]
  exact hinj (h1.trans u.map_zero.symm)

theorem linearIndependent_M_of
    (hcomm : HeckeOperatorsCommuteBar N) (hst : PeriodLatticeHeckeStable N)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
    (u : JZero N →+ (D N ⧸ periodLattice N)) (hinj : Function.Injective u)
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ))
    {ι : Type} (t : ι → HeckeAlg)
    (hli : letI := ModularCurve.heckeModuleBar N
      LinearIndependent ℤ (fun i =>
        Ideal.Quotient.mk (Module.annihilator HeckeAlg (JZero N)) (t i))) :
    LinearIndependent ℤ (fun i => M (periodLatticeHeckeEnd N) b (t i)) := by
  letI := ModularCurve.heckeModuleBar N

  let f : HeckeAlg →ₗ[ℤ] Matrix (Fin n) (Fin n) ℤ :=
    (M (periodLatticeHeckeEnd N) b).toAddMonoidHom.toIntLinearMap
  let g : HeckeAlg →ₗ[ℤ] (HeckeAlg ⧸ Module.annihilator HeckeAlg (JZero N)) :=
    (Ideal.Quotient.mk (Module.annihilator HeckeAlg (JZero N))).toAddMonoidHom.toIntLinearMap
  have hker : ∀ s, f s = 0 → g s = 0 := by
    intro s hs
    have hs' : periodLatticeHeckeEnd N s = 0 :=
      (LinearMap.toMatrix b b).map_eq_zero_iff.mp hs
    show Ideal.Quotient.mk (Module.annihilator HeckeAlg (JZero N)) s = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
    intro x
    rw [heckeModuleBar_smul_def hcomm]
    exact heckeEvalBar_eq_zero_of_periodLatticeHeckeEnd_eq_zero N hcomm hst b hsp u hinj hu s hs' x
  have hli' : LinearIndependent ℤ (fun i => g (t i)) := by
    first | exact hli | (convert hli using 1; funext i; rfl)
  exact linearIndependent_of_ker_le f g hker t hli'

end Annih

section Main

set_option maxHeartbeats 1600000 in
theorem main (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    {ι : Type} (t : ι → ModularCurve.HeckeAlg)
    (hli : letI := ModularCurve.heckeModuleBar N
      LinearIndependent ℤ (fun i =>
        Ideal.Quotient.mk (Module.annihilator ModularCurve.HeckeAlg (ModularCurve.JZero N)) (t i))) :
    letI := ModularCurve.heckeModuleBar N
    LinearIndependent ℚ_[p]
      (fun i => ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) (t i)) := by
  letI := ModularCurve.heckeModuleBar N

  have hst : PeriodLatticeHeckeStable N := ModularCurve.periodLatticeHeckeStable N
  obtain ⟨n, b, -, hsp⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  obtain ⟨u, hinj, -, hu⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice N hin hst
  obtain ⟨e₁, he₁⟩ :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
      N p hin hcomm hst

  have hM : LinearIndependent ℤ (fun i => M (periodLatticeHeckeEnd N) b (t i)) :=
    linearIndependent_M_of N hcomm hst b hsp u hinj hu t hli

  have hMp : LinearIndependent ℚ_[p] (fun i => Mp p (periodLatticeHeckeEnd N) b (t i)) :=
    linearIndependent_padic_of_int p _ hM

  exact linearIndependent_rationalHeckeRep_of_matrix p (JZero N) (periodLatticeHeckeEnd N) b e₁ he₁ t hMp

end Main

end W7U

end

theorem solution (N p : ℕ) [NeZero N]
    [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    {ι : Type} (t : ι → ModularCurve.HeckeAlg)
    (hli : letI := ModularCurve.heckeModuleBar N
      LinearIndependent ℤ (fun i =>
        Ideal.Quotient.mk (Module.annihilator ModularCurve.HeckeAlg (ModularCurve.JZero N)) (t i))) :
    letI := ModularCurve.heckeModuleBar N
    LinearIndependent ℚ_[p]
      (fun i => ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) (t i)) :=
  W7U.main N p hin hcomm t hli

end S_ModularCurve_linearIndependent_rationalHeckeRep_of_linearIndependent
end P2MW
export P2MW.S_ModularCurve_linearIndependent_rationalHeckeRep_of_linearIndependent (solution)
