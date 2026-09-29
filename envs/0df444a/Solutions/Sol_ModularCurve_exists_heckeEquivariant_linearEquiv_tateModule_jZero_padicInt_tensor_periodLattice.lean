-- Prove2me | solution 1 for ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/86300a83-c11e-5e90-b390-5cf1057403c3

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct

namespace W5ITatePeriod

section Functorial

variable {p : ℕ} [Fact p.Prime] {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M']
  [AddCommGroup M'']

def tateMap (p : ℕ) [Fact p.Prime] (f : M →+ M') : TateModule p M →ₗ[ℤ_[p]] TateModule p M' where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule p M) : ℕ → M) n) = f ((x : ℕ → M) n) + f ((y : ℕ → M) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    show f (((a • x : TateModule p M) : ℕ → M) n) =
      (((a • (⟨fun n => f ((x : ℕ → M) n), _⟩ : TateModule p M')) : TateModule p M') : ℕ → M') n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem coe_tateMap_apply (f : M →+ M') (x : TateModule p M) (n : ℕ) :
    ((tateMap p f x : TateModule p M') : ℕ → M') n = f ((x : ℕ → M) n) := rfl

theorem tateMap_comp_apply (f : M →+ M') (g : M' →+ M'') (x : TateModule p M) :
    tateMap p (g.comp f) x = tateMap p g (tateMap p f x) :=
  Subtype.ext (funext fun _ => rfl)

theorem tateMap_injective (f : M →+ M') (hf : Function.Injective f) :
    Function.Injective (tateMap p f) := by
  intro x y h
  refine Subtype.ext (funext fun n => hf ?_)
  exact congrArg (fun z : TateModule p M' => (z : ℕ → M') n) h

theorem tateMap_surjective (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ y : M', IsOfFinAddOrder y → y ∈ f.range) :
    Function.Surjective (tateMap p f) := by
  intro y
  have hfin : ∀ n, IsOfFinAddOrder ((y : ℕ → M') n) := fun n => by
    refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ]
    exact TateModule.torsion y n
  choose x hx using fun n => (AddMonoidHom.mem_range).1 (hsurj _ (hfin n))
  refine ⟨⟨x, fun n => ⟨hf ?_, hf ?_⟩⟩, Subtype.ext (funext fun n => hx n)⟩
  · rw [map_zsmul, hx, map_zero, TateModule.torsion]
  · rw [map_zsmul, hx, hx, TateModule.compat]

def tateEquivOfInjective (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ y : M', IsOfFinAddOrder y → y ∈ f.range) :
    TateModule p M ≃ₗ[ℤ_[p]] TateModule p M' :=
  LinearEquiv.ofBijective (tateMap p f) ⟨tateMap_injective f hf, tateMap_surjective f hf hsurj⟩

@[scoped simp] theorem tateEquivOfInjective_apply (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ y : M', IsOfFinAddOrder y → y ∈ f.range) (x : TateModule p M) :
    tateEquivOfInjective f hf hsurj x = tateMap p f x := rfl

theorem tateMap_naturality (u : M →+ M') (S : M →+ M) (T : M' →+ M')
    (h : ∀ m, u (S m) = T (u m)) (x : TateModule p M) :
    tateMap p u (tateMap p S x) = tateMap p T (tateMap p u x) :=
  Subtype.ext (funext fun n => h _)

end Functorial

section Torus

open Module

variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V]
variable (K) (p : ℕ) [Fact p.Prime] (Λ : Submodule ℤ V)

theorem natCast_ne_zero_K : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero

def divLevel (n : ℕ) : V →+ V ⧸ Λ where
  toFun v := Submodule.Quotient.mk ((((p : K) ^ n)⁻¹) • v)
  map_zero' := by rw [smul_zero, Submodule.Quotient.mk_zero]
  map_add' v w := by rw [smul_add, Submodule.Quotient.mk_add]

theorem divLevel_apply (n : ℕ) (v : V) :
    divLevel K p Λ n v = Submodule.Quotient.mk ((((p : K) ^ n)⁻¹) • v) := rfl

theorem natCast_pow_zsmul_eq (n : ℕ) (v : V) : (((p ^ n : ℕ) : ℤ) • v) = ((p : K) ^ n) • v := by
  rw [Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul K, Nat.cast_pow]

theorem natCast_zsmul_eq (v : V) : (((p : ℕ) : ℤ) • v) = (p : K) • v := by
  rw [Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul K]

@[scoped simp] theorem divLevel_natCast_pow_smul (n : ℕ) (v : V) :
    divLevel K p Λ n (((p ^ n : ℕ) : ℤ) • v) = Submodule.Quotient.mk v := by
  rw [divLevel_apply, natCast_pow_zsmul_eq K p, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero n (natCast_ne_zero_K K p)), one_smul]

theorem divLevel_succ_natCast_smul (n : ℕ) (v : V) :
    divLevel K p Λ (n + 1) (((p : ℕ) : ℤ) • v) = divLevel K p Λ n v := by
  rw [divLevel_apply, divLevel_apply, natCast_zsmul_eq K p, smul_smul, pow_succ, mul_inv,
    inv_mul_cancel_right₀ (natCast_ne_zero_K K p)]

theorem divLevel_zero (v : V) : divLevel K p Λ 0 v = Submodule.Quotient.mk v := by
  rw [divLevel_apply, pow_zero, inv_one, one_smul]

theorem divLevel_coe_eq_of_eq_add (n : ℕ) (l₁ l₂ μ : Λ) (h : l₁ = l₂ + ((p ^ n : ℕ) : ℤ) • μ) :
    divLevel K p Λ n (l₁ : V) = divLevel K p Λ n (l₂ : V) := by
  rw [h, Submodule.coe_add, Submodule.coe_smul, map_add, divLevel_natCast_pow_smul,
    (Submodule.Quotient.mk_eq_zero Λ).2 μ.2, add_zero]

def iota : Λ →ₗ[ℤ] TateModule p (V ⧸ Λ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun l => ⟨fun n => divLevel K p Λ n (l : V), fun n =>
        ⟨by rw [← map_zsmul, divLevel_natCast_pow_smul, (Submodule.Quotient.mk_eq_zero Λ).2 l.2],
         by rw [← map_zsmul, divLevel_succ_natCast_smul]⟩⟩
      map_zero' := Subtype.ext (funext fun n => by
        show divLevel K p Λ n ((0 : Λ) : V) = ((0 : TateModule p (V ⧸ Λ)) : ℕ → V ⧸ Λ) n
        rw [Submodule.coe_zero, map_zero, TateModule.coe_zero, Pi.zero_apply])
      map_add' := fun l m => Subtype.ext (funext fun n => by
        show divLevel K p Λ n ((l + m : Λ) : V) = divLevel K p Λ n (l : V) + divLevel K p Λ n (m : V)
        rw [Submodule.coe_add, map_add]) }

@[scoped simp] theorem coe_iota_apply (l : Λ) (n : ℕ) :
    ((iota K p Λ l : TateModule p (V ⧸ Λ)) : ℕ → V ⧸ Λ) n = divLevel K p Λ n (l : V) := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ Λ)

def psi : (ι → ℤ_[p]) →ₗ[ℤ_[p]] TateModule p (V ⧸ Λ) :=
  ∑ i, (LinearMap.proj i : (ι → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]).smulRight (iota K p Λ (b i))

theorem psi_apply (c : ι → ℤ_[p]) : psi K p Λ b c = ∑ i, c i • iota K p Λ (b i) := by
  simp only [psi, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]

def lam (c : ι → ℤ_[p]) (n : ℕ) : Λ := ∑ i, (((c i).appr n : ℕ) : ℤ) • b i

theorem coe_psi_apply (c : ι → ℤ_[p]) (n : ℕ) :
    ((psi K p Λ b c : TateModule p (V ⧸ Λ)) : ℕ → V ⧸ Λ) n = divLevel K p Λ n (lam p Λ b c n : V) := by
  rw [psi_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, lam, Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TateModule.smul_apply, coe_iota_apply, ← map_zsmul, Submodule.coe_smul]

theorem equivFun_lam (c : ι → ℤ_[p]) (n : ℕ) (i : ι) :
    b.equivFun (lam p Λ b c n) i = (((c i).appr n : ℕ) : ℤ) := by
  have : lam p Λ b c n = b.equivFun.symm fun i => (((c i).appr n : ℕ) : ℤ) := by
    rw [Basis.equivFun_symm_apply]; rfl
  rw [this, LinearEquiv.apply_symm_apply]

theorem exists_eq_smul_of_divLevel_eq_zero (n : ℕ) (l : Λ)
    (h : divLevel K p Λ n (l : V) = 0) : ∃ μ : Λ, l = ((p ^ n : ℕ) : ℤ) • μ := by
  rw [divLevel_apply, Submodule.Quotient.mk_eq_zero] at h
  refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
  rw [Submodule.coe_smul, natCast_pow_zsmul_eq K p, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero n (natCast_ne_zero_K K p)), one_smul]

theorem psi_injective : Function.Injective (psi K p Λ b) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  funext i
  refine (PadicInt.ext_of_toZModPow).1 fun n => ?_
  rw [Pi.zero_apply, map_zero, TateModule.toZModPow_eq_appr]
  have hn : ((psi K p Λ b c : TateModule p (V ⧸ Λ)) : ℕ → V ⧸ Λ) n = 0 := by
    rw [hc, TateModule.coe_zero, Pi.zero_apply]
  rw [coe_psi_apply] at hn
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_divLevel_eq_zero K p Λ n _ hn
  have hi := equivFun_lam p Λ b c n i
  rw [hμ, map_zsmul, Pi.smul_apply, smul_eq_mul] at hi
  have : (((((c i).appr n : ℕ) : ℤ)) : ZMod (p ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨_, hi.symm⟩
  rwa [Int.cast_natCast] at this

theorem psi_surjective : Function.Surjective (psi K p Λ b) := by
  intro x
  have hp : p.Prime := Fact.out

  choose v hv using fun n => Submodule.Quotient.mk_surjective Λ ((x : ℕ → V ⧸ Λ) n)

  have hΛ : ∀ n, (((p ^ n : ℕ) : ℤ) • v n) ∈ Λ := fun n => by
    rw [← Submodule.Quotient.mk_eq_zero]
    change Submodule.mkQ Λ (((p ^ n : ℕ) : ℤ) • v n) = 0
    rw [map_zsmul, Submodule.mkQ_apply, hv]
    exact TateModule.torsion x n

  have hδ : ∀ n, (((p : ℕ) : ℤ) • v (n + 1) - v n) ∈ Λ := fun n => by
    rw [← Submodule.Quotient.eq]
    change Submodule.mkQ Λ (((p : ℕ) : ℤ) • v (n + 1)) = Submodule.Quotient.mk (v n)
    rw [map_zsmul, Submodule.mkQ_apply, hv, hv]
    exact TateModule.compat x n
  set L : ℕ → Λ := fun n => ⟨_, hΛ n⟩ with hL
  set δ : ℕ → Λ := fun n => ⟨_, hδ n⟩ with hδdef
  have hLsucc : ∀ n, L (n + 1) = L n + ((p ^ n : ℕ) : ℤ) • δ n := fun n => by
    refine Subtype.ext ?_
    simp only [hL, hδdef, Submodule.coe_add, Submodule.coe_smul, smul_sub, smul_smul]
    push_cast
    rw [pow_succ, add_sub_cancel]
  set a : ℕ → ι → ℤ := fun n => b.equivFun (L n) with ha
  have hdvd : ∀ i n, (p : ℤ) ^ n ∣ a (n + 1) i - a n i := fun i n => by
    refine ⟨b.equivFun (δ n) i, ?_⟩
    rw [ha]
    dsimp only
    rw [hLsucc, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left,
      Nat.cast_pow]
  let c : ι → ℤ_[p] := fun i =>
    PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => a n i) p (hdvd i))
  have hc : ∀ i n, PadicInt.toZModPow n (c i) = (a n i : ZMod (p ^ n)) := fun i n =>
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => a n i) p (hdvd i) n
  refine ⟨c, Subtype.ext (funext fun n => ?_)⟩
  rw [coe_psi_apply, ← hv, ← divLevel_natCast_pow_smul K p Λ n (v n)]
  change divLevel K p Λ n (lam p Λ b c n : V) = divLevel K p Λ n (L n : V)

  have hcoef : ∀ i, ∃ e : ℤ, (((c i).appr n : ℕ) : ℤ) - a n i = ((p ^ n : ℕ) : ℤ) * e := fun i => by
    have h1 : ((a n i : ℤ) : ZMod (p ^ n)) = ((((c i).appr n : ℕ) : ℤ) : ZMod (p ^ n)) := by
      rw [Int.cast_natCast, ← TateModule.toZModPow_eq_appr, hc]
    obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
    exact ⟨e, he⟩
  choose e he using hcoef
  refine divLevel_coe_eq_of_eq_add K p Λ n _ _ (∑ i, e i • b i) ?_
  apply b.equivFun.injective
  funext i
  rw [equivFun_lam, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    ← sub_eq_iff_eq_add', he]
  congr 1
  have : (∑ j, e j • b j) = b.equivFun.symm e := (Basis.equivFun_symm_apply b e).symm
  rw [this, LinearEquiv.apply_symm_apply]

def psiEquiv : (ι → ℤ_[p]) ≃ₗ[ℤ_[p]] TateModule p (V ⧸ Λ) :=
  LinearEquiv.ofBijective (psi K p Λ b) ⟨psi_injective K p Λ b, psi_surjective K p Λ b⟩

def phi2 : ℤ_[p] ⊗[ℤ] Λ ≃ₗ[ℤ_[p]] TateModule p (V ⧸ Λ) :=
  (Algebra.TensorProduct.basis ℤ_[p] b).equivFun.trans (psiEquiv K p Λ b)

theorem phi2_toLinearMap_eq :
    (phi2 K p Λ b).toLinearMap = (iota K p Λ).liftBaseChange ℤ_[p] := by
  refine (Algebra.TensorProduct.basis ℤ_[p] b).ext fun i => ?_
  rw [LinearEquiv.coe_coe, Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul,
    ← Algebra.TensorProduct.basis_apply, phi2, LinearEquiv.trans_apply, psiEquiv,
    LinearEquiv.ofBijective_apply, psi_apply]
  rw [Finset.sum_eq_single i]
  · rw [Basis.equivFun_self, if_pos rfl, one_smul]
  · intro j _ hji
    rw [Basis.equivFun_self, if_neg (Ne.symm hji), zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

@[scoped simp] theorem phi2_tmul (a : ℤ_[p]) (l : Λ) : phi2 K p Λ b (a ⊗ₜ l) = a • iota K p Λ l := by
  rw [← LinearEquiv.coe_coe, phi2_toLinearMap_eq, LinearMap.liftBaseChange_tmul]

variable (T : V →ₗ[K] V) (hT : ∀ v ∈ Λ, T v ∈ Λ)

def quotEnd : V ⧸ Λ →+ V ⧸ Λ :=
  (Λ.mapQ Λ T.toAddMonoidHom.toIntLinearMap fun v hv => hT v hv).toAddMonoidHom

@[scoped simp] theorem quotEnd_mk (v : V) :
    quotEnd K Λ T hT (Submodule.Quotient.mk v) = Submodule.Quotient.mk (T v) := rfl

theorem quotEnd_divLevel (n : ℕ) (v : V) :
    quotEnd K Λ T hT (divLevel K p Λ n v) = divLevel K p Λ n (T v) := by
  rw [divLevel_apply, divLevel_apply, quotEnd_mk, LinearMap.map_smul]

variable (TΛ : Λ →ₗ[ℤ] Λ)

theorem iota_restrict (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l) (l : Λ) :
    iota K p Λ (TΛ l) = tateMap p (quotEnd K Λ T hT) (iota K p Λ l) :=
  Subtype.ext (funext fun n => by
    rw [coe_iota_apply, coe_tateMap_apply, coe_iota_apply, hTΛ, quotEnd_divLevel])

theorem phi2_baseChange (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l) (z : ℤ_[p] ⊗[ℤ] Λ) :
    phi2 K p Λ b (TΛ.baseChange ℤ_[p] z) = tateMap p (quotEnd K Λ T hT) (phi2 K p Λ b z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a l =>
      rw [LinearMap.baseChange_tmul, phi2_tmul, phi2_tmul, iota_restrict K p Λ T hT TΛ hTΛ, map_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem assemble (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l)
    {M : Type} [AddCommGroup M] (u : M →+ V ⧸ Λ) (hu : Function.Injective u)
    (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range) (S : M →+ M)
    (hS : ∀ m, u (S m) = quotEnd K Λ T hT (u m)) (x y : TateModule p M)
    (hy : ∀ n, (y : ℕ → M) n = S ((x : ℕ → M) n)) :
    ((tateEquivOfInjective u hu htors).trans (phi2 K p Λ b).symm) y =
      TΛ.baseChange ℤ_[p] (((tateEquivOfInjective u hu htors).trans (phi2 K p Λ b).symm) x) := by
  have hy' : y = tateMap p S x := Subtype.ext (funext hy)
  subst hy'
  apply (phi2 K p Λ b).injective
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply,
    phi2_baseChange K p Λ b T hT TΛ hTΛ, LinearEquiv.apply_symm_apply,
    tateEquivOfInjective_apply, tateEquivOfInjective_apply]
  exact tateMap_naturality u S _ hS x

end Torus

section Assembly

open ModularCurve

variable (N : ℕ) [NeZero N]

theorem uniformization_heckeEvalBar (hcomm : HeckeOperatorsCommuteBar N)
    (u : JZero N →+ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) ⧸ periodLattice N))
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
      u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ))
    (t : HeckeAlg) :
    ∀ (x : JZero N) (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
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

theorem mainThm (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (hst : ModularCurve.PeriodLatticeHeckeStable N) :
    letI := ModularCurve.heckeModuleBar N
    ∃ e : TateModule p (ModularCurve.JZero N) ≃ₗ[ℤ_[p]]
        TensorProduct ℤ ℤ_[p] (ModularCurve.periodLattice N),
      ∀ (t : ModularCurve.HeckeAlg) (x : TateModule p (ModularCurve.JZero N)),
        e (ModularCurve.tateHeckeRep p (ModularCurve.JZero N) t x) =
          (ModularCurve.periodLatticeHeckeEnd N t).baseChange ℤ_[p] (e x) := by
  letI := ModularCurve.heckeModuleBar N
  obtain ⟨u, hu_inj, hu_tors, hu_hecke⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice N hin hst
  obtain ⟨r, b, -, -⟩ := ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  classical
  refine ⟨(tateEquivOfInjective u hu_inj hu_tors).trans (phi2 ℂ p (periodLattice N) b).symm,
    fun t x => ?_⟩
  have hT : ∀ v ∈ periodLattice N, dualHeckeRep N t v ∈ periodLattice N :=
    fun v hv => periodLattice_stable_of hst t v hv
  have hS : ∀ m : JZero N, u ((heckeEvalBar hcomm t).toAddMonoidHom m) =
      quotEnd ℂ (periodLattice N) (dualHeckeRep N t) hT (u m) := fun m => by
    obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective (periodLattice N) (u m)
    calc u ((heckeEvalBar hcomm t).toAddMonoidHom m)
          = Submodule.Quotient.mk (dualHeckeRep N t φ) :=
            uniformization_heckeEvalBar N hcomm u hu_hecke t m φ hφ.symm
      _ = quotEnd ℂ (periodLattice N) (dualHeckeRep N t) hT (Submodule.Quotient.mk φ) :=
            (quotEnd_mk ℂ (periodLattice N) (dualHeckeRep N t) hT φ).symm
      _ = quotEnd ℂ (periodLattice N) (dualHeckeRep N t) hT (u m) := congrArg _ hφ
  exact assemble ℂ p (periodLattice N) b (dualHeckeRep N t) hT (periodLatticeHeckeEnd N t)
    (fun l => coe_periodLatticeHeckeEnd_apply hst t l) u hu_inj hu_tors _ hS x _
    (fun n => heckeModuleBar_smul_def hcomm t _)

end Assembly

end W5ITatePeriod
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice.W5ITatePeriod"

theorem solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (hst : ModularCurve.PeriodLatticeHeckeStable N) :
    letI := ModularCurve.heckeModuleBar N
    ∃ e : TateModule p (ModularCurve.JZero N) ≃ₗ[ℤ_[p]]
        TensorProduct ℤ ℤ_[p] (ModularCurve.periodLattice N),
      ∀ (t : ModularCurve.HeckeAlg) (x : TateModule p (ModularCurve.JZero N)),
        e (ModularCurve.tateHeckeRep p (ModularCurve.JZero N) t x) =
          (ModularCurve.periodLatticeHeckeEnd N t).baseChange ℤ_[p] (e x) :=
  W5ITatePeriod.mainThm N p hin hcomm hst

end
end S_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
end P2MW
export P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice (solution)
