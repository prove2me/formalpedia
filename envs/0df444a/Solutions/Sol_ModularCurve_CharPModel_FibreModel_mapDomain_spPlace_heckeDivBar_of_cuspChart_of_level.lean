-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/30b82abf-09c2-5223-8bbb-d18f50755fe4

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level
import Theorems.Thm_ModularCurve_mapDomain_heckeDivBar_single
import Theorems.Thm_ModularCurve_mapDomain_heckeDivBar_eq_of_forall_single
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_surjective
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j
import Theorems.Thm_ModularCurve_sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_finset_ord_jBar_sub_pos
import Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D"
p2m_attr_erase "simp" "ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe"

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve Polynomial

noncomputable section

namespace SolESAllDivisors

local notation "ℚbar" => AlgebraicClosure ℚ

section Rigidity

variable {N : ℕ} [NeZero N] {β : Type*}

private theorem apply_eq_zero_of_mem_degZero
    (δ : Divisor ℚbar (modularFunctionFieldBar N) →+ (β →₀ ℤ))
    (hprin : ∀ D ∈ Divisor.principal (K := ℚbar) (F := modularFunctionFieldBar N), δ D = 0)
    {D : Divisor ℚbar (modularFunctionFieldBar N)}
    (hD : D ∈ Divisor.degZero (K := ℚbar) (F := modularFunctionFieldBar N)) :
    δ D = 0 := by
  ext w
  rw [Finsupp.zero_apply]
  set c : ℤ := δ D w with hc
  obtain ⟨y, hy⟩ := ModularCurve.JZero.divisible N (c.natAbs + 1) (Nat.succ_ne_zero _)
    (Pic0.mk ⟨D, hD⟩)
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
  have hEq : Pic0.mk ((c.natAbs + 1) • E) = Pic0.mk ⟨D, hD⟩ := by
    rw [← hy]
    exact QuotientAddGroup.mk_nsmul _ _ _
  have hmem := QuotientAddGroup.eq.mp hEq
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  have h0 := hprin _ hmem
  rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_nsmul, map_add, map_neg,
    map_nsmul, neg_add_eq_zero] at h0

  have hcw : c = ((c.natAbs + 1 : ℕ) : ℤ) * δ (E : Divisor ℚbar (modularFunctionFieldBar N)) w := by
    have := congrArg (fun f : β →₀ ℤ => f w) h0
    simp only [Finsupp.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at this
    rw [hc]
    exact this.symm
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨_, hcw⟩
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)

private theorem apply_single_eq_apply_single
    (δ : Divisor ℚbar (modularFunctionFieldBar N) →+ (β →₀ ℤ))
    (hprin : ∀ D ∈ Divisor.principal (K := ℚbar) (F := modularFunctionFieldBar N), δ D = 0)
    (v v' : Place ℚbar (modularFunctionFieldBar N)) :
    δ (Finsupp.single v 1) = δ (Finsupp.single v' 1) := by
  have hmem : Finsupp.single v 1 - Finsupp.single v' 1
      ∈ Divisor.degZero (K := ℚbar) (F := modularFunctionFieldBar N) := by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      ModularCurve.deg_eq_one_modularFunctionFieldBar N v,
      ModularCurve.deg_eq_one_modularFunctionFieldBar N v']
    simp
  have h := apply_eq_zero_of_mem_degZero δ hprin hmem
  rwa [map_sub, sub_eq_zero] at h

end Rigidity

section Finsupp

variable {β : Type*}

private def csum : (β →₀ ℤ) →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

@[scoped simp] private theorem csum_single (b : β) (n : ℤ) : csum (Finsupp.single b n) = n := by
  simp [csum]

private theorem csum_eq_sum (f : β →₀ ℤ) : csum f = ∑ b ∈ f.support, f b := by
  simp [csum, Finsupp.liftAddHom_apply, Finsupp.sum]

private theorem eq_zero_of_nonneg_of_csum_eq_zero (f : β →₀ ℤ) (hf : ∀ b, 0 ≤ f b)
    (hs : csum f = 0) : f = 0 := by
  rw [csum_eq_sum] at hs
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hf b)).mp hs
  ext b
  by_cases hb : b ∈ f.support
  · exact hall b hb
  · simpa [Finsupp.mem_support_iff] using hb

end Finsupp

section ManyPlaces

variable {A : ValuationSubring ℚbar} {ℓ : ℕ} [Fact ℓ.Prime] {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

private theorem infinite_of_surjective (hred : Function.Surjective red) : Infinite k := by
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  let e : IsLocalRing.ResidueField A ≃+* k :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hred)
  exact Infinite.of_injective e e.injective

private theorem exists_ord_jBar_sub_pos (a : ℚbar) :
    ∃ w : Place ℚbar (modularFunctionFieldBar N),
      0 < w.ord (ModularCurve.jBar N - algebraMap ℚbar (modularFunctionFieldBar N) a) := by
  obtain ⟨S, hS⟩ := ModularCurve.exists_finset_ord_jBar_sub_pos N a
  have hsum := ModularCurve.sum_ord_jBar_sub_eq_dedekindPsi N a
    (ModularCurve.deg_eq_one_modularFunctionFieldBar N) S hS
  have hpos : 0 < (dedekindPsi N : ℤ) := by
    exact_mod_cast ModularCurve.dedekindPsi_pos N (NeZero.ne N)
  by_contra h
  push Not at h
  have hS0 : S = ∅ := by
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    exact absurd ((hS v).mp hv) (not_lt.mpr (h v))
  rw [hS0, Finset.sum_empty] at hsum
  omega

private theorem isUnit_algebraMap_place {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {c : K} (hc : c ≠ 0) :
    ∃ x : u.toValuationSubringˣ, ((x : u.toValuationSubring) : F) = algebraMap K F c := by
  refine ⟨⟨⟨algebraMap K F c, u.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, u.algebraMap_mem' c⁻¹⟩,
    ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (by simp [hc])
  · exact Subtype.ext (by simp [hc])

private theorem eq_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) (x : F) {c c' : K}
    (hc : 0 < u.ord (x - algebraMap K F c)) (hc' : 0 < u.ord (x - algebraMap K F c')) :
    c = c' := by
  by_contra hne
  have hx0 : x - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hc; exact lt_irrefl _ hc
  have hx0' : x - algebraMap K F c' ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hc'; exact lt_irrefl _ hc'
  have hmem : x - algebraMap K F c ∈ u.toValuationSubring :=
    u.mem_of_ord_nonneg hx0 hc.le
  have hmem' : x - algebraMap K F c' ∈ u.toValuationSubring :=
    u.mem_of_ord_nonneg hx0' hc'.le
  have hmax := (u.mem_maximalIdeal_iff_ord_pos hx0 hmem).mpr hc
  have hmax' := (u.mem_maximalIdeal_iff_ord_pos hx0' hmem').mpr hc'
  have hdiff := sub_mem hmax' hmax

  have hcc : c - c' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨y, hy⟩ := isUnit_algebraMap_place u hcc
  have hval : ((⟨x - algebraMap K F c', hmem'⟩ - ⟨x - algebraMap K F c, hmem⟩ :
      u.toValuationSubring) : F) = algebraMap K F (c - c') := by
    push_cast
    ring
  have hunit : IsUnit (⟨x - algebraMap K F c', hmem'⟩ - ⟨x - algebraMap K F c, hmem⟩ :
      u.toValuationSubring) := by
    have : (⟨x - algebraMap K F c', hmem'⟩ - ⟨x - algebraMap K F c, hmem⟩ :
        u.toValuationSubring) = (y : u.toValuationSubring) := Subtype.ext (by rw [hval, hy])
    rw [this]
    exact Units.isUnit y
  exact (IsLocalRing.mem_maximalIdeal _).mp hdiff hunit

private theorem infinite_place_modularFunctionFieldC (fm : FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    Infinite (Place k (modularFunctionFieldC k N)) := by
  haveI : Infinite k := infinite_of_surjective hred

  have hex : ∀ c : k, ∃ u : Place k (modularFunctionFieldC k N),
      0 < u.ord ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
        - algebraMap k (modularFunctionFieldC k N) c) := by
    intro c
    obtain ⟨a, rfl⟩ := hred c
    obtain ⟨w, hw⟩ := exists_ord_jBar_sub_pos (N := N) (a : ℚbar)
    exact ⟨fm.spPlace hred dataAll hsep w,
      ModularCurve.CharPModel.FibreModel.spPlace_d0_j N A ℓ k red fm hred dataAll hsep w a hw⟩
  choose u hu using hex
  refine Infinite.of_injective u fun c c' h => ?_
  exact eq_of_ord_sub_pos (u c) _ (hu c) (h ▸ hu c')

end ManyPlaces

section Frobenius

variable (k : Type*) [Field k] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

private theorem heckeFibreGeomLevel_single (u : Place k (modularFunctionFieldC k N)) (n : ℤ) :
    heckeFibreGeomLevel k N data hKr (Finsupp.single u n)
      = Finsupp.single (frobOnPlacesGeomLevel k N data hKr u) n
        + Finsupp.single (verOnPlacesGeomLevel k N data hKr u) (n * ℓ) := by
  rw [show heckeFibreGeomLevel k N data hKr (Finsupp.single u n)
      = frobeniusPushforwardGeomLevel k N data hKr (Finsupp.single u n)
        + frobeniusPullbackGeomLevel k N data hKr (Finsupp.single u n) from rfl,
    frobeniusPushforwardGeomLevel_single, frobeniusPullbackGeomLevel_single]

private theorem eq_or_eq_of_verOnPlacesGeomLevel_eq {u w : Place k (modularFunctionFieldC k N)}
    (h : verOnPlacesGeomLevel k N data hKr u = w) :
    u = frobOnPlacesGeomLevel k N data hKr w ∨ u = w := by
  unfold verOnPlacesGeomLevel at h
  split_ifs at h with h'
  · left
    rw [← h]
    exact h'.choose_spec.symm
  · right
    exact h

private theorem mem_finset_of_bad (w : Place k (modularFunctionFieldC k N)) :
    ∃ B : Finset (Place k (modularFunctionFieldC k N)), ∀ u,
      (frobOnPlacesGeomLevel k N data hKr u = w ∨ verOnPlacesGeomLevel k N data hKr u = w) →
        u ∈ B := by
  classical
  let pre : Finset (Place k (modularFunctionFieldC k N)) :=
    if h : ∃ p, frobOnPlacesGeomLevel k N data hKr p = w then {h.choose} else ∅
  refine ⟨insert w (insert (frobOnPlacesGeomLevel k N data hKr w) pre), fun u hu => ?_⟩
  rcases hu with hu | hu
  · have hex : ∃ p, frobOnPlacesGeomLevel k N data hKr p = w := ⟨u, hu⟩
    have hp : hex.choose = u :=
      frobOnPlacesGeomLevel_injective k N data hKr (hex.choose_spec.trans hu.symm)
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    simp only [pre, dif_pos hex, Finset.mem_singleton]
    exact hp.symm
  · rcases eq_or_eq_of_verOnPlacesGeomLevel_eq k N data hKr hu with h | h
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h]; exact Finset.mem_insert_self _ _

end Frobenius

section CharZero

variable {N ℓ : ℕ} [NeZero N] [Fact ℓ.Prime]

private scoped instance neZero_ell : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

variable (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
  (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
  [HasPrincipalDivisors (AlgebraicClosure ℚ)
    (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
  {k : Type*} [Field k]

private theorem mapDomain_heckeDivBar_single_eq_sum
    (sp : Place ℚbar (modularFunctionFieldBar N) → Place k (modularFunctionFieldC k N))
    (v : Place ℚbar (modularFunctionFieldBar N)) :
    Finsupp.mapDomain sp (heckeDivBar halpha hbeta (Finsupp.single v 1))
      = ∑ W ∈ Place.fiberAlong (heckeBetaBar ℚbar N ℓ) hbeta v,
          Finsupp.single (sp (W.restrictAlong (heckeAlphaBar ℚbar N ℓ) halpha))
            ((W.ramificationIndexAlong (heckeBetaBar ℚbar N ℓ) : ℤ)) := by
  rw [ModularCurve.mapDomain_heckeDivBar_single halpha hbeta sp v 1]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange (heckeAlphaBar ℚbar N ℓ) halpha W]
  simp

private theorem mapDomain_heckeDivBar_single_nonneg
    (sp : Place ℚbar (modularFunctionFieldBar N) → Place k (modularFunctionFieldC k N))
    (v : Place ℚbar (modularFunctionFieldBar N)) (u : Place k (modularFunctionFieldC k N)) :
    0 ≤ Finsupp.mapDomain sp (heckeDivBar halpha hbeta (Finsupp.single v 1)) u := by
  classical
  rw [mapDomain_heckeDivBar_single_eq_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_nonneg fun W _ => ?_
  rw [Finsupp.single_apply]
  split_ifs
  · exact_mod_cast Nat.zero_le _
  · exact le_rfl

private theorem csum_mapDomain_heckeDivBar_single (hlN : ¬ ℓ ∣ N)
    (sp : Place ℚbar (modularFunctionFieldBar N) → Place k (modularFunctionFieldC k N))
    (v : Place ℚbar (modularFunctionFieldBar N)) :
    csum (Finsupp.mapDomain sp (heckeDivBar halpha hbeta (Finsupp.single v 1))) = ℓ + 1 := by
  rw [mapDomain_heckeDivBar_single_eq_sum, map_sum]
  simp only [csum_single]
  exact ModularCurve.sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one N ℓ hlN hbeta
    (ModularCurve.deg_eq_one_modularFunctionFieldBar (N * ℓ)) v

end CharZero

section Assembly

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]

private theorem main
    (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta D) =
      heckeFibreGeomLevel k N data hKr
        (Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D) := by
  classical
  set sp := fm.spPlace hred dataAll hsep with hsp

  let S : Divisor ℚbar (modularFunctionFieldBar N) →+ Divisor k (modularFunctionFieldC k N) :=
    Finsupp.mapDomain.addMonoidHom sp
  let T : Divisor ℚbar (modularFunctionFieldBar N) →+ Divisor ℚbar (modularFunctionFieldBar N) :=
    heckeDivBar halpha hbeta
  let H : Divisor k (modularFunctionFieldC k N) →+ Divisor k (modularFunctionFieldC k N) :=
    heckeFibreGeomLevel k N data hKr
  let δ : Divisor ℚbar (modularFunctionFieldBar N) →+ Divisor k (modularFunctionFieldC k N) :=
    S.comp T - H.comp S
  have hδ : ∀ D, δ D = Finsupp.mapDomain sp (heckeDivBar halpha hbeta D)
      - heckeFibreGeomLevel k N data hKr (Finsupp.mapDomain sp D) := fun D => rfl

  have hprin : ∀ D ∈ Divisor.principal (K := ℚbar) (F := modularFunctionFieldBar N), δ D = 0 := by
    intro D hD
    rw [hδ, sub_eq_zero]
    exact ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level
      A ℓ N hlN data hKr k red halpha hbeta hred dataAll hsym hsep fm cc D hD

  have hconst : ∀ v v' : Place ℚbar (modularFunctionFieldBar N),
      δ (Finsupp.single v 1) = δ (Finsupp.single v' 1) :=
    apply_single_eq_apply_single δ hprin

  suffices hzero : ∀ v : Place ℚbar (modularFunctionFieldBar N), δ (Finsupp.single v 1) = 0 by
    have hsingle : ∀ v : Place ℚbar (modularFunctionFieldBar N),
        Finsupp.mapDomain sp (heckeDivBar halpha hbeta (Finsupp.single v 1))
          = heckeFibreGeomLevel k N data hKr (Finsupp.single (sp v) 1) := by
      intro v
      have h := hzero v
      rw [hδ, sub_eq_zero, Finsupp.mapDomain_single] at h
      exact h
    exact ModularCurve.mapDomain_heckeDivBar_eq_of_forall_single halpha hbeta sp
      (heckeFibreGeomLevel k N data hKr) hsingle D
  intro v₀
  set δ₀ := δ (Finsupp.single v₀ 1) with hδ₀

  have hcsum : csum δ₀ = 0 := by
    rw [hδ₀, hδ, map_sub, csum_mapDomain_heckeDivBar_single halpha hbeta hlN sp v₀,
      Finsupp.mapDomain_single, heckeFibreGeomLevel_single, map_add, csum_single, csum_single]
    ring

  have hlower : ∀ (u w : Place k (modularFunctionFieldC k N)),
      frobOnPlacesGeomLevel k N data hKr u ≠ w → verOnPlacesGeomLevel k N data hKr u ≠ w →
        0 ≤ δ₀ w := by
    intro u w hφ hV
    obtain ⟨v, hv⟩ := ModularCurve.CharPModel.FibreModel.spPlace_surjective N A ℓ k red fm hred
      dataAll hsep u
    have hv' : sp v = u := hv
    rw [hδ₀, hconst v₀ v, hδ, Finsupp.mapDomain_single, Finsupp.sub_apply,
      heckeFibreGeomLevel_single, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      hv', if_neg hφ, if_neg hV, add_zero, sub_zero]
    exact mapDomain_heckeDivBar_single_nonneg halpha hbeta sp v w

  haveI : Infinite (Place k (modularFunctionFieldC k N)) :=
    infinite_place_modularFunctionFieldC fm hred dataAll hsep
  have hnonneg : ∀ w, 0 ≤ δ₀ w := by
    intro w
    obtain ⟨B, hB⟩ := mem_finset_of_bad k N data hKr w
    obtain ⟨u, hu⟩ := Infinite.exists_notMem_finset B
    have hgood : ¬ (frobOnPlacesGeomLevel k N data hKr u = w
        ∨ verOnPlacesGeomLevel k N data hKr u = w) := fun h => hu (hB u h)
    push Not at hgood
    exact hlower u w hgood.1 hgood.2
  exact eq_zero_of_nonneg_of_csum_eq_zero δ₀ hnonneg hcsum

end Assembly

end SolESAllDivisors
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level.SolESAllDivisors"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level.SolESAllDivisors"

open SolESAllDivisors in

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta D) =
      heckeFibreGeomLevel k N data hKr
        (Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D) :=
  SolESAllDivisors.main A ℓ N hlN data hKr k red halpha hbeta hred dataAll hsym hsep fm cc D

end S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level (solution)
