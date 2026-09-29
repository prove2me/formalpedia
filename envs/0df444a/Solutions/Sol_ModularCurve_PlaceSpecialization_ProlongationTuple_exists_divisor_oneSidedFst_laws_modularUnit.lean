-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_divisor_oneSidedFst_laws_modularUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/40ab4ec7-21b0-5f7a-82c2-01efe12728ec

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces
import Theorems.Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_PlaceSpecialization_isAlgClosed_of_level_of_not_dvd
import Theorems.Thm_ModularCurve_isCusp_iff_ord_neg
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isZeroSide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_restrictAlong_filter_isInftySide_divisor_modularUnit
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_sp_filter_neg_divisor_j_eq_ord_jqModC_of_isModel
import Theorems.Thm_ModularCurve_CharPModel_ord_jBar_dvd_of_ord_jBar_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_divisor_oneSidedFst_laws_modularUnit
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode"
p2m_attr_erase "simp" "ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve~jBar"

namespace LeafGen

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem modularUnitSeries_mem_full_mul :
    modularUnitSeries q ∈ modularFunctionFieldFull (N * q) :=
  full_degeneracy_le (dvd_mul_left q N) (modularUnitSeries_mem_modularFunctionFieldFull q)

private theorem isCuspidal_of_isCusp (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : IsCusp (CharPModel.jBar (N * q)) W) :
    PlaceSpecialization.ProlongationTuple.IsCuspidal P W := by
  intro a
  by_contra hpos
  rw [not_le] at hpos
  apply hW
  have hne : PlaceSpecialization.ProlongationTuple.jFun N q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hpos
    exact lt_irrefl _ hpos
  have h1 := W.mem_of_ord_nonneg hne hpos.le
  have h2 := W.algebraMap_mem' (a : AlgebraicClosure ℚ)
  have h3 := add_mem h1 h2
  rw [sub_add_cancel] at h3
  exact h3

private theorem mapDomain_apply_eq_zero_of_forall {α β : Type*} (f : α → β) (g : α →₀ ℤ) (v : β)
    (h : ∀ a ∈ g.support, f a ≠ v) : Finsupp.mapDomain f g v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_eq_zero (fun a ha => by simp [(h a ha).symm])

private theorem mapDomain_filter_apply_of_pred {α β : Type*} (f : α → β) (g : α →₀ ℤ) (r : β → Prop)
    [DecidablePred r] (v : β) (hv : r v) :
    Finsupp.mapDomain f (g.filter (fun a => r (f a))) v = Finsupp.mapDomain f g v := by
  classical
  rw [Finsupp.mapDomain, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_apply, Finsupp.sum,
    Finsupp.sum, Finsupp.support_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hfa : f a = v
  · simp [hfa, hv]
  · simp [Ne.symm hfa]

private theorem isCusp_of_ord_ne_zero
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hne : W.ord u ≠ 0) :
    IsCusp (CharPModel.jBar (N * q)) W := by
  intro hnc
  apply hne
  have hu' : u = ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) modularUnitSeries_mem_full_mul⟩ :=
    Subtype.ext hu
  rw [hu']
  exact ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp (N * q) q (dvd_mul_left q N)
    modularUnitSeries_mem_full_mul W (fun h => h hnc)

open ModularCurve.CharPModel in

private theorem dvd (N : ℕ) [NeZero N]
    (b : AlgebraicCurve.Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : b.ord (CharPModel.jBar N) < 0) : b.ord (CharPModel.jBar N) ∣ (N : ℤ) :=
  CharPModel.ord_jBar_dvd_of_ord_jBar_neg N b hb

p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide" in open Classical ModularCurve.PlaceSpecialization.ProlongationTuple in

private theorem sheet
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0) :
    (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = 1 :=
  PlaceSpecialization.ProlongationTuple.sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one
    hqN P b hb

open Classical in

private theorem inftyCusps (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord u)
    (Dj : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hDj : ∀ b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Dj b = b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        (D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P)) b
      = ((q : ℤ) - 1) * (Dj.filter (fun b' => Dj b' < 0)) b :=
  PlaceSpecialization.ProlongationTuple.mapDomain_restrictAlong_filter_isInftySide_divisor_modularUnit
    hqN P u hu D hD Dj hDj b

private theorem specJ (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (Dj : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hDj : ∀ b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Dj b = b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    Finsupp.mapDomain P.sp (Dj.filter (fun b => Dj b < 0)) v
      = v.ord ⟨jqModC k, jqModC_mem k N⟩ :=
  PlaceSpecialization.ProlongationTuple.mapDomain_sp_filter_neg_divisor_j_eq_ord_jqModC_of_isModel
    hqN P R hmodel Dj hDj v hv

private theorem residueCuspOrd (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    v.ord (R.residue₁ ⟨u, h₁⟩) = ((q : ℤ) - 1) * v.ord ⟨jqModC k, jqModC_mem k N⟩ :=
  PlaceSpecialization.ProlongationTuple.ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace
    hqN P R u hu h₁ v hv

private theorem exists_divisor_j :
    ∃ Dj : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∀ b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        Dj b = b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hne : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ≠ 0 :=
    fun h => (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr jq_ne_zero (congrArg Subtype.val h)
  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hne
  exact ⟨Dj, hDj⟩

open Classical in

private theorem inftySide_identity (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord u)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    Finsupp.mapDomain P.reduceFst (D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P)) v
      = v.ord (R.residue₁ ⟨u, h₁⟩) := by
  obtain ⟨Dj, hDj⟩ := exists_divisor_j (N := N)
  have hpush : Finsupp.mapDomain (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
      (D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P))
      = ((q : ℤ) - 1) • Dj.filter (fun b' => Dj b' < 0) := by
    ext b
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact inftyCusps hqN P u hu D hD Dj hDj b
  have hcomp : Finsupp.mapDomain P.reduceFst (D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P))
      = Finsupp.mapDomain
          (P.sp ∘ fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
          (D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P)) := rfl
  rw [hcomp, Finsupp.mapDomain_comp, hpush, Finsupp.mapDomain_smul, Finsupp.smul_apply, smul_eq_mul,
    specJ hqN P R hmodel Dj hDj v hv, residueCuspOrd hqN P R u hu h₁ v hv]

section SideLaws

p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple"

private theorem ramificationIndexAlong_pos {F F' : Type*} [Field F] [Field F']
    [Algebra (AlgebraicClosure ℚ) F] [Algebra (AlgebraicClosure ℚ) F']
    (φ : F →ₐ[AlgebraicClosure ℚ] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place (AlgebraicClosure ℚ) F') :
    0 < w.ramificationIndexAlong φ := by
  unfold Place.ramificationIndexAlong
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact Place.ramificationIndex_pos (F := F) w

private theorem mem_restrictAlong_iff {F F' : Type*} [Field F] [Field F']
    [Algebra (AlgebraicClosure ℚ) F] [Algebra (AlgebraicClosure ℚ) F']
    (φ : F →ₐ[AlgebraicClosure ℚ] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place (AlgebraicClosure ℚ) F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

private theorem restrictAlong_alpha_atkinLehner_smul (hqN : ¬ q ∣ N)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (atkinLehnerBar N q • V).restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
      = V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ := by
  have hτ : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hτ).2
  apply Place.ext
  ext f
  rw [mem_restrictAlong_iff, mem_restrictAlong_iff, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hf : heckeAlphaBar (AlgebraicClosure ℚ) N q f
      = atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q f) := by
    have := congrArg (fun ψ => ψ f) hlegs
    exact this.symm
  rw [hf]
  show (atkinLehnerBar N q)⁻¹ • (atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q f)) ∈ _
    ↔ _
  rw [AlgEquiv.smul_def, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

private theorem heckeBetaBar_jBar :
    heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) = jQFun N q :=
  Subtype.ext (by
    rw [coe_heckeBetaBar]
    exact (coeffEmb_qExpand (AlgebraicClosure ℚ) q jq).symm)

private theorem jFun_ne_zero : ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q ≠ 0 := fun h =>
  (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr jq_ne_zero (congrArg Subtype.val h)

private theorem jQFun_ne_zero : jQFun N q ≠ 0 := fun h =>
  (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr ((map_ne_zero (qExpand ℚ q)).mpr jq_ne_zero)
    (congrArg Subtype.val h)

private theorem ord_jFun_neg_of_isCusp
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : IsCusp (CharPModel.jBar (N * q)) W) :
    W.ord (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q) < 0 :=
  (isCusp_iff_ord_neg (CharPModel.jBar (N * q)) W).mp hW

private theorem coe_ne_zero_of_red_eq_one {τ : A} (hτ : red τ = 1) :
    (τ : AlgebraicClosure ℚ) ≠ 0 := by
  intro h0
  have hτ0 : τ = 0 := Subtype.ext h0
  rw [hτ0, map_zero] at hτ
  exact zero_ne_one hτ

private theorem ord_jQFun_of_isInftySide (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P W) : W.ord (jQFun N q) = q * W.ord (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q) := by
  obtain ⟨-, τ, hτ, hval⟩ := hW
  have h0 : W.ord (ModularCurve.PlaceSpecialization.ProlongationTuple.tInfty N q) = 0 :=
    hval.ord_eq_zero (coe_ne_zero_of_red_eq_one hτ)
  unfold ModularCurve.PlaceSpecialization.ProlongationTuple.tInfty at h0
  rw [div_eq_mul_inv, W.ord_mul jQFun_ne_zero (inv_ne_zero (pow_ne_zero q jFun_ne_zero)),
    Place.ord_inv, ← zpow_natCast, Place.ord_zpow] at h0
  linarith

private theorem ord_jFun_of_isZeroSide (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : ModularCurve.PlaceSpecialization.ProlongationTuple.IsZeroSide P W) : W.ord (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q) = q * W.ord (jQFun N q) := by
  obtain ⟨-, τ, hτ, hval⟩ := hW
  have h0 : W.ord (ModularCurve.PlaceSpecialization.ProlongationTuple.tZero N q) = 0 :=
    hval.ord_eq_zero (coe_ne_zero_of_red_eq_one hτ)
  unfold ModularCurve.PlaceSpecialization.ProlongationTuple.tZero at h0
  rw [div_eq_mul_inv, W.ord_mul jFun_ne_zero (inv_ne_zero (pow_ne_zero q jQFun_ne_zero)),
    Place.ord_inv, ← zpow_natCast, Place.ord_zpow] at h0
  linarith

private theorem ord_jQFun_eq (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    W.ord (jQFun N q)
      = (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ)
          * (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord
              (CharPModel.jBar N) := by
  rw [← heckeBetaBar_jBar]
  exact Place.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ W (CharPModel.jBar N)

private theorem ord_jFun_eq (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    W.ord (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q)
      = (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)
          * (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
              (CharPModel.jBar N) := by
  have h : heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) = ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q :=
    Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)
  rw [← h]
  exact Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W (CharPModel.jBar N)

private theorem ord_jBar_restrictAlong_beta_neg
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (h : W.ord (jQFun N q) < 0) :
    (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord (CharPModel.jBar N) < 0 := by
  rw [ord_jQFun_eq (hβ := hβ)] at h
  by_contra hle
  rw [not_lt] at hle
  exact absurd h (not_lt.mpr (mul_nonneg (Int.natCast_nonneg _) hle))

private theorem ramificationIndexAlong_beta_ne_one_of_isInftySide (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P W)
    (hb : (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord (CharPModel.jBar N)
      < 0) :
    W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) ≠ 1 := by
  intro he
  have h1 := ord_jQFun_eq (hβ := hβ) W
  rw [he, Nat.cast_one, one_mul, ord_jQFun_of_isInftySide P W hW] at h1
  have hdvd : (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord (CharPModel.jBar N)
      ∣ (N : ℤ) := dvd N _ hb
  rw [← h1] at hdvd
  exact hqN (Int.natCast_dvd_natCast.mp ((dvd_mul_right (q : ℤ) _).trans hdvd))

private theorem frob_reduceFst_eq_reduceSnd_of_isInftySide (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : IsCusp (CharPModel.jBar (N * q)) W)
    (hnf : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W))
      ≠ P.reduceFst W)
    (hinf : ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P W) :
    frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := by
  rcases P.d1 W with h | h
  · exfalso
    change P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) at h
    have hguard :
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W))
          ≠ P.reduceSnd W := by
      intro hfix
      apply hnf
      rw [h]
      exact congrArg (frobOnPlacesGeomLevel k N data hKr) hfix
    obtain ⟨W₀, -, -, he, huniq⟩ :=
      P.d2 (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) hguard
    have hWW₀ : W = W₀ := huniq W rfl h
    have hpole :
        (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord (CharPModel.jBar N)
          < 0 := by
      apply ord_jBar_restrictAlong_beta_neg
      rw [ord_jQFun_of_isInftySide P W hinf]
      exact mul_neg_of_pos_of_neg (by exact_mod_cast (Fact.out : q.Prime).pos)
        (ord_jFun_neg_of_isCusp W hW)
    exact ramificationIndexAlong_beta_ne_one_of_isInftySide hqN P W hinf hpole (hWW₀ ▸ he)
  · exact h

open Classical in

private theorem not_isStrictFst_of_isZeroSide (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hnf : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W))
      ≠ P.reduceFst W)
    (hW : IsCusp (CharPModel.jBar (N * q)) W) (hzero : ModularCurve.PlaceSpecialization.ProlongationTuple.IsZeroSide P W) (hs : P.IsStrictFst W) :
    False := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  have hstrict : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := hs.1

  have hjq : W.ord (jQFun N q) < 0 := by
    have h := ord_jFun_of_isZeroSide P W hzero
    have hj := ord_jFun_neg_of_isCusp W hW
    by_contra hle
    rw [not_lt] at hle
    exact absurd (h ▸ hj) (not_lt.mpr (mul_nonneg (Int.natCast_nonneg _) hle))
  set x := W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ with hx
  have hpole : x.ord (CharPModel.jBar N) < 0 := ord_jBar_restrictAlong_beta_neg W hjq

  have hguard :
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp x))
        ≠ P.sp x := by
    intro hfix
    apply hnf
    change frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W))
      = P.reduceSnd W at hfix
    rw [← hstrict] at hfix
    exact frobOnPlacesGeomLevel_injective k N data hKr hfix
  obtain ⟨W₀, hW₀x, hW₀φ, hW₀e, -⟩ := P.d2 x hguard

  have hne : W ≠ W₀ := by
    intro hEq
    apply hnf
    subst hEq
    change P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) at hW₀φ
    rw [← hstrict] at hW₀φ
    exact hW₀φ.symm

  have hVx :
      (atkinLehnerBar N q • W).restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = x :=
    restrictAlong_alpha_atkinLehner_smul hqN W
  have hV₀x :
      (atkinLehnerBar N q • W₀).restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = x := by
    rw [restrictAlong_alpha_atkinLehner_smul hqN W₀]
    exact hW₀x
  have hVinf : ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P (atkinLehnerBar N q • W) :=
    (isInftySide_atkinLehnerBar_smul_iff P hqN W).mpr hzero

  have hW₀cusp : IsCusp (CharPModel.jBar (N * q)) (atkinLehnerBar N q • W₀) := by
    apply (isCusp_iff_ord_neg (CharPModel.jBar (N * q)) _).mpr
    change (atkinLehnerBar N q • W₀).ord (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q) < 0
    rw [ord_jFun_eq (hα := hα), hV₀x]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast ramificationIndexAlong_pos _ hα _) hpole
  have hV₀inf : ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P (atkinLehnerBar N q • W₀) := by
    rcases isInftySide_or_isZeroSide_of_isCuspidal P hqN _
        (isCuspidal_of_isCusp P _ hW₀cusp) with h | h
    · exact h
    · exfalso
      have hW₀inf : ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P W₀ :=
        (isZeroSide_atkinLehnerBar_smul_iff P hqN W₀).mp h
      exact ramificationIndexAlong_beta_ne_one_of_isInftySide hqN P W₀ hW₀inf (hW₀x ▸ hpole) hW₀e
  have hVne : atkinLehnerBar N q • W ≠ atkinLehnerBar N q • W₀ :=
    fun h => hne (smul_left_cancel _ h)

  have hsheet := sheet (hα := hα) (hβ := hβ) hqN P x hpole
  have hmem : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = x → ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P V →
      V ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα x).filter (ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P) :=
    fun V hVx' hVinf' =>
    Finset.mem_filter.mpr ⟨Place.mem_fiberAlong.mpr hVx', hVinf'⟩
  have hsub : ({atkinLehnerBar N q • W, atkinLehnerBar N q • W₀} : Finset _)
      ⊆ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα x).filter
          (ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P) := by
    intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV
    · exact hmem _ hVx hVinf
    · rw [Finset.mem_singleton] at hV
      subst hV
      exact hmem _ hV₀x hV₀inf
  have hle : (∑ V ∈ ({atkinLehnerBar N q • W, atkinLehnerBar N q • W₀} : Finset _),
        (V.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
      ≤ ∑ V ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα x).filter
          (ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P),
        (V.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Int.natCast_nonneg _)
  rw [Finset.sum_pair hVne, hsheet] at hle
  have h1 : (1 : ℤ)
      ≤ ((atkinLehnerBar N q • W).ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
          : ℤ) := by
    exact_mod_cast ramificationIndexAlong_pos _ hα _
  have h2 : (1 : ℤ)
      ≤ ((atkinLehnerBar N q • W₀).ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
          : ℤ) := by
    exact_mod_cast ramificationIndexAlong_pos _ hα _
  linarith

end SideLaws

private theorem isStrictFst_iff_isInftySide (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : IsCusp (CharPModel.jBar (N * q)) W)
    (hnf : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W)) ≠ P.reduceFst W) :
    P.IsStrictFst W ↔ PlaceSpecialization.ProlongationTuple.IsInftySide P W := by
  constructor
  · intro hs
    rcases PlaceSpecialization.ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN W
        (isCuspidal_of_isCusp P W hW) with h | h
    · exact h
    · exact (not_isStrictFst_of_isZeroSide hqN P W hnf hW h hs).elim
  · intro hinf
    exact ⟨frob_reduceFst_eq_reduceSnd_of_isInftySide hqN P W hW hnf hinf, hnf⟩

open Classical in

private theorem filter_isStrictFst_eq (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord u) :
    D.filter P.IsStrictFst
      = (D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P)).filter
          (fun W => frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W))
            ≠ P.reduceFst W) := by
  ext W
  rw [Finsupp.filter_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hz : D W = 0
  · simp [hz]
  · have hW : IsCusp (CharPModel.jBar (N * q)) W :=
      isCusp_of_ord_ne_zero u hu W (by rw [← hD W]; exact hz)
    by_cases hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W))
        = P.reduceFst W
    · have hs : ¬ P.IsStrictFst W := fun h => h.2 hfix
      rw [if_neg hs, if_neg (not_not.mpr hfix)]
    · have hiff := isStrictFst_iff_isInftySide hqN P W hW hfix
      by_cases hs : P.IsStrictFst W
      · rw [if_pos hs, if_pos hfix, if_pos (hiff.mp hs)]
      · rw [if_neg hs, if_pos hfix, if_neg (fun hi => hs (hiff.mpr hi))]

open Classical in

private theorem clause_strictFst (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord u)
    (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) :
    Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) v = v.ord (R.residue₁ ⟨u, h₁⟩) := by
  by_cases haff : IsAffineGeomPlace k N v
  · haveI : IsAlgClosed k := PlaceSpecialization.isAlgClosed_of_level_of_not_dvd hqN P
    have hss : v ∉ ssPlaces q N k := fun hw =>
      hv (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data
        hKr v hw)
    rw [PlaceSpecialization.ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces
      P R u hu h₁ v haff hss]
    apply mapDomain_apply_eq_zero_of_forall
    intro W hWs hWv
    rw [Finsupp.mem_support_iff, Finsupp.filter_apply] at hWs
    have hne : D W ≠ 0 := fun h0 => hWs (by simp [h0])
    have hW : IsCusp (CharPModel.jBar (N * q)) W :=
      isCusp_of_ord_ne_zero u hu W (by rw [← hD W]; exact hne)
    exact PlaceSpecialization.ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P W
      (isCuspidal_of_isCusp P W hW) (by rw [hWv]; exact haff)
  · calc Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) v
        = Finsupp.mapDomain P.reduceFst
            ((D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P)).filter
              (fun W => frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W))
                ≠ P.reduceFst W)) v := by
          rw [filter_isStrictFst_eq hqN P u hu D hD]
      _ = Finsupp.mapDomain P.reduceFst (D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P)) v :=
          mapDomain_filter_apply_of_pred P.reduceFst _
            (fun x => frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr x) ≠ x) v hv
      _ = v.ord (R.residue₁ ⟨u, h₁⟩) := inftySide_identity hqN P R hmodel u hu h₁ D hD v haff

open Classical in

private theorem clause_cuspInfty (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord u)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hc : PlaceSpecialization.ProlongationTuple.IsInftySide P c) :
    Finsupp.mapDomain P.reduceFst (D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P))
        (P.reduceFst c) = (P.reduceFst c).ord (R.residue₁ ⟨u, h₁⟩) :=
  inftySide_identity hqN P R hmodel u hu h₁ D hD (P.reduceFst c)
    (PlaceSpecialization.ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P c hc.1)

end LeafGen

p2m_open "Classical AlgebraicCurve ModularCurve~jBar ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve.PlaceSpecialization.ProlongationTuple"

open Classical in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers) :
    ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord u) ∧
      (∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
        Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) v
          = v.ord (R.residue₁ ⟨u, h₁⟩)) ∧
      (∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P c →
        Finsupp.mapDomain P.reduceFst (D.filter (ModularCurve.PlaceSpecialization.ProlongationTuple.IsInftySide P)) (P.reduceFst c)
          = (P.reduceFst c).ord (R.residue₁ ⟨u, h₁⟩)) := by
  have hu0 : u ≠ 0 := by
    intro h0
    have h1 : (u : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
      rw [h0]
      rfl
    rw [hu] at h1
    exact (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr (modularUnitSeries_ne_zero q) h1
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) u hu0
  exact ⟨D, hD, fun v hv => LeafGen.clause_strictFst hqN P R hmodel u hu h₁ D hD v hv,
    fun c hc => LeafGen.clause_cuspInfty hqN P R hmodel u hu h₁ D hD c hc⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_divisor_oneSidedFst_laws_modularUnit
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_divisor_oneSidedFst_laws_modularUnit (solution)
