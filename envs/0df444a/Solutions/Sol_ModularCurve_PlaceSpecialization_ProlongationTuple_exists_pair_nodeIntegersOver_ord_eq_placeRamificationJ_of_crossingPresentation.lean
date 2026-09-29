-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8ab91d55-d7a8-5677-8c42-c8ba7bc13123

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_PlaceWidth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_qExpand_jqNModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace SolW3_j1

section Eval

variable {L : Type*} [CommRing L] (M : ℕ) [NeZero M] (S : Subring L)

private theorem mev_X0_j1 : modularEval M S (MvPolynomial.X 0) = jqModC L := by
  simp [modularEval]

private theorem mev_X1_j1 : modularEval M S (MvPolynomial.X 1) = jqNModC L M := by
  simp [modularEval, Matrix.cons_val_one]

private theorem mev_C_j1 (c : S) : modularEval M S (MvPolynomial.C c) = algebraMap L (LaurentSeries L) c := by
  simp [modularEval, CharPReduction.constSeries]

private theorem jqNModC_cast_j1 {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) : jqNModC L n = jqNModC L m := by
  subst h
  rfl

private theorem qExpand_cast_j1 {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) (x : LaurentSeries L) :
    qExpand L n x = qExpand L m x := by
  subst h
  rfl

end Eval

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem hasValue_sub_j1 (v : Place K F) {g g' : F} {c c' : K}
    (h : v.HasValue g c) (h' : v.HasValue g' c') : v.HasValue (g - g') (c - c') := by
  rcases h with ⟨hg, hr⟩
  rcases h' with ⟨hg', hr'⟩
  refine ⟨sub_mem hg hg', ?_⟩
  rw [map_sub, ← hr, ← hr', ← map_sub]
  rfl

private theorem hasValue_pow_j1 (v : Place K F) {g : F} {c : K} (h : v.HasValue g c) :
    ∀ n : ℕ, v.HasValue (g ^ n) (c ^ n)
  | 0 => by
    rw [pow_zero, pow_zero]
    exact v.hasValue_one
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (hasValue_pow_j1 v h n).mul h

private theorem ord_eq_of_assoc_j1 (v : Place K F) {x d b b' : F} (hd : d ≠ 0)
    (hx : x = b * d) (hd' : d = b' * x)
    (hb : b ≠ 0 → 0 ≤ v.ord b) (hb' : b' ≠ 0 → 0 ≤ v.ord b') :
    x ≠ 0 ∧ v.ord x = v.ord d := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hd (by rw [hd', mul_zero])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hx, zero_mul])
  have hb0' : b' ≠ 0 := by
    rintro rfl
    exact hd (by rw [hd', zero_mul])
  have e1 : v.ord x = v.ord b + v.ord d := by rw [hx, v.ord_mul hb0 hd]
  have e2 : v.ord d = v.ord b' + v.ord x := by
    conv_lhs => rw [hd']
    exact v.ord_mul hb0' hx0
  have := hb hb0
  have := hb' hb0'
  exact ⟨hx0, by omega⟩

end PlaceFacts

section LinComb

variable {S T U : Type*} [CommRing S] [CommRing T] [CommRing U]

private theorem comb_read_j1 (τ : S →+* T) (ρ : T →+* U) {α β p g G : S} (h : α * p + β * g = G)
    (hp : ρ (τ p) = 0) : ρ (τ G) = ρ (τ β) * ρ (τ g) := by
  rw [← h, map_add, map_mul, map_mul, map_add, map_mul, map_mul, hp, mul_zero, zero_add]

end LinComb

section Frob

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]

private theorem frob_factor_j1 (c : k) (hc : c ^ (q ^ 2) = c) :
    jGeomGen k N - (jGeomGen k N ^ q) ^ q
      = (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c)
          * (1 - (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) ^ (q ^ 2 - 1)) := by
  haveI : CharP (modularFunctionFieldC k N) q :=
    charP_of_injective_algebraMap (algebraMap k (modularFunctionFieldC k N)).injective q
  obtain ⟨m, hm⟩ : ∃ m, q ^ 2 - 1 = m + 1 :=
    ⟨q ^ 2 - 2, by have := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt; omega⟩
  have hpow : jGeomGen k N ^ (q ^ 2)
      = (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) ^ (q ^ 2)
          + algebraMap k (modularFunctionFieldC k N) c := by
    rw [sub_pow_char_pow, ← map_pow, hc, sub_add_cancel]
  have hq2 : q ^ 2 = (q ^ 2 - 1) + 1 := by omega
  calc jGeomGen k N - (jGeomGen k N ^ q) ^ q
      = jGeomGen k N - jGeomGen k N ^ (q ^ 2) := by rw [← pow_mul, sq]
    _ = (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c)
          - (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) ^ (q ^ 2) := by rw [hpow]; ring
    _ = _ := by
      conv_lhs => rw [hq2, pow_succ]
      ring

variable [IsAlgClosed k] [DecidableEq k]

private theorem ord_frobDiff_j1 {w : Place k (modularFunctionFieldC k N)} (hss : IsSupersingularPlace q N k w) :
    jGeomGen k N - (jGeomGen k N ^ q) ^ q ≠ 0 ∧
    w.ord (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = (placeRamificationJ N w : ℤ) ∧
    (arithFrobC q k N • w).ord (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = (placeRamificationJ N w : ℤ) := by
  have hc : w.evalAt (jGeomGen k N) ^ (q ^ 2) = w.evalAt (jGeomGen k N) :=
    pow_q_sq_eq_self_of_mem_ssJSet q hss.2.2
  have ht0 : jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N)) ≠ 0 :=
    jGeomGen_sub_algebraMap_ne_zero k N _
  have hpos : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N))) :=
    ord_sub_evalAt_pos_of_isRational hss.1 hss.2.1.1 ht0
  have hr : (placeRamificationJ N w : ℤ)
      = w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N))) := by
    show (((w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N)))).toNat : ℕ)
        : ℤ) = _
    exact Int.toNat_of_nonneg hpos.le

  have hJ : w.HasValue (jGeomGen k N) (w.evalAt (jGeomGen k N)) :=
    ⟨hss.2.1.1, (w.algebraMap_evalAt hss.1 hss.2.1.1).symm⟩
  have hT : w.HasValue (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N))) 0 := by
    have h := hasValue_sub_j1 w hJ (w.hasValue_algebraMap (w.evalAt (jGeomGen k N)))
    rwa [sub_self] at h
  have hU : w.HasValue
      (1 - (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N))) ^ (q ^ 2 - 1)) 1 := by
    have h := hasValue_sub_j1 w w.hasValue_one (hasValue_pow_j1 w hT (q ^ 2 - 1))
    rwa [zero_pow (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt)),
      sub_zero] at h
  have hU0 := hU.ne_zero one_ne_zero
  have hfac := frob_factor_j1 (N := N) (w.evalAt (jGeomGen k N)) hc
  have hD0 : jGeomGen k N - (jGeomGen k N ^ q) ^ q ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero ht0 hU0
  have hordw : w.ord (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = (placeRamificationJ N w : ℤ) := by
    rw [hfac, w.ord_mul ht0 hU0, hU.ord_eq_zero one_ne_zero, add_zero, hr]

  have hfix : arithFrobC q k N • (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
    have hj : SemilinearAut.toRingAut (arithFrobC q k N) (jGeomGen k N) = jGeomGen k N := arithFrobC_smul_jq q k N
    show SemilinearAut.toRingAut (arithFrobC q k N) _ = _
    rw [map_sub, map_pow, map_pow, hj]
  refine ⟨hD0, hordw, ?_⟩
  rw [← hordw]
  conv_lhs => rw [← hfix]
  exact SemilinearAut.ord_smul _ _ _

end Frob

section Tuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem residue₁_const_j1 (c : A) (hc : red c = 0) :
    ∀ (g : ↥(modularFunctionFieldBar (N * q))) (h₁ : g ∈ R.R₁.integers),
      g = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) →
      R.ι (R.R₁.residue ⟨g, h₁⟩) = 0 := by
  rintro g h₁ rfl
  have e : R.R₁.residue ⟨_, h₁⟩ = algebraMap (ResidueField A) _ (IsLocalRing.residue A c) :=
    R.R₁.residue_algebraMap c
  rw [e]
  apply Subtype.ext
  rw [R.ι_coe, ZeroMemClass.coe_zero]
  show coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A c)) = 0
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, R.redBar_residue, hc, HahnSeries.single_eq_zero]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem residue₂_const_j1 (c : A) (hc : red c = 0)
    (g : ↥(modularFunctionFieldBar (N * q))) (h₂ : g ∈ R.R₂.integers)
    (hg : g = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) :
    R.residue₂ ⟨g, h₂⟩ = 0 := by
  rw [residue₂_apply, R.residue₂_eq]
  refine residue₁_const_j1 R c hc _ _ ?_
  rw [hg]
  exact (atkinLehnerBar N q).commutes _

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₁_series_j1 (y : LaurentSeries A) :
    ∀ g : ↥(modularFunctionFieldBar (N * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y →
      ∃ h : g ∈ R.R₁.integers,
        ((R.residue₁ ⟨g, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) = coeffMap red y := by
  rintro ⟨g, hg⟩ e
  simp only at e
  subst e
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hg
  refine ⟨h, ?_⟩
  rw [residue₁_apply, R.ι_coe, hres, coeffMap_coeffMap]
  exact congrArg (coeffMap · y) (RingHom.ext R.redBar_residue)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem dict₁_j1 :
    (∃ h : jFun N q ∈ R.R₁.integers, R.residue₁ ⟨jFun N q, h⟩ = jGeomGen k N) ∧
    (∃ h : jQFun N q ∈ R.R₁.integers, R.residue₁ ⟨jQFun N q, h⟩ = jGeomGen k N ^ q) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨h, e⟩ := residue₁_series_j1 R (jqModC A) (jFun N q)
      (by rw [coeffSemilinearAut.coeffMap_jqModC]; exact coeffEmb_jq _)
    refine ⟨h, Subtype.ext ?_⟩
    rw [e, coeffSemilinearAut.coeffMap_jqModC, coe_jGeomGen]
  · obtain ⟨h, e⟩ := residue₁_series_j1 R (qExpand A q (jqModC A)) (jQFun N q)
      (by
        rw [coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_jqModC,
          ← coeffEmb_jq (AlgebraicClosure ℚ), ← coeffEmb_qExpand]
        rfl)
    refine ⟨h, Subtype.ext ?_⟩
    have hp := qExpand_jqNModC_eq_pow_unconditional k 1 (ℓ := q)
    rw [jqNModC_one] at hp
    rw [e, coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_jqModC, hp, SubmonoidClass.coe_pow,
      coe_jGeomGen]

private theorem jpair_mk_j1 :
    jFun N q = ⟨coeffEmb (AlgebraicClosure ℚ)
        ((⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))).2⟩ ∧
    jQFun N q = ⟨coeffEmb (AlgebraicClosure ℚ)
        ((⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))).2⟩ :=
  ⟨Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq).symm),
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_cast_j1 (one_mul q).symm jq))⟩

private theorem al_swap_j1 (hqN : ¬ q ∣ N) :
    atkinLehnerBar N q (jFun N q) = jQFun N q ∧ atkinLehnerBar N q (jQFun N q) = jFun N q := by
  have hAL := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN) 1 inferInstance (one_dvd N)
  obtain ⟨e₁, e₂⟩ := jpair_mk_j1 (q := q) (N := N)
  have g₁ := geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
    ⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩
  have g₂ := geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
    ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩
  rw [hAL.1] at g₁
  rw [hAL.2] at g₂
  constructor
  · rw [e₁, e₂]
    exact g₁
  · rw [e₁, e₂]
    exact g₂

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem dict₂_j1 (hqN : ¬ q ∣ N) :
    (∃ h : jFun N q ∈ R.R₂.integers, R.residue₂ ⟨jFun N q, h⟩ = jGeomGen k N ^ q) ∧
    (∃ h : jQFun N q ∈ R.R₂.integers, R.residue₂ ⟨jQFun N q, h⟩ = jGeomGen k N) := by
  obtain ⟨⟨h₁, r₁⟩, ⟨h₁', r₁'⟩⟩ := dict₁_j1 R
  obtain ⟨s₁, s₂⟩ := al_swap_j1 (q := q) (N := N) hqN
  have m₂ : jFun N q ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, s₁]
    exact h₁'
  have m₂' : jQFun N q ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, s₂]
    exact h₁
  have transport : ∀ (g : ↥(modularFunctionFieldBar (N * q))) (hg : g ∈ R.R₁.integers)
      (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ∈ R.R₁.integers) (hfg : g = f)
      (c : ↥(modularFunctionFieldC k N)), R.residue₁ ⟨f, hf⟩ = c → R.ι (R.R₁.residue ⟨g, hg⟩) = c := by
    rintro g hg f hf rfl c hc
    exact hc
  refine ⟨⟨m₂, ?_⟩, ⟨m₂', ?_⟩⟩
  · rw [residue₂_apply, R.residue₂_eq]
    exact transport _ _ _ h₁' s₁ _ r₁'
  · rw [residue₂_apply, R.residue₂_eq]
    exact transport _ _ _ h₁ s₂ _ r₁

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem dict_pair_j1 (hqN : ¬ q ∣ N) :
    (∀ (g : ↥(modularFunctionFieldBar (N * q))) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      g = jQFun N q - jFun N q ^ q →
      R.residue₁ ⟨g, h₁⟩ = 0 ∧ R.residue₂ ⟨g, h₂⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q) ∧
    (∀ (g : ↥(modularFunctionFieldBar (N * q))) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      g = jFun N q - jQFun N q ^ q →
      R.residue₁ ⟨g, h₁⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q ∧ R.residue₂ ⟨g, h₂⟩ = 0) := by
  obtain ⟨⟨a₁, ra₁⟩, ⟨b₁, rb₁⟩⟩ := dict₁_j1 R
  obtain ⟨⟨a₂, ra₂⟩, ⟨b₂, rb₂⟩⟩ := dict₂_j1 R hqN
  constructor
  · rintro g h₁ h₂ rfl
    constructor
    · have hs : (⟨jQFun N q - jFun N q ^ q, h₁⟩ : ↥R.R₁.integers) = ⟨jQFun N q, b₁⟩ - ⟨jFun N q, a₁⟩ ^ q := rfl
      rw [hs, map_sub, map_pow, ra₁, rb₁, sub_self]
    · have hs : (⟨jQFun N q - jFun N q ^ q, h₂⟩ : ↥R.R₂.integers) = ⟨jQFun N q, b₂⟩ - ⟨jFun N q, a₂⟩ ^ q := rfl
      rw [hs, map_sub, map_pow, ra₂, rb₂]
  · rintro g h₁ h₂ rfl
    constructor
    · have hs : (⟨jFun N q - jQFun N q ^ q, h₁⟩ : ↥R.R₁.integers) = ⟨jFun N q, a₁⟩ - ⟨jQFun N q, b₁⟩ ^ q := rfl
      rw [hs, map_sub, map_pow, ra₁, rb₁]
    · have hs : (⟨jFun N q - jQFun N q ^ q, h₂⟩ : ↥R.R₂.integers) = ⟨jFun N q, a₂⟩ - ⟨jQFun N q, b₂⟩ ^ q := rfl
      rw [hs, map_sub, map_pow, ra₂, rb₂, sub_self]

private theorem coe_injective_j1 (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) : Function.Injective
    (fun g : ↥(R.nodeIntegersOver K w) =>
      ((g : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

private theorem exists_lift_j1 [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (f : LaurentSeries (AlgebraicClosure ℚ))
    (hf : f ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :
    ∃ g : ↥(R.nodeIntegersOver K w),
      ((g : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = f := by
  obtain ⟨g, hg, hc⟩ :=
    R.exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint W hW K w hw a ha f hf
  exact ⟨⟨g, hg⟩, hc⟩

private noncomputable def liftFun_j1 [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    ↥(R.nodeIntegersOver K w) :=
  (exists_lift_j1 R W hW K w hw a ha f f.2).choose

private theorem coe_liftFun_j1 [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    ((liftFun_j1 R W hW K w hw a ha f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = f :=
  (exists_lift_j1 R W hW K w hw a ha f f.2).choose_spec

private noncomputable def lift_j1 [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (a : k) (ha : w.evalAt (jGeomGen k N) = a) :
    ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+* ↥(R.nodeIntegersOver K w)
    where
  toFun := liftFun_j1 R W hW K w hw a ha
  map_one' := coe_injective_j1 R K w (by
    show ((liftFun_j1 R W hW K w hw a ha 1 : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = (((1 : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    rw [coe_liftFun_j1, OneMemClass.coe_one, OneMemClass.coe_one, OneMemClass.coe_one])
  map_mul' f g := coe_injective_j1 R K w (by
    show ((liftFun_j1 R W hW K w hw a ha (f * g) : ↥(modularFunctionFieldBar (N * q))) :
        LaurentSeries (AlgebraicClosure ℚ))
      = (((liftFun_j1 R W hW K w hw a ha f * liftFun_j1 R W hW K w hw a ha g : ↥(R.nodeIntegersOver K w)) :
          ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    rw [coe_liftFun_j1, MulMemClass.coe_mul, MulMemClass.coe_mul, MulMemClass.coe_mul, coe_liftFun_j1,
      coe_liftFun_j1])
  map_zero' := coe_injective_j1 R K w (by
    show ((liftFun_j1 R W hW K w hw a ha 0 : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = (((0 : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    rw [coe_liftFun_j1, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero])
  map_add' f g := coe_injective_j1 R K w (by
    show ((liftFun_j1 R W hW K w hw a ha (f + g) : ↥(modularFunctionFieldBar (N * q))) :
        LaurentSeries (AlgebraicClosure ℚ))
      = (((liftFun_j1 R W hW K w hw a ha f + liftFun_j1 R W hW K w hw a ha g : ↥(R.nodeIntegersOver K w)) :
          ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    rw [coe_liftFun_j1, AddMemClass.coe_add, AddMemClass.coe_add, AddMemClass.coe_add, coe_liftFun_j1,
      coe_liftFun_j1])

private theorem coe_lift_j1 [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    ((lift_j1 R W hW K w hw a ha f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = f :=
  coe_liftFun_j1 R W hW K w hw a ha f

private theorem lift_C_j1 [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (ϖ : ↥(coeffSubring A K)) :
    lift_j1 R W hW K w hw a ha
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
      = R.nodeConst K w ϖ :=
  coe_injective_j1 R K w (by
    show ((lift_j1 R W hW K w hw a ha _ : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = (((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) :
          LaurentSeries (AlgebraicClosure ℚ))
    rw [coe_lift_j1, coe_nodeConst]
    exact mev_C_j1 (1 * q) (coeffSubring A K) ϖ)

private theorem lift_gens_j1 [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (a : k) (ha : w.evalAt (jGeomGen k N) = a) :
    (lift_j1 R W hW K w hw a ha
        ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularFunctionFieldBar (N * q))) = jQFun N q - jFun N q ^ q ∧
    (lift_j1 R W hW K w hw a ha
        ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularFunctionFieldBar (N * q))) = jFun N q - jQFun N q ^ q := by
  have eX0 : ((jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) := by
    rw [mev_X0_j1]
    exact coeffEmb_jq _
  have eX1 : ((jQFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1) := by
    rw [mev_X1_j1, jqNModC_cast_j1 (one_mul q)]
    show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = _
    rw [coeffEmb_qExpand, coeffEmb_jq]
    rfl
  constructor
  · apply Subtype.ext
    rw [coe_lift_j1, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, eX0, eX1]
    exact map_sub (modularEval (1 * q) (coeffSubring A K)) _ _ |>.trans (by rw [map_pow])
  · apply Subtype.ext
    rw [coe_lift_j1, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, eX0, eX1]
    exact map_sub (modularEval (1 * q) (coeffSubring A K)) _ _ |>.trans (by rw [map_pow])

private theorem reg_j1 [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hqN : ¬ q ∣ N) (hreg : R.RegularityLaw W) (g : ↥(R.nodeIntegersOver K w)) :
    (R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 → 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
    (R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 → 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩)) := by
  have hss : IsSupersingularPlace q N k w := hW w hw
  have hφ : arithFrobC q k N • w = frobOnPlacesGeomLevel k N data hKr w :=
    arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w
  have hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w := by
    rw [← hφ, ← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr (arithFrobC q k N • w)]
    exact arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q N hqN k w hss
  have H := hreg.1 (g : ↥(modularFunctionFieldBar (N * q))) g.2.1.1 g.2.1.2.1 w hfix hss.2.1
    (fun V hV => R.ord_nonneg_of_mem_nodeIntegers g.2.1 hV)
  rw [← hφ] at H
  exact H

end Tuple

end SolW3_j1

set_option maxHeartbeats 3200000 in
open SolW3_j1 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ d : ↥(coeffSubring A K), redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (G' H' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (E₁ : ℕ) (w₁ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hw₁ : IsUnit w₁)
    (hGH : G' * H' =
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ E₁ * w₁)
    (hGspan : Ideal.span {
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))})
    (hHspan : Ideal.span {
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) :
    ∃ x' y' u' : ↥(R.nodeIntegersOver K w), IsUnit u' ∧ x' * y' = R.nodeConst K w ϖ ^ E₁ * u' ∧
      R.nodeResidue₁ w ⟨x', x'.2.1⟩ = 0 ∧ R.nodeResidue₂ w ⟨y', y'.2.1⟩ = 0 ∧
      R.nodeResidue₂ w ⟨x', x'.2.1⟩ ≠ 0 ∧
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x', x'.2.1⟩) = (placeRamificationJ N w : ℤ) ∧
      R.nodeResidue₁ w ⟨y', y'.2.1⟩ ≠ 0 ∧
      w.ord (R.nodeResidue₁ w ⟨y', y'.2.1⟩) = (placeRamificationJ N w : ℤ) := by
  classical
  have hss : IsSupersingularPlace q N k w := hW w hw

  have hϖ0 : red ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩

  set ϖL : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ with hϖL
  set Gexp : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ with hGexp
  set Hexp : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ with hHexp

  set τ := lift_j1 R W hW K w hw a ha with hτ
  set ρ₁ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
    (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w)) with hρ₁
  set ρ₂ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
    (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w)) with hρ₂
  have ρ₁_apply : ∀ g : ↥(R.nodeIntegersOver K w), ρ₁ g = R.nodeResidue₁ w ⟨g, g.2.1⟩ := fun g => rfl
  have ρ₂_apply : ∀ g : ↥(R.nodeIntegersOver K w), ρ₂ g = R.nodeResidue₂ w ⟨g, g.2.1⟩ := fun g => rfl

  have τϖ : τ ϖL = R.nodeConst K w ϖ := lift_C_j1 R W hW K w hw a ha ϖ
  obtain ⟨τG, τH⟩ := lift_gens_j1 R W hW K w hw a ha

  have rϖ₁ : ρ₁ (τ ϖL) = 0 := by
    rw [ρ₁_apply, nodeResidue₁_apply, residue₁_apply]
    exact residue₁_const_j1 R ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ hϖ0 _ _
      (((congrArg (fun g : ↥(R.nodeIntegersOver K w) => (g : ↥(modularFunctionFieldBar (N * q)))) τϖ).trans
        (R.coe_nodeConst K w ϖ)))
  have rϖ₂ : ρ₂ (τ ϖL) = 0 := by
    rw [ρ₂_apply, nodeResidue₂_apply]
    exact residue₂_const_j1 R ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ hϖ0 _ _
      (((congrArg (fun g : ↥(R.nodeIntegersOver K w) => (g : ↥(modularFunctionFieldBar (N * q)))) τϖ).trans
        (R.coe_nodeConst K w ϖ)))
  obtain ⟨dG, dH⟩ := dict_pair_j1 R hqN
  have rG : ρ₁ (τ Gexp) = 0 ∧ ρ₂ (τ Gexp) = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
    rw [ρ₁_apply, ρ₂_apply, nodeResidue₁_apply, nodeResidue₂_apply]
    exact dG _ _ _ τG
  have rH : ρ₁ (τ Hexp) = jGeomGen k N - (jGeomGen k N ^ q) ^ q ∧ ρ₂ (τ Hexp) = 0 := by
    rw [ρ₁_apply, ρ₂_apply, nodeResidue₁_apply, nodeResidue₂_apply]
    exact dH _ _ _ τH

  have memG : G' ∈ Ideal.span {ϖL, Gexp} := by
    rw [← hGspan]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have memG' : Gexp ∈ Ideal.span {ϖL, G'} := by
    rw [hGspan]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have memH : H' ∈ Ideal.span {ϖL, Hexp} := by
    rw [← hHspan]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have memH' : Hexp ∈ Ideal.span {ϖL, H'} := by
    rw [hHspan]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨αG, βG, eG⟩ := Ideal.mem_span_pair.mp memG
  obtain ⟨αG', βG', eG'⟩ := Ideal.mem_span_pair.mp memG'
  obtain ⟨αH, βH, eH⟩ := Ideal.mem_span_pair.mp memH
  obtain ⟨αH', βH', eH'⟩ := Ideal.mem_span_pair.mp memH'

  have x₁ : ρ₁ (τ G') = 0 := by
    rw [comb_read_j1 τ ρ₁ eG rϖ₁, rG.1, mul_zero]
  have y₂ : ρ₂ (τ H') = 0 := by
    rw [comb_read_j1 τ ρ₂ eH rϖ₂, rH.2, mul_zero]
  have x₂ : ρ₂ (τ G') = ρ₂ (τ βG) * (jGeomGen k N - (jGeomGen k N ^ q) ^ q) := by
    rw [comb_read_j1 τ ρ₂ eG rϖ₂, rG.2]
  have x₂' : jGeomGen k N - (jGeomGen k N ^ q) ^ q = ρ₂ (τ βG') * ρ₂ (τ G') := by
    rw [← rG.2]
    exact comb_read_j1 τ ρ₂ eG' rϖ₂
  have y₁ : ρ₁ (τ H') = ρ₁ (τ βH) * (jGeomGen k N - (jGeomGen k N ^ q) ^ q) := by
    rw [comb_read_j1 τ ρ₁ eH rϖ₁, rH.1]
  have y₁' : jGeomGen k N - (jGeomGen k N ^ q) ^ q = ρ₁ (τ βH') * ρ₁ (τ H') := by
    rw [← rH.1]
    exact comb_read_j1 τ ρ₁ eH' rϖ₁

  obtain ⟨hD0, hDw, hDφ⟩ := ord_frobDiff_j1 (N := N) hss
  obtain ⟨hx0, hxord⟩ := ord_eq_of_assoc_j1 (arithFrobC q k N • w) hD0 x₂ x₂'
    (reg_j1 R W hW K w hw hqN hreg (τ βG)).2 (reg_j1 R W hW K w hw hqN hreg (τ βG')).2
  obtain ⟨hy0, hyord⟩ := ord_eq_of_assoc_j1 w hD0 y₁ y₁'
    (reg_j1 R W hW K w hw hqN hreg (τ βH)).1 (reg_j1 R W hW K w hw hqN hreg (τ βH')).1

  have hprod : τ G' * τ H' = R.nodeConst K w ϖ ^ E₁ * τ w₁ := by
    rw [← map_mul, hGH, map_mul, map_pow, τϖ]
  refine ⟨τ G', τ H', τ w₁, hw₁.map τ, hprod, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ρ₁_apply]; exact x₁
  · rw [← ρ₂_apply]; exact y₂
  · rw [← ρ₂_apply]; exact hx0
  · rw [← ρ₂_apply, hxord, hDφ]
  · rw [← ρ₁_apply]; exact hy0
  · rw [← ρ₁_apply, hyord, hDw]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pair_nodeIntegersOver_ord_eq_placeRamificationJ_of_crossingPresentation (solution)
