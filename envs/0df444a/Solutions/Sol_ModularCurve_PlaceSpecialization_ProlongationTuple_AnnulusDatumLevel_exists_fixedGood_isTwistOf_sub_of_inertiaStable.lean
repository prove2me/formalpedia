-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedGood_isTwistOf_sub_of_inertiaStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b8a0e317-a76e-5183-8776-5c273bb272c2

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedGood_isTwistOf_sub_of_inertiaStable
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace TwistLevel

theorem sum_laplace_Ico (f : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Ico 1 n, (f (d - 1) - 2 * f d + f (d + 1)) = f 0 - f 1 - f (n - 1) + f n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega), ih hm]
      obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

theorem tent_sum (n : ℕ) (δ : ℚ) (h0 : 0 ≤ δ) (hn : δ ≤ n) :
    ∑ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) = 1 := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hlt : δ < ⌊δ⌋₊ + 1 := Nat.lt_floor_add_one δ
  have hmn : ⌊δ⌋₊ ≤ n := Nat.floor_le_of_le (by exact_mod_cast hn)

  have hterm : ∀ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) =
      (if d = ⌊δ⌋₊ then 1 - (δ - ⌊δ⌋₊) else 0) + (if d = ⌊δ⌋₊ + 1 then δ - ⌊δ⌋₊ else 0) := by
    intro d _
    by_cases h1 : d = ⌊δ⌋₊
    · subst h1
      have h2 : ¬ (⌊δ⌋₊ = ⌊δ⌋₊ + 1) := by omega
      rw [if_pos rfl, if_neg h2, add_zero, abs_of_nonneg (by linarith)]
      exact max_eq_right (by linarith)
    · rw [if_neg h1, zero_add]
      by_cases h2 : d = ⌊δ⌋₊ + 1
      · subst h2
        rw [if_pos rfl, abs_of_nonpos (by push_cast; linarith)]
        push_cast
        rw [max_eq_right (by linarith)]
        ring
      · rw [if_neg h2]
        apply max_eq_left

        rcases Nat.lt_or_gt_of_ne h1 with h | h
        ·
          have : (d : ℚ) + 1 ≤ ⌊δ⌋₊ := by exact_mod_cast h
          rw [abs_of_nonneg (by linarith)]
          linarith
        ·
          have : (⌊δ⌋₊ : ℚ) + 2 ≤ d := by exact_mod_cast (show ⌊δ⌋₊ + 2 ≤ d by omega)
          rw [abs_of_nonpos (by linarith)]
          linarith
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' , Finset.sum_ite_eq']
  have hm : ⌊δ⌋₊ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos hm]
  by_cases hm1 : ⌊δ⌋₊ + 1 ∈ Finset.range (n + 1)
  · rw [if_pos hm1]; ring
  · rw [if_neg hm1, add_zero]

    have h3 : ⌊δ⌋₊ = n := by rw [Finset.mem_range] at hm1; omega
    have h4 : δ = n := le_antisymm hn (by rw [← h3]; exact hfl)
    rw [h4]; simp

theorem tent_one (d : ℕ) : max 0 (1 - |(1 : ℚ) - (d : ℚ)|) = if d = 1 then 1 else 0 := by
  by_cases h : d = 1
  · subst h; simp
  · rw [if_neg h]
    apply max_eq_left
    rcases Nat.lt_or_gt_of_ne h with h0 | h2
    · have : d = 0 := by omega
      subst this; simp
    · have : (2 : ℚ) ≤ d := by exact_mod_cast h2
      rw [abs_of_nonpos (by linarith)]; linarith

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

section PS
variable (P : PlaceSpecialization A q N data hKr k red hα hβ)

omit [PerfectField k] in
theorem not_isStrictSnd_of_isStrictFst {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h1 : P.IsStrictFst V) : ¬ P.IsStrictSnd V := fun h2 =>
  h1.2 (by rw [h1.1, ← h2.1])

omit [PerfectField k] in

theorem degree_eq_sum_support (D : (Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) : Divisor.degree D = ∑ V ∈ D.support, D V := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]
  simp

omit [PerfectField k] in
theorem degree_filter (D : (Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → Prop)
    [DecidablePred p] : Divisor.degree (D.filter p) = ∑ V ∈ D.support with p V, D V := by
  classical
  rw [degree_eq_sum_support, Finsupp.support_filter]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finsupp.filter_apply_pos]
  exact (Finset.mem_filter.mp hV).2

open Classical in
omit [PerfectField k] in

theorem degree_decomp {W : Finset (Place k (modularFunctionFieldC k N))} (D : (Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hgood : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) :
    Divisor.degree D = Divisor.degree (P.fstDiv D) + Divisor.degree (P.sndDiv D) +
      ∑ w ∈ W, ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V := by
  classical
  have hF : Divisor.degree (P.fstDiv D) = ∑ V ∈ D.support with P.IsStrictFst V, D V := by
    unfold PlaceSpecialization.fstDiv; convert degree_filter D P.IsStrictFst
  have hS : Divisor.degree (P.sndDiv D) = ∑ V ∈ D.support with P.IsStrictSnd V, D V := by
    unfold PlaceSpecialization.sndDiv; convert degree_filter D P.IsStrictSnd
  rw [hF, hS, degree_eq_sum_support]
  have step1 := (Finset.sum_filter_add_sum_filter_not D.support P.IsStrictFst (fun V => D V)).symm
  have step2 := (Finset.sum_filter_add_sum_filter_not (D.support.filter fun V => ¬ P.IsStrictFst V)
    P.IsStrictSnd (fun V => D V)).symm
  rw [step1, step2, Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  · refine Finset.sum_congr (Finset.filter_congr fun V _ => ?_) fun _ _ => rfl
    exact ⟨fun h => h.2, fun h => ⟨fun h1 => not_isStrictSnd_of_isStrictFst P h1 h, h⟩⟩
  · rw [← Finset.sum_fiberwise_of_maps_to (s := D.support.filter fun V => ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
      (t := W) (g := P.reduceFst) (f := fun V => D V) ?_]
    · refine Finset.sum_congr rfl fun w _ => Finset.sum_congr ?_ fun _ _ => rfl
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun V _ => by tauto
    · intro V hV
      rw [Finset.mem_filter] at hV
      rcases hgood V hV.1 with h | h | h
      · exact absurd h hV.2.1
      · exact absurd h hV.2.2
      · exact h

end PS

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
  {W : Finset (Place k (modularFunctionFieldC k N))} (dat : R.AnnulusDatumLevel W)

open Classical in

noncomputable def tentFn (w : Place k (modularFunctionFieldC k N)) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : ℚ :=
  if P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V then max 0 (1 - |dat.depthQ V - d|) else 0

noncomputable def circleHom (w : Place k (modularFunctionFieldC k N)) (d : ℕ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) →+ ℚ :=
  Finsupp.liftAddHom fun V => (AddMonoidHom.mulRight (tentFn dat w d V)).comp (Int.castAddHom ℚ)

open Classical in
theorem circleDeg_eq_circleHom (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (w : Place k (modularFunctionFieldC k N)) (d : ℕ) :
    dat.circleDeg D w d = circleHom dat w d D := by
  unfold ProlongationTuple.AnnulusDatumLevel.circleDeg circleHom
  rw [Finsupp.liftAddHom_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun V _ => ?_
  unfold tentFn
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mulRight, Function.comp_apply, Int.coe_castAddHom]
  split_ifs <;> simp

theorem circleHom_single (w : Place k (modularFunctionFieldC k N)) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (n : ℤ) :
    circleHom dat w d (Finsupp.single V n) = n * tentFn dat w d V := by
  unfold circleHom
  rw [Finsupp.liftAddHom_apply_single]
  simp

open Classical in
theorem tentFn_of_strict (w : Place k (modularFunctionFieldC k N)) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (h : P.IsStrictFst V ∨ P.IsStrictSnd V) :
    tentFn dat w d V = 0 := by
  unfold tentFn
  rw [if_neg]
  rintro ⟨-, h1, h2⟩
  rcases h with h | h
  · exact h1 h
  · exact h2 h

end TwistLevel

set_option maxHeartbeats 16000000 in
open TwistLevel in
open Classical in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P)
    (dat : R.AnnulusDatumLevel W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    (hD1 : ∀ w ∈ W, 2 ≤ dat.width w →
        ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
          dat.depthQ V = 1)
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hEstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
          (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = E)
    (hEsupp : ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (B : Finset (Place k (modularFunctionFieldC k N))) :
    ∃ Dfix : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      Divisor.degree Dfix = 0 ∧
      (∀ V ∈ Dfix.support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
        ((P.IsStrictFst V ∧ P.reduceFst V ∉ B) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∉ B) ∨
          (P.reduceFst V ∈ W ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ dat.depthQ V = 1))) ∧
      ∃ a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W,
        dat.IsTwistOf a ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - Dfix) := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set Xd : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) with hXd

  have hint : ∀ w ∈ W, ∀ d : ℕ, (dat.circleDeg Xd w d).den = 1 :=
    (ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
      dat hKfix hdepthQ hdepthσ Xd hEstab).1

  have hXdepth : ∀ V ∈ Xd.support, ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width (P.reduceFst V) := by
    intro V hV h1 h2
    have hw : P.reduceFst V ∈ W := by
      rcases hEsupp V hV with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    obtain ⟨h0, hlt, -⟩ := hdepthQ (P.reduceFst V) hw V rfl h1 h2
    exact ⟨h0, hlt⟩
  have hw1 : ∀ w : ↥W, 1 ≤ dat.width w.1 := fun w => hwidth w.1 w.2

  set r : ↥W → ℕ → ℤ := fun w d => (dat.circleDeg Xd w.1 d).num with hr
  have hrq : ∀ (w : ↥W) (d : ℕ), (r w d : ℚ) = dat.circleDeg Xd w.1 d := fun w d =>
    Rat.coe_int_num_of_den_eq_one (hint w.1 w.2 d)

  have hGG := ModularCurve.ChainDirichlet.exists_depthOne_correction_dirichlet (fun w : ↥W => dat.width w.1) hw1 r
  obtain ⟨ν, c, hν1, hc0, hcn, hclap⟩ := hGG
  have hν0 : ∀ w : ↥W, ¬ 2 ≤ dat.width w.1 → ν w = 0 := fun w h => hν1 w (by have := hw1 w; omega)

  let a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W :=
    ⟨0, 0, fun w d => if hw : w ∈ W then c ⟨w, hw⟩ d else 0⟩
  have hchain : ∀ (w : ↥W) (d : ℕ), dat.chainVal a w.1 d = c w d := by
    intro w d
    unfold ProlongationTuple.AnnulusDatumLevel.chainVal
    by_cases hd0 : d = 0
    · rw [if_pos hd0, hd0, hc0]
    · rw [if_neg hd0]
      by_cases hdw : dat.width w.1 ≤ d
      · rw [if_pos hdw, hcn w d hdw]
      · rw [if_neg hdw]
        show (if hw : w.1 ∈ W then c ⟨w.1, hw⟩ d else 0) = c w d
        rw [dif_pos w.2]

  have hFAM := ModularCurve.PlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq P hqN B 1 1
  obtain ⟨Q₁, Q₂, hQ₁s, hQ₂s, -, -, hQ₁B, hQ₂B, hQ₁fix, hQ₂fix⟩ := hFAM
  set V₁ := Q₁ 0 with hV₁
  set V₂ := Q₂ 0 with hV₂
  have hV₁s : P.IsStrictFst V₁ := hQ₁s 0
  have hV₂s : P.IsStrictSnd V₂ := hQ₂s 0
  have hnF2 : ¬ P.IsStrictFst V₂ := fun h => not_isStrictSnd_of_isStrictFst P h hV₂s
  have hnS1 : ¬ P.IsStrictSnd V₁ := not_isStrictSnd_of_isStrictFst P hV₁s

  have hVex : ∀ w : ↥W, ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), 2 ≤ dat.width w.1 →
      P.reduceFst V = w.1 ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧ dat.depthQ V = 1 := by
    intro w
    by_cases h2 : 2 ≤ dat.width w.1
    · obtain ⟨V, hV⟩ := hD1 w.1 w.2 h2
      exact ⟨V, fun _ => hV⟩
    · exact ⟨V₁, fun h => absurd h h2⟩
  choose Vf hVf using hVex

  set S : ℤ := ∑ w ∈ W.attach, ν w with hS
  set m : ℤ := -(Divisor.degree (P.fstDiv Xd)) - S - ∑ w ∈ W, dat.endOrderFst a Xd w with hm
  set Dann : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := ∑ w ∈ W.attach, ν w • Finsupp.single (Vf w) (1 : ℤ) with hDann
  set Dfix : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := Dann + m • Finsupp.single V₂ (1 : ℤ) - (m + S) • Finsupp.single V₁ (1 : ℤ) with hDfix

  have hDann_apply : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), Dann V = ∑ w ∈ W.attach, ν w * (Finsupp.single (Vf w) (1 : ℤ) V) := by
    intro V
    rw [hDann, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul]
  have hVf_ns : ∀ w : ↥W, ν w ≠ 0 → P.reduceFst (Vf w) = w.1 ∧ ¬ P.IsStrictFst (Vf w) ∧ ¬ P.IsStrictSnd (Vf w) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Vf w = Vf w) ∧
      dat.depthQ (Vf w) = 1 := by
    intro w hν
    have h2 : 2 ≤ dat.width w.1 := by
      by_contra h2
      exact hν (hν0 w h2)
    exact hVf w h2
  have hDann_strict : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst V ∨ P.IsStrictSnd V → Dann V = 0 := by
    intro V hV
    rw [hDann_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases hν : ν w = 0
    · rw [hν, zero_mul]
    · rw [Finsupp.single_apply, if_neg, mul_zero]
      rintro rfl
      obtain ⟨-, h1, h2, -⟩ := hVf_ns w hν
      rcases hV with h | h
      · exact h1 h
      · exact h2 h
  have hDann_supp : ∀ V ∈ Dann.support, ∃ w : ↥W, ν w ≠ 0 ∧ V = Vf w := by
    intro V hV
    rw [Finsupp.mem_support_iff, hDann_apply] at hV
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
    refine ⟨w, fun h => hw (by rw [h, zero_mul]), ?_⟩
    by_contra hne
    apply hw
    rw [Finsupp.single_apply, if_neg (fun h => hne h.symm), mul_zero]

  have hDfixsupp : ∀ V ∈ Dfix.support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
      ((P.IsStrictFst V ∧ P.reduceFst V ∉ B) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∉ B) ∨
        (P.reduceFst V ∈ W ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ dat.depthQ V = 1)) := by
    intro V hV
    rw [hDfix] at hV
    rcases Finset.mem_union.mp (Finsupp.support_sub hV) with h | h
    · rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
      · obtain ⟨w, hν, rfl⟩ := hDann_supp V h
        obtain ⟨hr, h1, h2, hfix, hdep⟩ := hVf_ns w hν
        exact ⟨hfix, Or.inr (Or.inr ⟨hr ▸ w.2, h1, h2, hdep⟩)⟩
      · have hV2 : V = V₂ := by
          have := Finsupp.support_smul h
          rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at this
          exact this
        subst hV2
        exact ⟨hQ₂fix 0, Or.inr (Or.inl ⟨hV₂s, hQ₂B 0⟩)⟩
    · have hV1 : V = V₁ := by
        have := Finsupp.support_smul h
        rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at this
        exact this
      subst hV1
      exact ⟨hQ₁fix 0, Or.inl ⟨hV₁s, hQ₁B 0⟩⟩

  have hdeg1 : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), Divisor.degree (Finsupp.single V (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = 1 := fun V => by
    rw [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]; simp
  have hdegDann : Divisor.degree Dann = S := by
    rw [hDann, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_zsmul, hdeg1, smul_eq_mul, mul_one]
  have hdegDfix : Divisor.degree Dfix = 0 := by
    rw [hDfix, map_sub, map_add, map_zsmul, map_zsmul, hdegDann, hdeg1, hdeg1]
    ring
  refine ⟨Dfix, hdegDfix, hDfixsupp, a, ?_⟩

  set D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := Xd - Dfix with hD

  have htent : ∀ (w : ↥W) (d : ℕ) (w' : ↥W), ν w' * tentFn dat w.1 d (Vf w') =
      if w' = w then (if d = 1 then (ν w' : ℚ) else 0) else 0 := by
    intro w d w'
    by_cases hν : ν w' = 0
    · rw [hν]; simp
    · obtain ⟨hr, h1, h2, -, hdep⟩ := hVf_ns w' hν
      unfold tentFn
      by_cases hww : w' = w
      · subst hww
        rw [if_pos ⟨hr, h1, h2⟩, hdep, tent_one, if_pos rfl]
        split_ifs <;> simp
      · rw [if_neg, if_neg hww, mul_zero]
        rintro ⟨hr', -, -⟩
        exact hww (Subtype.ext (hr.symm.trans hr'))
  have hcDfix : ∀ (w : ↥W) (d : ℕ), dat.circleDeg Dfix w.1 d = if d = 1 then (ν w : ℚ) else 0 := by
    intro w d
    rw [circleDeg_eq_circleHom, hDfix, map_sub, map_add, map_zsmul, map_zsmul, hDann, map_sum,
      circleHom_single, circleHom_single, tentFn_of_strict dat _ _ _ (Or.inl hV₁s),
      tentFn_of_strict dat _ _ _ (Or.inr hV₂s), mul_zero, smul_zero, smul_zero, add_zero, sub_zero]
    rw [Finset.sum_congr rfl (fun w' _ => by rw [map_zsmul, circleHom_single, zsmul_eq_mul, Int.cast_one, one_mul]),
      Finset.sum_congr rfl (fun w' _ => htent w d w'), Finset.sum_ite_eq' (W.attach) w, if_pos (Finset.mem_attach _ _)]
  have hcD : ∀ (w : ↥W) (d : ℕ), dat.circleDeg D w.1 d = dat.circleDeg Xd w.1 d - if d = 1 then (ν w : ℚ) else 0 := by
    intro w d
    rw [hD, circleDeg_eq_circleHom, map_sub, ← circleDeg_eq_circleHom, ← circleDeg_eq_circleHom, hcDfix]
  have hcD0 : ∀ w : ↥W, dat.circleDeg D w.1 0 = dat.circleDeg Xd w.1 0 := fun w => by
    rw [hcD]; simp
  have hcDn : ∀ w : ↥W, dat.circleDeg D w.1 (dat.width w.1) = dat.circleDeg Xd w.1 (dat.width w.1) := fun w => by
    rw [hcD]
    by_cases h2 : 2 ≤ dat.width w.1
    · rw [if_neg (by omega), sub_zero]
    · rw [hν0 w h2]; simp
  have hintD : ∀ (w : ↥W) (d : ℕ), (dat.circleDeg D w.1 d).den = 1 := by
    intro w d
    rw [hcD, ← hrq]
    split_ifs
    · exact_mod_cast (show ((r w d - ν w : ℤ) : ℚ).den = 1 from Rat.den_intCast _)
    · rw [sub_zero]; exact Rat.den_intCast _

  have hshF : ∀ w : ↥W, dat.endShareFst D w.1 = r w 0 := fun w => by
    unfold ProlongationTuple.AnnulusDatumLevel.endShareFst
    rw [if_pos (hintD w 0), hcD0]
  have hshS : ∀ w : ↥W, dat.endShareSnd D w.1 = r w (dat.width w.1) := fun w => by
    unfold ProlongationTuple.AnnulusDatumLevel.endShareSnd
    rw [if_pos (hintD w _), hcDn]
  have hshFX : ∀ w : ↥W, dat.endShareFst Xd w.1 = r w 0 := fun w => by
    unfold ProlongationTuple.AnnulusDatumLevel.endShareFst
    rw [if_pos (hint w.1 w.2 0)]
  have hoF : ∀ w : ↥W, dat.endOrderFst a D w.1 = dat.endOrderFst a Xd w.1 := fun w => by
    unfold ProlongationTuple.AnnulusDatumLevel.endOrderFst
    rw [hshF, hshFX]
  have hslF : ∀ w : ↥W, dat.endSlopeFst a w.1 = c w 1 := fun w => by
    unfold ProlongationTuple.AnnulusDatumLevel.endSlopeFst
    rw [hchain, hchain, hc0, sub_zero]
  have hslS : ∀ w : ↥W, dat.endSlopeSnd a w.1 = c w (dat.width w.1 - 1) := fun w => by
    unfold ProlongationTuple.AnnulusDatumLevel.endSlopeSnd
    rw [hchain, hchain, hcn w _ le_rfl, sub_zero]

  have hfst_apply : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.fstDiv D V = P.fstDiv Xd V + (m + S) * (Finsupp.single V₁ (1 : ℤ) V) := by
    intro V
    unfold PlaceSpecialization.fstDiv
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hV : P.IsStrictFst V
    · rw [if_pos hV, if_pos hV, hD, Finsupp.sub_apply, hDfix, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.smul_apply, hDann_strict V (Or.inl hV), smul_eq_mul, smul_eq_mul]
      have h2 : Finsupp.single V₂ (1 : ℤ) V = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hnF2 hV
      rw [h2]
      ring
    · rw [if_neg hV, if_neg hV]
      have h1 : Finsupp.single V₁ (1 : ℤ) V = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hV hV₁s
      rw [h1]
      ring
  have hsnd_apply : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.sndDiv D V = P.sndDiv Xd V - m * (Finsupp.single V₂ (1 : ℤ) V) := by
    intro V
    unfold PlaceSpecialization.sndDiv
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hV : P.IsStrictSnd V
    · rw [if_pos hV, if_pos hV, hD, Finsupp.sub_apply, hDfix, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.smul_apply, hDann_strict V (Or.inr hV), smul_eq_mul, smul_eq_mul]
      have h2 : Finsupp.single V₁ (1 : ℤ) V = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hnS1 hV
      rw [h2]
      ring
    · rw [if_neg hV, if_neg hV]
      have h1 : Finsupp.single V₂ (1 : ℤ) V = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hV hV₂s
      rw [h1]
      ring
  have hfst : P.fstDiv D = P.fstDiv Xd + (m + S) • Finsupp.single V₁ 1 := by
    ext V
    rw [hfst_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hsnd : P.sndDiv D = P.sndDiv Xd - m • Finsupp.single V₂ 1 := by
    ext V
    rw [hsnd_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  have hdegF : Divisor.degree (P.fstDiv D) = Divisor.degree (P.fstDiv Xd) + (m + S) := by
    rw [hfst, map_add, map_zsmul, hdeg1, smul_eq_mul, mul_one]
  have hdegS : Divisor.degree (P.sndDiv D) = Divisor.degree (P.sndDiv Xd) - m := by
    rw [hsnd, map_sub, map_zsmul, hdeg1, smul_eq_mul, mul_one]

  have E1 : Divisor.degree (P.fstDiv D) = -∑ w ∈ W, dat.endOrderFst a D w := by
    rw [hdegF, ← Finset.sum_attach W, Finset.sum_congr rfl (fun w _ => hoF w), Finset.sum_attach W (fun w => dat.endOrderFst a Xd w), hm]
    ring

  have E3 : ∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
      dat.circleDeg D w d = -((dat.chainVal a w (d - 1) - 2 * dat.chainVal a w d + dat.chainVal a w (d + 1) : ℤ) : ℚ) := by
    intro w hw d hd1 hd2
    have hcl := hclap ⟨w, hw⟩ d hd1 hd2
    rw [hchain ⟨w, hw⟩, hchain ⟨w, hw⟩, hchain ⟨w, hw⟩, hcl, hcD ⟨w, hw⟩ d, ← hrq ⟨w, hw⟩ d]
    split_ifs <;> push_cast <;> ring

  have hDdepth : ∀ V ∈ D.support, ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width (P.reduceFst V) := by
    intro V hV h1 h2
    rw [hD] at hV
    rcases Finset.mem_union.mp (Finsupp.support_sub hV) with h | h
    · exact hXdepth V h h1 h2
    · rcases (hDfixsupp V h).2 with h' | h' | h'
      · exact absurd h'.1 h1
      · exact absurd h'.1 h2
      · obtain ⟨hw, -, -, hdep⟩ := h'
        rw [hdep]
        refine ⟨one_pos, ?_⟩
        have : (2 : ℚ) ≤ dat.width (P.reduceFst V) := by

          rw [hDfix] at h
          rcases Finset.mem_union.mp (Finsupp.support_sub h) with h | h
          · rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
            · obtain ⟨w', hν, rfl⟩ := hDann_supp V h
              obtain ⟨hr, -⟩ := hVf_ns w' hν
              have h2 : 2 ≤ dat.width w'.1 := by
                by_contra h2; exact hν (hν0 w' h2)
              rw [hr]; exact_mod_cast h2
            · exfalso
              have := Finsupp.support_smul h
              rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at this
              exact h2 (this ▸ hV₂s)
          · exfalso
            have := Finsupp.support_smul h
            rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at this
            exact h1 (this ▸ hV₁s)
        linarith
  have hann : ∀ w : ↥W,
      ∑ V ∈ D.support with (P.reduceFst V = w.1 ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ)
        = dat.endOrderFst a D w.1 + dat.endOrderSnd a D w.1 := by
    intro w
    have hn1 : 1 ≤ dat.width w.1 := hw1 w

    have h1 : ∑ V ∈ D.support with (P.reduceFst V = w.1 ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ)
        = ∑ d ∈ Finset.range (dat.width w.1 + 1), dat.circleDeg D w.1 d := by
      unfold ProlongationTuple.AnnulusDatumLevel.circleDeg
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun V hV => ?_
      obtain ⟨hVs, hVw, hV1, hV2⟩ := Finset.mem_filter.mp hV
      obtain ⟨h0, hlt⟩ := hDdepth V hVs hV1 hV2
      rw [hVw] at hlt
      rw [← Finset.mul_sum, tent_sum _ _ h0.le (by exact_mod_cast hlt.le), mul_one]

    have h2 : ∑ d ∈ Finset.range (dat.width w.1 + 1), dat.circleDeg D w.1 d
        = dat.circleDeg D w.1 0 + ∑ d ∈ Finset.Ico 1 (dat.width w.1), dat.circleDeg D w.1 d +
          dat.circleDeg D w.1 (dat.width w.1) := by
      rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn1]
    have h3 : dat.circleDeg D w.1 0 = dat.endShareFst D w.1 := by
      rw [hshF, hrq, hcD0]
    have h4 : dat.circleDeg D w.1 (dat.width w.1) = dat.endShareSnd D w.1 := by
      rw [hshS, hrq, hcDn]
    have h5 : ∑ d ∈ Finset.Ico 1 (dat.width w.1), dat.circleDeg D w.1 d
        = (dat.endSlopeFst a w.1 + dat.endSlopeSnd a w.1 : ℤ) := by
      rw [Finset.sum_congr rfl (fun d hd => E3 w.1 w.2 d (Finset.mem_Ico.mp hd).1
        (by have := (Finset.mem_Ico.mp hd).2; omega))]
      rw [Finset.sum_neg_distrib]
      have hL := congrArg (fun z : ℤ => (z : ℚ))
        (sum_laplace_Ico (fun d => dat.chainVal a w.1 d) (dat.width w.1) hn1)
      push_cast at hL ⊢
      rw [hL, hslF, hslS, hchain, hchain, hchain, hchain, hc0, hcn w _ le_rfl]
      push_cast; ring
    rw [h1, h2, h3, h4, h5]
    unfold ProlongationTuple.AnnulusDatumLevel.endOrderFst ProlongationTuple.AnnulusDatumLevel.endOrderSnd
    push_cast; ring

  have hdeg0 : Divisor.degree D = 0 := by
    rw [hD, map_sub, hdegDfix, sub_zero]
    exact Divisor.mem_degZero.mp E.2
  have hgoodD : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W := by
    intro V hV
    rw [hD] at hV
    rcases Finset.mem_union.mp (Finsupp.support_sub hV) with h | h
    · exact hEsupp V h
    · rcases (hDfixsupp V h).2 with h' | h' | h'
      · exact Or.inl h'.1
      · exact Or.inr (Or.inl h'.1)
      · exact Or.inr (Or.inr h'.1)
  have hdec := degree_decomp (P := P) (W := W) D hgoodD
  have E2 : Divisor.degree (P.sndDiv D) = -∑ w ∈ W, dat.endOrderSnd a D w := by
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hdec
    simp only [hdeg0] at hc
    push_cast at hc
    rw [← Finset.sum_attach W, Finset.sum_congr rfl (fun w _ => hann w), Finset.sum_add_distrib,
      Finset.sum_attach W (fun w => (dat.endOrderFst a D w : ℚ)), Finset.sum_attach W (fun w => (dat.endOrderSnd a D w : ℚ))] at hc
    have hE1 := congrArg (fun z : ℤ => (z : ℚ)) E1
    push_cast at hE1
    have : (Divisor.degree (P.sndDiv D) : ℚ) = -∑ w ∈ W, (dat.endOrderSnd a D w : ℚ) := by linarith
    exact_mod_cast this
  exact ⟨E1, E2, E3⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedGood_isTwistOf_sub_of_inertiaStable
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedGood_isTwistOf_sub_of_inertiaStable (solution)
