-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d3e558f8-34e3-5954-bde4-a73bc5bc6fd1

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace SubStrictLevel

section Degrees
variable {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F'] [Algebra K' F']

theorem degree_mapDomain_of_deg_eq_one (r : Place K F → Place K' F')
    (h1 : ∀ w : Place K F, w.deg = 1) (h1' : ∀ v : Place K' F', v.deg = 1) (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  classical
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_mapDomain_index]
  · refine Finsupp.sum_congr fun w _ => ?_
    show D w * ((r w).deg : ℤ) = D w * (w.deg : ℤ)
    rw [h1, h1']
  · intro v; exact zero_mul _
  · intro v m n; exact add_mul _ _ _

end Degrees

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
  {W : Finset (Place k (modularFunctionFieldC k N))}

def IsAnn (P : PlaceSpecialization A q N data hKr k red hα hβ) (w : Place k (modularFunctionFieldC k N))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Prop :=
  P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V

theorem apply_eq_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    {w : Place k (modularFunctionFieldC k N)} {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV : IsAnn P w V) : Dt V = 0 := by
  by_contra h
  rcases hDt V (Finsupp.mem_support_iff.mpr h) with h1 | h1
  · exact hV.2.1 h1
  · exact hV.2.2 h1

theorem sub_apply_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    {w : Place k (modularFunctionFieldC k N)} {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV : IsAnn P w V) : (X - Dt) V = X V := by
  rw [Finsupp.sub_apply, apply_eq_zero_of_strict hDt hV, sub_zero]

open Classical in
theorem filter_sub_eq_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    (X - Dt).support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
      = X.support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) := by
  ext V
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨h0, hV⟩
    exact ⟨by rwa [sub_apply_of_strict X hDt hV] at h0, hV⟩
  · rintro ⟨h0, hV⟩
    exact ⟨by rwa [sub_apply_of_strict X hDt hV], hV⟩

open Classical in
theorem filter_eq_empty_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    Dt.support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) = ∅ := by
  ext V
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finset.notMem_empty, iff_false, not_and]
  intro h0 h1 h2 h3
  exact h0 (apply_eq_zero_of_strict hDt ⟨h1, h2, h3⟩)

variable (dat : R.AnnulusDatumLevel W)

open Classical in
theorem circleDeg_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) (d : ℕ) :
    dat.circleDeg (X - Dt) w d = dat.circleDeg X w d := by
  unfold ProlongationTuple.AnnulusDatumLevel.circleDeg
  rw [filter_sub_eq_of_strict X hDt w]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [sub_apply_of_strict X hDt (Finset.mem_filter.mp hV).2]

open Classical in
theorem circleDeg_eq_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) (d : ℕ) :
    dat.circleDeg Dt w d = 0 := by
  unfold ProlongationTuple.AnnulusDatumLevel.circleDeg
  rw [filter_eq_empty_of_strict hDt w, Finset.sum_empty]

open Classical in
theorem depthMoment_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    dat.depthMoment (X - Dt) w = dat.depthMoment X w := by
  unfold ProlongationTuple.AnnulusDatumLevel.depthMoment
  rw [filter_sub_eq_of_strict X hDt w]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [sub_apply_of_strict X hDt (Finset.mem_filter.mp hV).2]

open Classical in
theorem annulusDeg_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    ProlongationTuple.AnnulusDatumLevel.annulusDeg (P := P) (X - Dt) w = ProlongationTuple.AnnulusDatumLevel.annulusDeg (P := P) X w := by
  unfold ProlongationTuple.AnnulusDatumLevel.annulusDeg
  rw [filter_sub_eq_of_strict X hDt w]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [sub_apply_of_strict X hDt (Finset.mem_filter.mp hV).2]

open Classical in
theorem endShareFst_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    dat.endShareFst (X - Dt) w = dat.endShareFst X w := by
  unfold ProlongationTuple.AnnulusDatumLevel.endShareFst
  rw [circleDeg_sub_of_strict dat X hDt w 0]

open Classical in
theorem endShareSnd_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    dat.endShareSnd (X - Dt) w = dat.endShareSnd X w := by
  unfold ProlongationTuple.AnnulusDatumLevel.endShareSnd
  rw [circleDeg_sub_of_strict dat X hDt w]

open Classical in
theorem endShareFst_eq_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    dat.endShareFst Dt w = 0 := by
  unfold ProlongationTuple.AnnulusDatumLevel.endShareFst
  rw [circleDeg_eq_zero_of_strict dat hDt w 0]
  simp

open Classical in
theorem endShareSnd_eq_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    dat.endShareSnd Dt w = 0 := by
  unfold ProlongationTuple.AnnulusDatumLevel.endShareSnd
  rw [circleDeg_eq_zero_of_strict dat hDt w]
  simp

open Classical in
theorem endOrderFst_sub_of_strict (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W) (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    dat.endOrderFst a (X - Dt) w = dat.endOrderFst a X w := by
  unfold ProlongationTuple.AnnulusDatumLevel.endOrderFst
  rw [endShareFst_sub_of_strict dat X hDt w]

open Classical in
theorem endOrderSnd_sub_of_strict (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W) (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    dat.endOrderSnd a (X - Dt) w = dat.endOrderSnd a X w := by
  unfold ProlongationTuple.AnnulusDatumLevel.endOrderSnd
  rw [endShareSnd_sub_of_strict dat X hDt w]

theorem chainVal_zero (w : Place k (modularFunctionFieldC k N)) (d : ℕ) :
    dat.chainVal ⟨0, 0, fun _ _ => 0⟩ w d = 0 := by
  unfold ProlongationTuple.AnnulusDatumLevel.chainVal
  split_ifs <;> rfl

open Classical in
theorem endOrderFst_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    dat.endOrderFst ⟨0, 0, fun _ _ => 0⟩ Dt w = 0 := by
  unfold ProlongationTuple.AnnulusDatumLevel.endOrderFst ProlongationTuple.AnnulusDatumLevel.endSlopeFst
  rw [chainVal_zero, chainVal_zero, endShareFst_eq_zero_of_strict dat hDt w]
  simp

open Classical in
theorem endOrderSnd_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k N)) :
    dat.endOrderSnd ⟨0, 0, fun _ _ => 0⟩ Dt w = 0 := by
  unfold ProlongationTuple.AnnulusDatumLevel.endOrderSnd ProlongationTuple.AnnulusDatumLevel.endSlopeSnd
  rw [chainVal_zero, chainVal_zero, endShareSnd_eq_zero_of_strict dat hDt w]
  simp

open Classical in
theorem angFactor_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    dat.angFactor w hw (X - Dt) = dat.angFactor w hw X := by
  unfold ProlongationTuple.AnnulusDatumLevel.angFactor
  have hprod : (∏ V ∈ (X - Dt).support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
      V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))) ^ (-((X - Dt) V)))
      = ∏ V ∈ X.support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
        V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))) ^ (-(X V)) := by
    rw [filter_sub_eq_of_strict X hDt w]
    refine Finset.prod_congr rfl fun V hV => ?_
    rw [sub_apply_of_strict X hDt (Finset.mem_filter.mp hV).2]
  simp only [hprod, depthMoment_sub_of_strict dat X hDt w]
  all_goals first
    | rfl
    | (congr 1 <;> first | rfl | exact Subsingleton.elim _ _ | (funext h; rfl))

open Classical in
theorem nodeUnitOf_sub_of_strict (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W) (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) :
    dat.nodeUnitOf a (X - Dt) = dat.nodeUnitOf a X := by
  funext s
  unfold ProlongationTuple.AnnulusDatumLevel.nodeUnitOf
  simp only [annulusDeg_sub_of_strict X hDt, endOrderFst_sub_of_strict dat a X hDt,
    endOrderSnd_sub_of_strict dat a X hDt, angFactor_sub_of_strict dat X hDt]

open Classical in
theorem fstDiv_sub (X Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : P.fstDiv (X - Dt) = P.fstDiv X - P.fstDiv Dt := by
  unfold PlaceSpecialization.fstDiv
  rw [sub_eq_add_neg, Finsupp.filter_add, Finsupp.filter_neg, ← sub_eq_add_neg]

open Classical in
theorem sndDiv_sub (X Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : P.sndDiv (X - Dt) = P.sndDiv X - P.sndDiv Dt := by
  unfold PlaceSpecialization.sndDiv
  rw [sub_eq_add_neg, Finsupp.filter_add, Finsupp.filter_neg, ← sub_eq_add_neg]

end SubStrictLevel

open SubStrictLevel in
open Classical in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (dat : R.AnnulusDatumLevel W)
    (X Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hdeg₁ : Divisor.degree (P.fstDiv Dt) = 0) (hdeg₂ : Divisor.degree (P.sndDiv Dt) = 0)
    (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W)
    (ha : dat.IsTwistOf a X) :
    dat.IsTwistOf a (X - Dt) ∧
      dat.spData a (X - Dt) = dat.spData a X - P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) Dt := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  unfold ProlongationTuple.AnnulusDatumLevel.IsTwistOf at ha ⊢
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [fstDiv_sub, map_sub, hdeg₁, sub_zero, ha.1]
    simp only [endOrderFst_sub_of_strict dat a X hDt]
  · rw [sndDiv_sub, map_sub, hdeg₂, sub_zero, ha.2.1]
    simp only [endOrderSnd_sub_of_strict dat a X hDt]
  · intro w hw d hd hd'
    rw [circleDeg_sub_of_strict dat X hDt w d]
    exact ha.2.2 w hw d hd hd'
  ·
    unfold ProlongationTuple.AnnulusDatumLevel.spData PlaceSpecialization.glueData
    simp only [Prod.mk_sub_mk, sub_zero, nodeUnitOf_sub_of_strict dat a X hDt, fstDiv_sub, sndDiv_sub,
      Finsupp.mapDomain_sub, endOrderFst_sub_of_strict dat a X hDt, endOrderSnd_sub_of_strict dat a X hDt]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · show _ = _
      abel
    · show _ = _
      abel

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict (solution)
