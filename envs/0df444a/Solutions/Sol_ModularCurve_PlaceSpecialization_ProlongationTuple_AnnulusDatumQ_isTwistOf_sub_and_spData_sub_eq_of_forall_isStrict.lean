-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e6542e55-aad5-5274-8efa-e0b293bd2649

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace S12EL
namespace Tss

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

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
  {W : Finset (Place k (modularFunctionFieldC k 1))}

def IsAnn (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (w : Place k (modularFunctionFieldC k 1))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V

theorem apply_eq_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    {w : Place k (modularFunctionFieldC k 1)} {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hV : IsAnn P w V) : Dt V = 0 := by
  by_contra h
  rcases hDt V (Finsupp.mem_support_iff.mpr h) with h1 | h1
  · exact hV.2.1 h1
  · exact hV.2.2 h1

theorem sub_apply_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    {w : Place k (modularFunctionFieldC k 1)} {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hV : IsAnn P w V) : (X - Dt) V = X V := by
  rw [Finsupp.sub_apply, apply_eq_zero_of_strict hDt hV, sub_zero]

open Classical in
theorem filter_sub_eq_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
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
theorem filter_eq_empty_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    Dt.support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) = ∅ := by
  ext V
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finset.notMem_empty, iff_false, not_and]
  intro h0 h1 h2 h3
  exact h0 (apply_eq_zero_of_strict hDt ⟨h1, h2, h3⟩)

variable (dat : R.AnnulusDatumQ W)

open Classical in
theorem circleDeg_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) :
    dat.circleDeg (X - Dt) w d = dat.circleDeg X w d := by
  unfold ProlongationTuple.AnnulusDatumQ.circleDeg
  rw [filter_sub_eq_of_strict X hDt w]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [sub_apply_of_strict X hDt (Finset.mem_filter.mp hV).2]

open Classical in
theorem circleDeg_eq_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) :
    dat.circleDeg Dt w d = 0 := by
  unfold ProlongationTuple.AnnulusDatumQ.circleDeg
  rw [filter_eq_empty_of_strict hDt w, Finset.sum_empty]

open Classical in
theorem depthMoment_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    dat.depthMoment (X - Dt) w = dat.depthMoment X w := by
  unfold ProlongationTuple.AnnulusDatumQ.depthMoment
  rw [filter_sub_eq_of_strict X hDt w]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [sub_apply_of_strict X hDt (Finset.mem_filter.mp hV).2]

open Classical in
theorem annulusDeg_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    ProlongationTuple.AnnulusDatum.annulusDeg (P := P) (X - Dt) w = ProlongationTuple.AnnulusDatum.annulusDeg (P := P) X w := by
  unfold ProlongationTuple.AnnulusDatum.annulusDeg
  rw [filter_sub_eq_of_strict X hDt w]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [sub_apply_of_strict X hDt (Finset.mem_filter.mp hV).2]

open Classical in
theorem endShareFst_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    dat.endShareFst (X - Dt) w = dat.endShareFst X w := by
  unfold ProlongationTuple.AnnulusDatumQ.endShareFst
  rw [circleDeg_sub_of_strict dat X hDt w 0]

open Classical in
theorem endShareSnd_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    dat.endShareSnd (X - Dt) w = dat.endShareSnd X w := by
  unfold ProlongationTuple.AnnulusDatumQ.endShareSnd
  rw [circleDeg_sub_of_strict dat X hDt w]

open Classical in
theorem endShareFst_eq_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    dat.endShareFst Dt w = 0 := by
  unfold ProlongationTuple.AnnulusDatumQ.endShareFst
  rw [circleDeg_eq_zero_of_strict dat hDt w 0]
  simp

open Classical in
theorem endShareSnd_eq_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    dat.endShareSnd Dt w = 0 := by
  unfold ProlongationTuple.AnnulusDatumQ.endShareSnd
  rw [circleDeg_eq_zero_of_strict dat hDt w]
  simp

open Classical in
theorem endOrderFst_sub_of_strict (a : ProlongationTuple.TwistVector (k := k) W) (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    dat.endOrderFst a (X - Dt) w = dat.endOrderFst a X w := by
  unfold ProlongationTuple.AnnulusDatumQ.endOrderFst
  rw [endShareFst_sub_of_strict dat X hDt w]

open Classical in
theorem endOrderSnd_sub_of_strict (a : ProlongationTuple.TwistVector (k := k) W) (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    dat.endOrderSnd a (X - Dt) w = dat.endOrderSnd a X w := by
  unfold ProlongationTuple.AnnulusDatumQ.endOrderSnd
  rw [endShareSnd_sub_of_strict dat X hDt w]

theorem chainVal_zero (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) :
    dat.chainVal ⟨0, 0, fun _ _ => 0⟩ w d = 0 := by
  unfold ProlongationTuple.AnnulusDatumQ.chainVal
  split_ifs <;> rfl

open Classical in
theorem endOrderFst_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    dat.endOrderFst ⟨0, 0, fun _ _ => 0⟩ Dt w = 0 := by
  unfold ProlongationTuple.AnnulusDatumQ.endOrderFst ProlongationTuple.AnnulusDatumQ.endSlopeFst
  rw [chainVal_zero, chainVal_zero, endShareFst_eq_zero_of_strict dat hDt w]
  simp

open Classical in
theorem endOrderSnd_zero_of_strict {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) (w : Place k (modularFunctionFieldC k 1)) :
    dat.endOrderSnd ⟨0, 0, fun _ _ => 0⟩ Dt w = 0 := by
  unfold ProlongationTuple.AnnulusDatumQ.endOrderSnd ProlongationTuple.AnnulusDatumQ.endSlopeSnd
  rw [chainVal_zero, chainVal_zero, endShareSnd_eq_zero_of_strict dat hDt w]
  simp

open Classical in
theorem angFactor_sub_of_strict (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) :
    dat.angFactor w hw (X - Dt) = dat.angFactor w hw X := by
  unfold ProlongationTuple.AnnulusDatumQ.angFactor
  have hprod : (∏ V ∈ (X - Dt).support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
      V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))) ^ (-((X - Dt) V)))
      = ∏ V ∈ X.support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
        V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))) ^ (-(X V)) := by
    rw [filter_sub_eq_of_strict X hDt w]
    refine Finset.prod_congr rfl fun V hV => ?_
    rw [sub_apply_of_strict X hDt (Finset.mem_filter.mp hV).2]
  simp only [hprod, depthMoment_sub_of_strict dat X hDt w]
  all_goals first
    | rfl
    | (congr 1 <;> first | rfl | exact Subsingleton.elim _ _ | (funext h; rfl))

open Classical in
theorem nodeUnitOf_sub_of_strict (a : ProlongationTuple.TwistVector (k := k) W) (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V) :
    dat.nodeUnitOf a (X - Dt) = dat.nodeUnitOf a X := by
  funext s
  unfold ProlongationTuple.AnnulusDatumQ.nodeUnitOf
  simp only [annulusDeg_sub_of_strict X hDt, endOrderFst_sub_of_strict dat a X hDt,
    endOrderSnd_sub_of_strict dat a X hDt, angFactor_sub_of_strict dat X hDt]

open Classical in
theorem fstDiv_sub (X Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : P.fstDiv (X - Dt) = P.fstDiv X - P.fstDiv Dt := by
  unfold PlaceSpecialization.fstDiv
  rw [sub_eq_add_neg, Finsupp.filter_add, Finsupp.filter_neg, ← sub_eq_add_neg]

open Classical in
theorem sndDiv_sub (X Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : P.sndDiv (X - Dt) = P.sndDiv X - P.sndDiv Dt := by
  unfold PlaceSpecialization.sndDiv
  rw [sub_eq_add_neg, Finsupp.filter_add, Finsupp.filter_neg, ← sub_eq_add_neg]

end S12EL.Tss

open S12EL.Tss in
open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumQ W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hwidthj : ∀ w ∈ W, dat.width w = jWidth (w.evalAt (jGeomGen k 1)))
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = dat.depthQ V)
    (hcusp : dat.cusp ∉ W) (hcuspφ : arithFrobC q k 1 • dat.cusp = dat.cusp)
    (hunif : ∀ w ∈ W,
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single w (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifFst w)) ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single (arithFrobC q k 1 • w) (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifSnd w)))
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    [hK : ∀ w : Place k (modularFunctionFieldC k 1), FiniteDimensional ℚ ↥(dat.K w)]
    (ϖ : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hϖ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (eK : Place k (modularFunctionFieldC k 1) → ℕ) (heK : ∀ w ∈ W, 1 ≤ eK w)
    (ε : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w)
    (hε1 : ∀ w ∈ W, NodeLocalized.redRestrict red (dat.K w) (ε w) = 1)
    (u : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), IsUnit (u w hw) ∧
        (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw)
    (hmax : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
          M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y})
    (hbr : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
        (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
        (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
        ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (hu0 : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (1 * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k))
    (hlam : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).y.2.1⟩
        / dat.unifFst w) ((dat.lam w : kˣ) : k))
    (hmu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      (arithFrobC q k 1 • w).HasValue
        (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).x.2.1⟩
          / dat.unifSnd w) ((dat.mu w : kˣ) : k))
    (X Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (a : ProlongationTuple.TwistVector (k := k) W)
    (ha : dat.IsTwistOf a X) (hz : dat.IsTwistOf ⟨0, 0, fun _ _ => 0⟩ Dt) :
    dat.IsTwistOf a (X - Dt) ∧
      dat.spData a (X - Dt) = dat.spData a X - P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) Dt := by
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  unfold ProlongationTuple.AnnulusDatumQ.IsTwistOf at ha hz ⊢
  have hdegBar : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), w.deg = 1 :=
    deg_eq_one_modularFunctionFieldBar (1 * q)
  have hdegC : ∀ v : Place k ↥(modularFunctionFieldC k 1), v.deg = 1 := place_deg_eq_one_of_isAlgClosed k 1

  have hdeg₁ : Divisor.degree (P.fstDiv Dt) = 0 := by
    rw [hz.1]
    simp only [endOrderFst_zero_of_strict dat hDt, Finset.sum_const_zero, neg_zero]
  have hdeg₂ : Divisor.degree (P.sndDiv Dt) = 0 := by
    rw [hz.2.1]
    simp only [endOrderSnd_zero_of_strict dat hDt, Finset.sum_const_zero, neg_zero]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [fstDiv_sub, map_sub, hdeg₁, sub_zero, ha.1]
    simp only [endOrderFst_sub_of_strict dat a X hDt]
  · rw [sndDiv_sub, map_sub, hdeg₂, sub_zero, ha.2.1]
    simp only [endOrderSnd_sub_of_strict dat a X hDt]
  · intro w hw d hd hd'
    rw [circleDeg_sub_of_strict dat X hDt w d]
    exact ha.2.2 w hw d hd hd'
  ·
    unfold ProlongationTuple.AnnulusDatumQ.spData PlaceSpecialization.glueData
    have hm₁ : Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv Dt)) = 0 := by
      rw [degree_mapDomain_of_deg_eq_one _ hdegBar hdegC, hdeg₁]
    have hm₂ : Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv Dt)) = 0 := by
      rw [degree_mapDomain_of_deg_eq_one _ hdegBar hdegC, hdeg₂]
    simp only [Prod.mk_sub_mk, sub_zero, nodeUnitOf_sub_of_strict dat a X hDt, fstDiv_sub, sndDiv_sub,
      Finsupp.mapDomain_sub, map_sub, hm₁, hm₂]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · show _ = _
      abel
    · show _ = _
      abel

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict (solution)
