-- Prove2me | solution 1 for MazurReduction.dedekind_torsion_card_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T12:00:05.757813+00:00
-- url     : https://prove2.me/submissions/3c3298fe-103c-420f-b71f-c79db218307c

import Mathlib
import Definitions.Def_MazurReduction_DedekindResidueTypes
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_MazurReduction_PointTransport
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_MazurReduction_leading_coefficient_root_bound

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# The residue map on `v`-integral elements of the fraction field

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R`.
An element of `K` of `v`-adic valuation at most `1` is congruent to an element of `R` modulo
elements of valuation `< 1` (`exists_valuation_sub_lt_of_integer`), and the class in
`R ⧸ v.asIdeal` of such an approximant does not depend on its choice.  This file packages the
resulting *residue map* as a ring homomorphism
`residueHom : (v.valuation K).integer →+* R ⧸ v.asIdeal`
on the subring of `v`-integral elements of `K`, extending `Ideal.Quotient.mk v.asIdeal`
(`residueHom_algebraMap`); an unfolding requires only *some* approximant (`residueHom_eq`).

It also provides the `R`-algebra structure on `(v.valuation K).integer` and the `Field`
instance on `R ⧸ v.asIdeal` (the ideal is maximal).
-/

section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/- Implementation note (upstreaming): Mathlib deliberately keeps `Ideal.Quotient.field` a *local*
instance (cf. `RingTheory/DedekindDomain/Different.lean`, `RingTheory/Artinian/Module.lean`),
since maximality of a general ideal is not inferable.  Here the ideal is `v.asIdeal` for a
height-one prime `v` of a Dedekind domain, whose maximality is an instance
(`HeightOneSpectrum.isMaximal`), so the `Field` instance is keyed on `v` and safe to make global;
be prepared to demote it to a local instance if upstream review prefers that. -/


noncomputable instance instAlgebraIntegerValuationSubring : Algebra R (v.valuation K).integer :=
  ((algebraMap R K).codRestrict (v.valuation K).integer fun r ↦ v.valuation_le_one r).toAlgebra

instance : IsScalarTower R (v.valuation K).integer K :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

@[simp] lemma coe_algebraMap_integer (r : R) :
    ((algebraMap R (v.valuation K).integer r : (v.valuation K).integer) : K)
      = algebraMap R K r := rfl

/-- The distinguished `R`-approximant of a `v`-integral element of `K` (an element of `R`
congruent to it modulo valuation `< 1`).  Implementation detail of `residueHom`; use that (and
`residueHom_eq`) instead. -/
noncomputable def residueAux (x : (v.valuation K).integer) : R :=
  (v.exists_valuation_sub_lt_of_integer x.2 1).choose

private lemma valuation_sub_residueAux_lt (x : (v.valuation K).integer) :
    v.valuation K (algebraMap R K (residueAux v x) - x) < 1 :=
  lt_of_lt_of_eq (v.exists_valuation_sub_lt_of_integer x.2 1).choose_spec Units.val_one

/-- Two `R`-approximants of the same `v`-integral element agree modulo `v`. -/
private lemma mk_eq_mk_of_close {x : (v.valuation K).integer} {a b : R}
    (ha : v.valuation K (algebraMap R K a - x) < 1)
    (hb : v.valuation K (algebraMap R K b - x) < 1) :
    Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b := by
  rw [Ideal.Quotient.eq, ← intValuation_lt_one_iff_mem, ← valuation_of_algebraMap (K := K),
    Algebra.cast, map_sub (algebraMap R K)]
  calc v.valuation K (algebraMap R K a - algebraMap R K b)
      = v.valuation K ((algebraMap R K a - x) - (algebraMap R K b - x)) := by ring_nf
    _ ≤ max (v.valuation K (algebraMap R K a - x)) (v.valuation K (algebraMap R K b - x)) :=
        Valuation.map_sub _ _ _
    _ < 1 := max_lt ha hb

/-- An approximant of a `v`-integral element is itself `v`-integral in `K`. -/
private lemma valuation_le_one_of_close {x : (v.valuation K).integer} {a : R}
    (ha : v.valuation K (algebraMap R K a - x) < 1) :
    v.valuation K (algebraMap R K a) ≤ 1 := by
  calc v.valuation K (algebraMap R K a)
      = v.valuation K ((algebraMap R K a - x) + x) := by ring_nf
    _ ≤ max (v.valuation K (algebraMap R K a - x)) (v.valuation K x) := Valuation.map_add _ _ _
    _ ≤ 1 := max_le ha.le x.2

/-- The **residue map** on the `v`-integral elements of `K`, with values in the residue field
`R ⧸ v.asIdeal`: the class of any `R`-approximant within valuation `< 1`.  It extends
`Ideal.Quotient.mk v.asIdeal` (`residueHom_algebraMap`). -/
noncomputable def residueHom : (v.valuation K).integer →+* R ⧸ v.asIdeal where
  toFun x := Ideal.Quotient.mk v.asIdeal (residueAux v x)
  map_one' := by
    rw [mk_eq_mk_of_close v (valuation_sub_residueAux_lt v 1) (b := 1) (by simp), map_one]
  map_mul' x y := by
    rw [← map_mul]
    refine mk_eq_mk_of_close v (valuation_sub_residueAux_lt v (x * y)) ?_
    have hx := valuation_sub_residueAux_lt v x
    have hy := valuation_sub_residueAux_lt v y
    calc v.valuation K (algebraMap R K (residueAux v x * residueAux v y) - (x * y : _))
        = v.valuation K (algebraMap R K (residueAux v x) * (algebraMap R K (residueAux v y) - y)
            + (y : K) * (algebraMap R K (residueAux v x) - x)) := by push_cast; ring_nf
      _ ≤ max (v.valuation K (algebraMap R K (residueAux v x)
              * (algebraMap R K (residueAux v y) - y)))
            (v.valuation K ((y : K) * (algebraMap R K (residueAux v x) - x))) :=
          Valuation.map_add _ _ _
      _ < 1 := by
          rw [map_mul, map_mul]
          refine max_lt (lt_of_le_of_lt (mul_le_of_le_one_left' ?_) hy)
            (lt_of_le_of_lt (mul_le_of_le_one_left' y.2) hx)
          exact valuation_le_one_of_close v hx
  map_zero' := by
    rw [mk_eq_mk_of_close v (valuation_sub_residueAux_lt v 0) (b := 0) (by simp), map_zero]
  map_add' x y := by
    rw [← map_add]
    refine mk_eq_mk_of_close v (valuation_sub_residueAux_lt v (x + y)) ?_
    have hx := valuation_sub_residueAux_lt v x
    have hy := valuation_sub_residueAux_lt v y
    calc v.valuation K (algebraMap R K (residueAux v x + residueAux v y) - (x + y : _))
        = v.valuation K ((algebraMap R K (residueAux v x) - x)
            + (algebraMap R K (residueAux v y) - y)) := by push_cast; ring_nf
      _ ≤ _ := Valuation.map_add _ _ _
      _ < 1 := max_lt hx hy

/-- Unfolding lemma for `residueHom`: the residue of `x` is the class of *any* `R`-approximant
of `x` within valuation `< 1`. -/
lemma residueHom_eq {x : (v.valuation K).integer} {a : R}
    (h : v.valuation K (algebraMap R K a - x) < 1) :
    residueHom v x = Ideal.Quotient.mk v.asIdeal a :=
  mk_eq_mk_of_close v (valuation_sub_residueAux_lt v x) h

@[simp] lemma residueHom_algebraMap (r : R) :
    residueHom v (algebraMap R (v.valuation K).integer r) = Ideal.Quotient.mk v.asIdeal r :=
  residueHom_eq v (by simp)

end IsDedekindDomain.HeightOneSpectrum

end

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Uses the generic integral-coordinate lemmas of Anthropic's FLT,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/

open WithZero
namespace MazurReduction

/-- Boundary: discrete valuation coordinates for integral Weierstrass models
over any field. Named downstream consumer: the unramified torsion-kernel
bound for the cubic-field quotient used in the order-18 exclusion. -/
theorem discrete_abscissa_valuation_ge_two
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (W : WeierstrassCurve v.valuationSubring) {x y : K}
    (h : (W.map v.valuationSubring.subtype).toAffine.Equation x y)
    (hx : x ∉ v.valuationSubring) : exp (2 : ℤ) ≤ v x := by
  let A := v.valuationSubring
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
  have hy0 : y ≠ 0 := WeierstrassCurve.Affine.Y_ne_zero_of_X_notMem W h hx
  obtain ⟨hr, hrnot⟩ := WeierstrassCurve.Affine.X_cubed_div_Y_sq_notMem_nonunits W h hx
  have hr0 : x ^ 3 / y ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hy0)
  have hrv : v (x ^ 3 / y ^ 2) = 1 := by
    apply le_antisymm
    · exact hr
    · apply (inv_le_one₀ (show 0 < v (x ^ 3 / y ^ 2) from
        (zero_lt_iff).mpr ((map_ne_zero v).mpr hr0))).mp
      rw [← map_inv₀]
      exact A.inv_mem_of_notMem_nonunits hrnot
  have hex : exp (log (v x)) = v x := exp_log ((map_ne_zero v).mpr hx0)
  have hey : exp (log (v y)) = v y := exp_log ((map_ne_zero v).mpr hy0)
  have heq : 3 * log (v x) = 2 * log (v y) := by
    rw [map_div₀, map_pow, map_pow, ← hex, ← hey] at hrv
    simp only [← exp_nsmul, ← exp_sub, ← exp_zero, exp_inj, nsmul_eq_mul] at hrv
    omega
  have hxlt : 1 < v x := lt_of_not_ge hx
  rw [← hex, ← exp_zero, exp_lt_exp] at hxlt
  rw [← hex, exp_le_exp]
  omega

end MazurReduction

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

open WithZero
namespace MazurReduction

/-- Boundary: division-polynomial nonvanishing at an unramified odd prime
of any discretely valued field. Named downstream consumer: the order-18
cubic-field good-reduction torsion-kernel exclusion. -/
theorem unramified_odd_prime_division_nonzero
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hv : v (p : K) = exp (-1 : ℤ))
    (W : WeierstrassCurve v.valuationSubring) {x y : K}
    (h : (W.map v.valuationSubring.subtype).toAffine.Equation x y)
    (hx : x ∉ v.valuationSubring) :
    ((W.map v.valuationSubring.subtype).preΨ' p).eval x ≠ 0 := by
  let Wk := W.map v.valuationSubring.subtype
  have hp0 : (p : K) ≠ 0 := by
    intro hz
    have he : exp (-1 : ℤ) = 0 := hv.symm.trans (by rw [hz, map_zero])
    exact exp_ne_zero he
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hlc : (Wk.preΨ' p).leadingCoeff = p := by
    rw [Wk.leadingCoeff_preΨ' hp0, if_neg (Nat.not_even_iff_odd.mpr hpodd)]
  have hc : ∀ i, v ((Wk.preΨ' p).coeff i) ≤ 1 := by
    intro i
    dsimp only [Wk]
    rw [W.map_preΨ', Polynomial.coeff_map]
    exact ((W.preΨ' p).coeff i).property
  intro hr
  have hb := leading_coefficient_root_bound v (Wk.preΨ' p)
    (Wk.natDegree_preΨ'_pos hp hp0) hc hr (lt_of_not_ge hx)
  rw [hlc, hv] at hb
  have he : exp (1 : ℤ) ≤ exp (-1 : ℤ) * v x := by
    calc
      exp (1 : ℤ) = exp (-1 : ℤ) * exp (2 : ℤ) := by rw [← exp_add]; norm_num
      _ ≤ exp (-1 : ℤ) * v x :=
        mul_le_mul_of_nonneg_left (discrete_abscissa_valuation_ge_two v W h hx) zero_le
  have hpos : 1 < exp (1 : ℤ) := by rw [← exp_zero, exp_lt_exp]; norm_num
  exact (not_le_of_gt (hpos.trans_le he)) hb

end MazurReduction

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

open WithZero IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine
namespace MazurReduction

/-- Boundary: good reduction at an unramified odd prime of a discretely
valued field kills no nonzero torsion point. Named downstream consumer:
the cubic-field reduction in the order-18 exclusion. -/
theorem unramified_torsion_kernel_zero
    {K : Type*} [Field K] [DecidableEq K]
    (v : Valuation K ℤᵐ⁰) (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (hv : v (p : K) = WithZero.exp (-1 : ℤ))
    [DecidableEq (ResidueField v.valuationSubring)]
    (W : WeierstrassCurve v.valuationSubring)
    [(W.map v.valuationSubring.subtype).IsElliptic]
    (hΔ : (W.map (residue v.valuationSubring)).Δ ≠ 0)
    (P : (W.map v.valuationSubring.subtype).toAffine.Point)
    (hP : IsOfFinAddOrder P)
    (hred : WeierstrassCurve.reduceHom hΔ P = 0) : P = 0 := by
  classical
  let A := v.valuationSubring
  let F := ResidueField A
  have hpzero : (p : F) = 0 := by
    have hm : (p : A) ∈ maximalIdeal A := by
      apply v.mem_maximalIdeal_iff.mpr
      change v (p : K) < 1
      rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    have hz := (residue_eq_zero_iff (p : A)).mpr hm
    simpa only [map_natCast] using hz
  letI : CharP F p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpzero
  by_contra hP0
  have hn0 : addOrderOf P ≠ 0 := hP.addOrderOf_pos.ne'
  have hn1 : addOrderOf P ≠ 1 := fun h => hP0 (AddMonoid.addOrderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hn1
  let Q := (addOrderOf P / q) • P
  have hQorder : addOrderOf Q = q := by
    exact orderOf_pow_orderOf_div (x := Multiplicative.ofAdd P) hn0 hqdvd
  have hQred : WeierstrassCurve.reduceHom hΔ Q = 0 := by
    dsimp only [Q]
    rw [map_nsmul, hred, nsmul_zero]
  have hQq : q • Q = 0 := by rw [← hQorder]; exact addOrderOf_nsmul_eq_zero Q
  generalize hQdef : Q = R at hQorder hQred hQq
  cases R with
  | zero =>
    have hz : addOrderOf (0 : (W.map A.subtype).toAffine.Point) = q := hQorder
    exact hq.ne_one (by simpa only [addOrderOf_zero] using hz.symm)
  | some x y h =>
    have hx : x ∉ A := by
      intro hx
      have hs : WeierstrassCurve.reduceHom hΔ (.some x y h) ≠ 0 := by
        change WeierstrassCurve.reducePoint hΔ (.some x y h) ≠ 0
        rw [WeierstrassCurve.reducePoint_some_of_mem hΔ h hx]
        exact Point.some_ne_zero _
      exact hs hQred
    by_cases hqp : q = p
    · rw [hqp] at hQq
      have hz := (Point.nsmul_some_eq_zero_iff_eval_prePsi
        (W.map A.subtype) ((Fact.out : p.Prime).odd_of_ne_two (by omega)) h).mp hQq
      exact unramified_odd_prime_division_nonzero v p hp hv W h.1 hx hz
    · have hqres : (q : F) ≠ 0 := by
        intro hz
        have hdiv := (CharP.cast_eq_zero_iff F p q).mp hz
        exact hqp ((Nat.dvd_prime hq).mp hdiv |>.resolve_left (Fact.out : p.Prime).ne_one).symm
      exact hx (WeierstrassCurve.X_mem_of_nsmul_eq_zero' W hqres h hQq)

end MazurReduction

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Uses Michael Stoll's residueHom as integrated in MazurTheorem, with its
original Apache-2.0 attribution retained in the imported source module.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
namespace MazurReduction

/-- Boundary: identify the canonical valuation-ring residue field with the
Dedekind residue field, compatibly with Stoll's explicit residue map.
Named downstream consumer: the order-18 cubic-field point-count bound. -/
theorem dedekind_residue_equiv
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    ∃ e : ResidueField (v.valuation K).valuationSubring ≃+* (R ⧸ v.asIdeal),
      e.toRingHom.comp (residue (v.valuation K).valuationSubring) = residueHom v := by
  let w := v.valuation K
  let A := w.valuationSubring
  let f : A →+* (R ⧸ v.asIdeal) := residueHom v
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨⟨algebraMap R K r, v.valuation_le_one r⟩, ?_⟩
    exact residueHom_algebraMap v r
  have hker : RingHom.ker f = maximalIdeal A := by
    ext a
    rw [RingHom.mem_ker, w.mem_maximalIdeal_iff]
    obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer a.property 1
    have hclose : w (algebraMap R K r - (a : K)) < 1 := hr
    change residueHom v a = 0 ↔ w (a : K) < 1
    rw [residueHom_eq v hclose, Ideal.Quotient.eq_zero_iff_mem,
      ← v.valuation_lt_one_iff_mem (K := K)]
    constructor
    · intro h
      calc
        w (a : K) = w (algebraMap R K r - (algebraMap R K r - a)) := by congr 1; ring
        _ ≤ max (w (algebraMap R K r)) (w (algebraMap R K r - a)) := w.map_sub _ _
        _ < 1 := max_lt h hclose
    · intro h
      calc
        w (algebraMap R K r) = w ((algebraMap R K r - a) + a) := by congr 1; ring
        _ ≤ max (w (algebraMap R K r - a)) (w (a : K)) := w.map_add _ _
        _ < 1 := max_lt hclose h
  let e := (Ideal.quotEquivOfEq hker.symm).trans (f.quotientKerEquivOfSurjective hf)
  refine ⟨e, ?_⟩
  ext a
  change e (Ideal.Quotient.mk (maximalIdeal A) a) = f a
  simp [e]

end MazurReduction

open MazurReduction
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open scoped WeierstrassCurve.Affine

/-- Boundary: full torsion over a fraction field injects into the finite
special fibre at an unramified odd prime. Named downstream consumer:
the order-18 cubic-field 21-point bound. -/
theorem solution
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (hv : v.valuation K (p : K) = exp (-1 : ℤ))
    (W : WeierstrassCurve R) [(W.map (algebraMap R K)).IsElliptic]
    [(W.map (algebraMap R (R ⧸ v.asIdeal))).IsElliptic] :
    Finite (AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point) ∧
      Nat.card (AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point) ∣
        Nat.card (W.map (algebraMap R (R ⧸ v.asIdeal))).toAffine.Point := by
  classical
  let w := v.valuation K
  let A := w.valuationSubring
  let F := ResidueField A
  let i : R →+* A := (algebraMap R K).codRestrict A.toSubring (fun r => v.valuation_le_one r)
  let WA := W.map i
  have hi : A.subtype.comp i = algebraMap R K := rfl
  have hWk : WA.map A.subtype = W.map (algebraMap R K) := by
    dsimp only [WA]
    rw [WeierstrassCurve.map_map, hi]
  letI : (WA.map A.subtype).IsElliptic := hWk.symm ▸ inferInstance
  obtain ⟨er, her⟩ := dedekind_residue_equiv (K := K) v
  let fR : A →+* (R ⧸ v.asIdeal) := residueHom v
  have hfi : fR.comp i = algebraMap R (R ⧸ v.asIdeal) := by
    ext r
    exact residueHom_algebraMap v r
  have hmod : (WA.map (residue A)).map er.toRingHom = W.map (algebraMap R (R ⧸ v.asIdeal)) := by
    dsimp only [WA]
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map,
      her, hfi]
  have hΔ : (WA.map (residue A)).Δ ≠ 0 := by
    intro hz
    have hg : (W.map (algebraMap R (R ⧸ v.asIdeal))).Δ ≠ 0 :=
      isUnit_iff_ne_zero.mp (W.map (algebraMap R (R ⧸ v.asIdeal))).isUnit_Δ
    apply hg
    rw [← hmod, WeierstrassCurve.map_Δ, hz, map_zero]
  letI : Algebra A (R ⧸ v.asIdeal) := fR.toAlgebra
  let σ : F ≃ₐ[A] (R ⧸ v.asIdeal) := AlgEquiv.ofRingEquiv (f := er) (by
    intro a
    exact DFunLike.congr_fun her a)
  let eF : (WA.map (residue A)).toAffine.Point ≃+
      (W.map (algebraMap R (R ⧸ v.asIdeal))).toAffine.Point :=
    (curvePointCongr (by ext <;> rfl)).trans
      ((pointBaseChangeEquiv WA.toAffine σ).trans
        (curvePointCongr (by
          change WA.map fR = W.map (algebraMap R (R ⧸ v.asIdeal))
          dsimp only [WA]
          rw [WeierstrassCurve.map_map, hfi])))
  let eK : (W.map (algebraMap R K)).toAffine.Point ≃+ (WA.map A.subtype).toAffine.Point :=
    curvePointCongr (congrArg WeierstrassCurve.toAffine hWk.symm)
  let f : AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point →+
      (WA.map (residue A)).toAffine.Point :=
    (WeierstrassCurve.reduceHom hΔ).comp
      (eK.toAddMonoidHom.comp (AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point).subtype)
  have hf : Function.Injective f := by
    intro P Q hPQ
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply eK.injective
    rw [map_zero]
    apply unramified_torsion_kernel_zero w p hp hv WA hΔ
    · exact eK.toAddMonoidHom.isOfFinAddOrder (P - Q).property
    · change f (P - Q) = 0
      rw [map_sub, hPQ, sub_self]
  letI : Finite (WA.map (residue A)).toAffine.Point :=
    Finite.of_equiv (W.map (algebraMap R (R ⧸ v.asIdeal))).toAffine.Point eF.symm.toEquiv
  refine ⟨Finite.of_injective f hf, ?_⟩
  rw [← Nat.card_congr eF.toEquiv]
  exact AddSubgroup.card_dvd_of_injective f hf

