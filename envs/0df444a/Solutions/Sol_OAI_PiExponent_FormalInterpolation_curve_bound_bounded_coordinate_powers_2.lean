-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.curve_bound_bounded_coordinate_powers
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-24T03:57:47.470852+00:00
-- url     : https://prove2.me/submissions/ff70371c-d38e-4c77-9dab-16e725e581ce

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.NormNum

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

noncomputable section

/- The shifted point is the obstruction. The curve-bound calculation uses
   inversion of the rational parameter, rather than classifying places.
   Reindexing finsum needs no separate finite-support argument. -/

abbrev cpShiftedIdeal : Ideal (MvPolynomial (Fin 1) Complex) :=
  Ideal.span {MvPolynomial.X 0 - 1}

lemma cpShiftedFinite :
    Module.Finite Complex (MvPolynomial (Fin 1) Complex ⧸ cpShiftedIdeal) := by
  let q := Ideal.Quotient.mkₐ Complex cpShiftedIdeal
  have hx : q (MvPolynomial.X 0) = 1 := by
    have hg : q (MvPolynomial.X 0 - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simpa only [map_sub, map_one, sub_eq_zero] using hg
  have hq (p : MvPolynomial (Fin 1) Complex) :
      q p = algebraMap Complex (MvPolynomial (Fin 1) Complex ⧸ cpShiftedIdeal)
        (MvPolynomial.eval (fun _ => 1) p) := by
    induction p using MvPolynomial.induction_on with
    | C c => simp [q]
    | add p r hp hr => simpa only [map_add] using congrArg₂ (· + ·) hp hr
    | mul_X p i hp =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [map_mul, MvPolynomial.eval_X, mul_one, hx, hp]
  have hs : Function.Surjective
      (algebraMap Complex (MvPolynomial (Fin 1) Complex ⧸ cpShiftedIdeal)) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨MvPolynomial.eval (fun _ => 1) p, (hq p).symm⟩
  exact Module.Finite.of_surjective
    (Algebra.linearMap Complex (MvPolynomial (Fin 1) Complex ⧸ cpShiftedIdeal)) hs

lemma cpShiftedNoPower (s n : Nat) (hs : 0 < s) :
    (MvPolynomial.X (0 : Fin 1)) ^ n ∉ cpShiftedIdeal ^ s := by
  intro hmem
  let e := MvPolynomial.eval (fun _ : Fin 1 => (1 : Complex))
  have hI : cpShiftedIdeal ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    change e (MvPolynomial.X 0 - 1) = 0
    simp [e]
  have hz : e ((MvPolynomial.X (0 : Fin 1)) ^ n) = 0 :=
    hI (Ideal.pow_le_self (Nat.ne_of_gt hs) hmem)
  simpa [e] using hz

/- Pullback permutes normalized places, preserving also surjectivity. -/
def cpPlacePull {E : Type} [Field E] [Algebra Complex E]
    (a : E ≃ₐ[Complex] E) (nu : PolynomialCurvePlace E) : PolynomialCurvePlace E :=
  ⟨nu.1.comap a.toAlgHom.toRingHom, by
    constructor
    · intro c hc
      change nu.1 (a (algebraMap Complex E c)) = 0
      rw [a.commutes]
      exact nu.2.1 c hc
    · intro k
      obtain ⟨f, hf⟩ := nu.2.2 k
      refine ⟨a.symm f, ?_⟩
      change nu.1 (a (a.symm f)) = (k : WithTop Int)
      simpa only [AlgEquiv.apply_symm_apply] using hf⟩

def cpPlaceEquiv {E : Type} [Field E] [Algebra Complex E]
    (a : E ≃ₐ[Complex] E) : PolynomialCurvePlace E ≃ PolynomialCurvePlace E where
  toFun := cpPlacePull a
  invFun := cpPlacePull a.symm
  left_inv nu := by
    apply Subtype.ext
    apply AddValuation.ext
    intro f
    change nu.1 (a (a.symm f)) = nu.1 f
    rw [AlgEquiv.apply_symm_apply]
  right_inv nu := by
    apply Subtype.ext
    apply AddValuation.ext
    intro f
    change nu.1 (a.symm (a f)) = nu.1 f
    rw [AlgEquiv.symm_apply_apply]

lemma cpPoleOne {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin 1 → E) :
    polynomialCurvePole nu x (fun _ => 1) =
      max 0 (-(polynomialCurveOrder nu (x 0) : Real)) := by
  unfold polynomialCurvePole
  simp only [Rat.cast_one, div_one]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    cases i with
    | none => exact le_max_left _ _
    | some i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact le_max_right 0 (-(polynomialCurveOrder nu (x 0) : Real))
  · apply max_le
    · exact Finset.le_sup'
          (fun i : Option (Fin 1) => i.elim (0 : Real)
            (fun j => -(polynomialCurveOrder nu (x j) : Real)))
          (Finset.mem_univ (none : Option (Fin 1)))
    · exact Finset.le_sup'
          (fun i : Option (Fin 1) => i.elim (0 : Real)
            (fun j => -(polynomialCurveOrder nu (x j) : Real)))
          (Finset.mem_univ (some (0 : Fin 1)))

lemma cpPoleAddOne {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (z : E) :
    max 0 (-(polynomialCurveOrder nu (z + 1) : Real)) =
      max 0 (-(polynomialCurveOrder nu z : Real)) := by
  by_cases hz : (0 : WithTop Int) ≤ nu.1 z
  · have hz' : (0 : WithTop Int) ≤ nu.1 (z + 1) :=
      nu.1.map_le_add hz (by simp)
    have hr : (0 : Real) ≤ (polynomialCurveOrder nu z : Real) := by
      exact_mod_cast (WithTop.untop₀_nonneg.mpr hz)
    have hr' : (0 : Real) ≤ (polynomialCurveOrder nu (z + 1) : Real) := by
      exact_mod_cast (WithTop.untop₀_nonneg.mpr hz')
    rw [max_eq_left (neg_nonpos.mpr hr'), max_eq_left (neg_nonpos.mpr hr)]
  · have hlt : nu.1 z < nu.1 1 := by simpa using lt_of_not_ge hz
    have heq := nu.1.map_add_eq_of_lt_left hlt
    simp only [polynomialCurveOrder, heq]

lemma cpAevalNonneg {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin 1 → E)
    (hx : (0 : WithTop Int) ≤ nu.1 (x 0))
    (p : MvPolynomial (Fin 1) Complex) :
    (0 : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C]
    by_cases hc : c = 0
    · simp [hc]
    · simp only [nu.2.1 c hc, le_refl]
  | add p q hp hq =>
    rw [map_add]
    exact nu.1.map_le_add hp hq
  | mul_X p i hp =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [map_mul, MvPolynomial.aeval_X, nu.1.map_mul]
    exact add_nonneg hp hx

/- At an affine place the generator attains the sInf and every multiplier
   has nonnegative valuation. Off that chart both sides vanish. -/
lemma cpShiftedContact {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin 1 → E) (hx : x 0 - 1 ≠ 0) :
    polynomialCurveIdealContact nu x cpShiftedIdeal =
      (polynomialCurveOrder nu (x 0 - 1)).toNat := by
  classical
  let r : Int := polynomialCurveOrder nu (x 0 - 1)
  have hfinite : nu.1 (x 0 - 1) ≠ ⊤ := (nu.1.ne_top_iff).mpr hx
  have hv : (r : WithTop Int) = nu.1 (x 0 - 1) :=
    WithTop.coe_untop₀_of_ne_top hfinite
  by_cases ha : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)
  · have hg : (0 : WithTop Int) ≤ nu.1 (x 0 - 1) :=
      nu.1.map_le_sub (ha 0) (by simp)
    have hr : 0 ≤ r := WithTop.untop₀_nonneg.mpr hg
    have hnat : (((r.toNat : Nat) : Int) : WithTop Int) = nu.1 (x 0 - 1) := by
      rw [Int.toNat_of_nonneg hr]
      exact hv
    let S : Set Nat := {k | ∃ f : MvPolynomial (Fin 1) Complex,
      f ∈ cpShiftedIdeal ∧
        nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)}
    have hmem : r.toNat ∈ S := by
      refine ⟨MvPolynomial.X 0 - 1, Ideal.mem_span_singleton_self _, ?_⟩
      simpa only [map_sub, MvPolynomial.aeval_X, map_one] using hnat.symm
    have hmin : ∀ k ∈ S, r.toNat ≤ k := by
      rintro k ⟨f, hf, hk⟩
      obtain ⟨p, rfl⟩ := Ideal.mem_span_singleton.mp hf
      have hp := cpAevalNonneg nu x (ha 0) p
      have hb : nu.1 (x 0 - 1) ≤
          nu.1 (MvPolynomial.aeval x ((MvPolynomial.X 0 - 1) * p)) := by
        have heval : MvPolynomial.aeval x ((MvPolynomial.X 0 - 1) * p) =
            (x 0 - 1) * MvPolynomial.aeval x p := by
          simp only [map_mul, map_sub, MvPolynomial.aeval_X, map_one]
        rw [heval, nu.1.map_mul]
        simpa only [add_zero] using
          add_le_add (le_refl (nu.1 (x 0 - 1))) hp
      rw [hk, ← hnat] at hb
      exact_mod_cast hb
    unfold polynomialCurveIdealContact
    rw [if_pos ha]
    change sInf S = r.toNat
    exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ hmin)
  · have hneg : nu.1 (x 0) < (0 : WithTop Int) := by
      apply lt_of_not_ge
      intro h
      apply ha
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using h
    have heq : nu.1 (x 0 - 1) = nu.1 (x 0) :=
      nu.1.map_sub_eq_of_lt_left (by simpa using hneg)
    have hr : r ≤ 0 := by
      have hb : (r : WithTop Int) ≤ ((0 : Int) : WithTop Int) := by
        rw [hv, heq]
        exact hneg.le
      exact_mod_cast hb
    unfold polynomialCurveIdealContact
    rw [if_neg ha]
    change 0 = r.toNat
    omega

lemma cpToNatReal (r : Int) : (r.toNat : Real) = max 0 (r : Real) := by
  by_cases hr : 0 ≤ r
  · have heq : (r.toNat : Real) = (r : Real) := by
      exact_mod_cast Int.toNat_of_nonneg hr
    rw [heq, max_eq_right (by exact_mod_cast hr)]
  · have hr' : r ≤ 0 := (lt_of_not_ge hr).le
    have hz : r.toNat = 0 := by omega
    rw [hz, Nat.cast_zero, max_eq_left (by exact_mod_cast hr')]

/- A generating transcendental parameter identifies the whole field
   with the rational-function field. -/
def cpAdjoinEquiv {E : Type} [Field E] [Algebra Complex E]
    (y : E) (hy : IntermediateField.adjoin Complex {y} = ⊤) :
    IntermediateField.adjoin Complex {y} ≃ₐ[Complex] E :=
  AlgEquiv.ofBijective (IntermediateField.adjoin Complex {y}).val
    ⟨Subtype.val_injective, by
      intro z
      exact ⟨⟨z, by rw [hy]; trivial⟩, rfl⟩⟩

def cpRatEquiv {E : Type} [Field E] [Algebra Complex E]
    (y : E) (ht : Transcendental Complex y)
    (hy : IntermediateField.adjoin Complex {y} = ⊤) :
    RatFunc Complex ≃ₐ[Complex] E :=
  (RatFunc.algEquivOfTranscendental y ht).trans (cpAdjoinEquiv y hy)

lemma cpRatEquivX {E : Type} [Field E] [Algebra Complex E]
    (y : E) (ht : Transcendental Complex y)
    (hy : IntermediateField.adjoin Complex {y} = ⊤) :
    cpRatEquiv y ht hy RatFunc.X = y := by
  change ((RatFunc.algEquivOfTranscendental y ht) RatFunc.X : E) = y
  exact RatFunc.algEquivOfTranscendental_X y ht

lemma cpShiftedCurveBound :
    WeightedIdealCurveBound cpShiftedIdeal (fun _ => 1) 1 := by
  intro E _ _ _ htr x hx
  have hxgen : IntermediateField.adjoin Complex {x 0} = ⊤ := by
    have hrange : Set.range x = {x 0} :=
      Set.range_eq_singleton (fun i => congrArg x (Subsingleton.elim i 0))
    rwa [hrange] at hx
  have hxt : Transcendental Complex (x 0) := by
    intro halg
    letI : Algebra.IsAlgebraic Complex (IntermediateField.adjoin Complex {x 0}) :=
      IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
    letI : Algebra.IsAlgebraic Complex E := (cpAdjoinEquiv (x 0) hxgen).isAlgebraic
    have hz : Algebra.trdeg Complex E = 0 := trdeg_eq_zero
    rw [htr] at hz
    exact one_ne_zero hz
  let y : E := x 0 - 1
  have hyt : Transcendental Complex y := by
    intro halg
    apply hxt
    have h := halg.add (isAlgebraic_one (R := Complex) (A := E))
    simpa only [y, sub_add_cancel] using h
  have hyne : y ≠ 0 := by
    intro h
    apply hyt
    rw [h]
    exact isAlgebraic_zero
  have hygen : IntermediateField.adjoin Complex {y} = ⊤ := by
    apply top_unique
    rw [← hxgen]
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    change x 0 ∈ IntermediateField.adjoin Complex {y}
    have hm : y ∈ IntermediateField.adjoin Complex {y} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton y)
    have h : y + 1 ∈ IntermediateField.adjoin Complex {y} :=
      (IntermediateField.adjoin Complex {y}).add_mem hm
      (IntermediateField.adjoin Complex {y}).one_mem
    have hxy : y + 1 = x 0 := sub_add_cancel _ _
    rw [hxy] at h
    exact h
  have hyit : Transcendental Complex y⁻¹ := by
    intro halg
    apply hyt
    simpa only [inv_inv] using halg.inv
  have hyigen : IntermediateField.adjoin Complex {y⁻¹} = ⊤ := by
    apply top_unique
    rw [← hygen]
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    change y ∈ IntermediateField.adjoin Complex {y⁻¹}
    have hm : y⁻¹ ∈ IntermediateField.adjoin Complex {y⁻¹} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    have h : (y⁻¹)⁻¹ ∈ IntermediateField.adjoin Complex {y⁻¹} :=
      (IntermediateField.adjoin Complex {y⁻¹}).inv_mem hm
    rw [inv_inv] at h
    exact h
  let a : E ≃ₐ[Complex] E :=
    (cpRatEquiv y hyt hygen).symm.trans (cpRatEquiv y⁻¹ hyit hyigen)
  have hay : a y = y⁻¹ := by
    calc
      a y = a (cpRatEquiv y hyt hygen RatFunc.X) :=
        congrArg a (cpRatEquivX y hyt hygen).symm
      _ = cpRatEquiv y⁻¹ hyit hyigen RatFunc.X := by
        change cpRatEquiv y⁻¹ hyit hyigen
          ((cpRatEquiv y hyt hygen).symm (cpRatEquiv y hyt hygen RatFunc.X)) = _
        rw [AlgEquiv.symm_apply_apply]
      _ = y⁻¹ := cpRatEquivX y⁻¹ hyit hyigen
  have hax : a (x 0) = y⁻¹ + 1 := by
    calc
      a (x 0) = a (y + 1) := by dsimp only [y]; rw [sub_add_cancel]
      _ = y⁻¹ + 1 := by rw [map_add, map_one, hay]
  have hpoint (nu : PolynomialCurvePlace E) :
      (polynomialCurveIdealContact nu x cpShiftedIdeal : Real) =
        polynomialCurvePole (cpPlaceEquiv a nu) x (fun _ => 1) := by
    rw [cpShiftedContact nu x hyne, cpToNatReal, cpPoleOne]
    change max 0 (polynomialCurveOrder nu y : Real) =
      max 0 (-(polynomialCurveOrder nu (a (x 0)) : Real))
    rw [hax, cpPoleAddOne]
    simp only [polynomialCurveOrder, AddValuation.map_inv,
      WithTop.untop₀_neg, Int.cast_neg, neg_neg]
  simp only [Rat.cast_one, one_mul]
  exact le_of_eq (finsum_eq_of_bijective (cpPlaceEquiv a)
    (cpPlaceEquiv a).bijective hpoint)

theorem solution : ¬ (∀ {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps),
    ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ I ^ s ∧
        (n : Real) * (w i : Real) ≤ (B : Real)) := by
  intro h
  obtain ⟨ s, hs, B, hB, hcoords ⟩ :=
    h cpShiftedIdeal cpShiftedFinite (fun _ => 1) (by intro i; norm_num)
      1 (by norm_num) cpShiftedCurveBound 1 (by norm_num)
  obtain ⟨ n, hn, hmem, hbound ⟩ := hcoords 0
  exact cpShiftedNoPower s n hs hmem