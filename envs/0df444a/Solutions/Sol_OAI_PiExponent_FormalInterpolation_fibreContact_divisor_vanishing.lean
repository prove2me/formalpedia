-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_divisor_vanishing
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-23T23:13:06.995547+00:00
-- url     : https://prove2.me/submissions/063b2319-8050-4232-b956-5f3341242588

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

noncomputable section

namespace FibreContactCounterexample

abbrev E := RatFunc Complex

def t : E := (RatFunc.X : E)⁻¹

def x (i : Fin 2) : E := if i = 0 then 1 else t

def I : Ideal (MvPolynomial (Fin 2) Complex) :=
  Ideal.span {MvPolynomial.X (1 : Fin 2)}

@[simp] lemma x_zero : x 0 = 1 := by simp [x]
@[simp] lemma x_one : x 1 = t := by simp [x]
@[simp] lemma t_ne_zero : t ≠ 0 := inv_ne_zero RatFunc.X_ne_zero

lemma trdeg_E : Algebra.trdeg Complex E = 1 := by
  letI : Algebra.IsAlgebraic (Polynomial Complex) E :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := Polynomial Complex) (K := E) (C := E)).mpr inferInstance
  have h := trdeg_add_eq Complex (Polynomial Complex) (A := E)
  simpa only [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] using h.symm

lemma essFiniteType_E : Algebra.EssFiniteType Complex E := by
  apply IntermediateField.fg_top_iff.mp
  rw [← (RatFunc.adjoin_X (K := Complex))]
  exact IntermediateField.fg_adjoin_of_finite (Set.finite_singleton _)

lemma generates : IntermediateField.adjoin Complex (Set.range x) = ⊤ := by
  apply top_unique
  rw [← (RatFunc.adjoin_X (K := Complex))]
  apply IntermediateField.adjoin_le_iff.mpr
  intro f hf
  have hfX : f = (RatFunc.X : E) := Set.mem_singleton_iff.mp hf
  subst f
  have ht : t ∈ IntermediateField.adjoin Complex (Set.range x) :=
    IntermediateField.subset_adjoin Complex _ ⟨1, x_one⟩
  change (RatFunc.X : E) ∈ IntermediateField.adjoin Complex (Set.range x)
  simpa only [t, inv_inv] using
    (IntermediateField.adjoin Complex (Set.range x)).inv_mem ht

/- Construct the additive degree valuation directly with the required codomain. -/
def infinityOrder (f : E) : WithTop Int := by
  classical
  exact if f = 0 then ⊤ else (-f.intDegree : Int)

def infinityValuation : AddValuation E (WithTop Int) :=
  AddValuation.of infinityOrder (by simp [infinityOrder])
    (by simp [infinityOrder])
    (by
      intro f g
      by_cases hf : f = 0
      · subst f
        rw [zero_add]
        exact min_le_right _ _
      by_cases hg : g = 0
      · subst g
        rw [add_zero]
        exact min_le_left _ _
      by_cases hfg : f + g = 0
      · simp [infinityOrder, hf, hg, hfg]
      simp only [infinityOrder, if_neg hf, if_neg hg, if_neg hfg]
      have h := RatFunc.intDegree_add_le hg hfg
      have h' : min (-f.intDegree) (-g.intDegree) ≤ -(f + g).intDegree := by
        rcases le_total f.intDegree g.intDegree with hle | hle
        · have hle' : (f + g).intDegree ≤ g.intDegree := by
            simpa only [max_eq_right hle] using h
          exact (min_le_right _ _).trans (neg_le_neg hle')
        · have hle' : (f + g).intDegree ≤ f.intDegree := by
            simpa only [max_eq_left hle] using h
          exact (min_le_left _ _).trans (neg_le_neg hle')
      exact_mod_cast h')
    (by
      intro f g
      by_cases hf : f = 0
      · simp [hf, infinityOrder]
      by_cases hg : g = 0
      · simp [hg, infinityOrder]
      simp [infinityOrder, hf, hg, mul_ne_zero hf hg, RatFunc.intDegree_mul hf hg,
        neg_add, WithTop.coe_add, add_comm])

lemma degree_X_pow (n : Nat) : ((RatFunc.X : E) ^ n).intDegree = (n : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ RatFunc.X_ne_zero)
      RatFunc.X_ne_zero, ih, RatFunc.intDegree_X]
    simp

def infinityPlace : PolynomialCurvePlace E :=
  ⟨infinityValuation, (by
    constructor
    · intro b hb
      change infinityOrder (algebraMap Complex E b) = 0
      have hb' : (algebraMap Complex E b) ≠ 0 := by
        intro h
        apply hb
        apply FaithfulSMul.algebraMap_injective Complex E
        simpa using h
      simp [infinityOrder, hb', hb, RatFunc.algebraMap_eq_C]
    · intro k
      cases k with
      | ofNat n =>
        refine ⟨((RatFunc.X : E) ^ n)⁻¹, ?_⟩
        change infinityOrder _ = _
        simp [infinityOrder,
          inv_ne_zero (pow_ne_zero n (RatFunc.X_ne_zero (K := Complex))),
          RatFunc.X_ne_zero (K := Complex), degree_X_pow]
      | negSucc n =>
        refine ⟨(RatFunc.X : E) ^ (n + 1), ?_⟩
        change infinityOrder _ = _
        simp [infinityOrder,
          pow_ne_zero (n + 1) (RatFunc.X_ne_zero (K := Complex)),
          RatFunc.X_ne_zero (K := Complex), degree_X_pow, Int.negSucc_eq])⟩

@[simp] lemma infinity_t : infinityPlace.1 t = (1 : WithTop Int) := by
  change infinityOrder t = _
  simp [infinityOrder, t, RatFunc.X_ne_zero (K := Complex)]

@[simp] lemma infinity_order_t : polynomialCurveOrder infinityPlace t = 1 := by
  simp [polynomialCurveOrder]

lemma coe_zsmul_int (k a : Int) :
    k • (a : WithTop Int) = ((k * a : Int) : WithTop Int) := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, natCast_zsmul, ← WithTop.coe_nsmul, nsmul_eq_mul]
  | negSucc n =>
    rw [negSucc_zsmul, ← WithTop.coe_nsmul]
    change ((-((n + 1) • a) : Int) : WithTop Int) = _
    congr 1
    simp only [nsmul_eq_mul, Int.negSucc_eq, Nat.cast_add, Nat.cast_one]
    ring

/- The degree formula gives v(f) = degree(f) * v(X). Surjectivity gives a
   product equal to one, forcing the negative integer v(X) to be -1. -/
lemma eq_infinity_of_order_X_neg (nu : PolynomialCurvePlace E)
    (hneg : polynomialCurveOrder nu (RatFunc.X : E) < 0) : nu = infinityPlace := by
  classical
  let a : Int := polynomialCurveOrder nu (RatFunc.X : E)
  change a < 0 at hneg
  have hX : nu.1 (RatFunc.X : E) = (a : WithTop Int) :=
    (WithTop.coe_untop₀_of_ne_top
      ((AddValuation.ne_top_iff nu.1).mpr RatFunc.X_ne_zero)).symm
  let v := AddValuation.toValuation nu.1
  letI : v.IsTrivialOn Complex := ⟨fun b hb => by
    change nu.1 (algebraMap Complex E b) = 0
    exact nu.2.1 b hb⟩
  have hvX : 1 < v (RatFunc.X : E) := by
    change nu.1 (RatFunc.X : E) < (0 : WithTop Int)
    rw [hX]
    exact_mod_cast hneg
  have hformula (f : E) (hf : f ≠ 0) :
      nu.1 f = ((f.intDegree * a : Int) : WithTop Int) := by
    have h := RatFunc.valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X
      (v := v) hvX hf
    change nu.1 f = f.intDegree • nu.1 (RatFunc.X : E) at h
    rw [hX, coe_zsmul_int] at h
    exact h
  obtain ⟨f, hf⟩ := nu.2.2 1
  have hf0 : f ≠ 0 := by
    intro h
    subst f
    simpa using hf
  have hprod : (1 : Int) = f.intDegree * a := by
    exact_mod_cast (hf.symm.trans (hformula f hf0))
  have haunit : IsUnit a := isUnit_iff_dvd_one.mpr
    ⟨f.intDegree, by simpa only [mul_comm] using hprod⟩
  have ha : a = -1 := by
    have habs := Int.isUnit_iff_abs_eq.mp haunit
    rw [abs_of_neg hneg] at habs
    omega
  apply Subtype.ext
  apply AddValuation.ext
  intro g
  by_cases hg : g = 0
  · subst g
    simp
  · rw [hformula g hg, ha, mul_neg_one]
    change ((-g.intDegree : Int) : WithTop Int) = infinityOrder g
    simp [infinityOrder, hg]

lemma aeval_nonneg (nu : PolynomialCurvePlace E)
    (hx : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (p : MvPolynomial (Fin 2) Complex) :
    (0 : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x p) := by
  induction p using MvPolynomial.induction_on with
  | C b =>
    by_cases hb : b = 0
    · simp [hb]
    · simpa only [MvPolynomial.aeval_C, nu.2.1 b hb] using
        (le_refl (0 : WithTop Int))
  | add p q hp hq =>
    simpa only [map_add] using nu.1.map_le_add hp hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, AddValuation.map_mul]
    exact add_nonneg hp (hx i)

lemma infinity_chart : ∀ i, (0 : WithTop Int) ≤ infinityPlace.1 (x i) := by
  intro i
  fin_cases i <;> simp

lemma generator_mem : MvPolynomial.X (1 : Fin 2) ∈ I := by
  exact Ideal.subset_span (Set.mem_singleton _)

lemma infinity_contact : polynomialCurveIdealContact infinityPlace x I = 1 := by
  classical
  let S : Set Nat := {k | ∃ f : MvPolynomial (Fin 2) Complex,
    f ∈ I ∧ infinityPlace.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)}
  have h1 : 1 ∈ S :=
    ⟨MvPolynomial.X (1 : Fin 2), generator_mem, by simp⟩
  have hlower : ∀ k ∈ S, 1 ≤ k := by
    rintro k ⟨f, hf, hval⟩
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    have hg := aeval_nonneg infinityPlace infinity_chart g
    have hge : (1 : WithTop Int) ≤
        infinityPlace.1 (MvPolynomial.aeval x (g * MvPolynomial.X (1 : Fin 2))) := by
      simpa only [map_mul, MvPolynomial.aeval_X, AddValuation.map_mul, x_one,
        infinity_t, zero_add, add_zero, add_comm] using
          add_le_add_right hg (1 : WithTop Int)
    rw [hval] at hge
    exact_mod_cast hge
  change (if (∀ i, (0 : WithTop Int) ≤ infinityPlace.1 (x i)) then sInf S else 0) = 1
  rw [if_pos infinity_chart]
  exact le_antisymm (Nat.sInf_le h1) (le_csInf ⟨1, h1⟩ hlower)

lemma contact_zero_of_ne (nu : PolynomialCurvePlace E) (hne : nu ≠ infinityPlace) :
    polynomialCurveIdealContact nu x I = 0 := by
  classical
  by_cases hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)
  · let a : Int := polynomialCurveOrder nu t
    have ha0 : 0 ≤ a := by
      apply WithTop.untop₀_nonneg.mpr
      simpa only [x_one] using hchart 1
    have hatop : nu.1 t ≠ ⊤ := (AddValuation.ne_top_iff nu.1).mpr t_ne_zero
    have hcoe : nu.1 t = (a : WithTop Int) :=
      (WithTop.coe_untop₀_of_ne_top hatop).symm
    have hanotpos : ¬ 0 < a := by
      intro hpos
      apply hne
      apply eq_infinity_of_order_X_neg
      have hinv : polynomialCurveOrder nu t =
          -polynomialCurveOrder nu (RatFunc.X : E) := by
        simp [polynomialCurveOrder, t, AddValuation.map_inv]
      change a = _ at hinv
      omega
    have ha : a = 0 := by omega
    have hzero : nu.1 t = (0 : WithTop Int) := by simpa [ha] using hcoe
    have hbound : polynomialCurveIdealContact nu x I ≤ 0 := by
      rw [polynomialCurveIdealContact, if_pos hchart]
      apply Nat.sInf_le
      exact ⟨MvPolynomial.X (1 : Fin 2), generator_mem, by simpa using hzero⟩
    exact Nat.eq_zero_of_le_zero hbound
  · simp only [polynomialCurveIdealContact, if_neg hchart]

lemma total_contact :
    (∑ᶠ nu : PolynomialCurvePlace E, (polynomialCurveIdealContact nu x I : Real)) = 1 := by
  rw [finsum_eq_single _ infinityPlace]
  · simp [infinity_contact]
  · intro nu hne
    simp [contact_zero_of_ne nu hne]

lemma pole_zero (nu : PolynomialCurvePlace E) :
    polynomialCurvePole nu x (fun _ => (0 : Rat)) = 0 := by
  classical
  unfold polynomialCurvePole
  apply Finset.sup'_eq_of_forall
  intro i hi
  cases i <;> simp

lemma total_pole :
    (∑ᶠ nu : PolynomialCurvePlace E,
      polynomialCurvePole nu x (fun _ => (0 : Rat))) = 0 := by
  simp [pole_zero]

end FibreContactCounterexample

/- All binders of the challenged proposition, including its unused K and
   every field/algebra instance, are inside the negation. -/
theorem solution :
    ¬ (∀ {m K : Nat} (E : Type) [Field E] [Algebra Complex E]
      [Algebra.EssFiniteType Complex E]
      (htrdeg : Algebra.trdeg Complex E = 1)
      (x : Fin (m + 1) → E)
      (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
      (hfibre : x 0 = 1)
      (w : Fin (m + 1) → Rat) (R sigma : Rat)
      (hR : 0 < R) (hsigma : 0 < (sigma : Real))
      (N : Nat) (hN : 0 < N)
      (P : MvPolynomial (Fin m) Complex)
      (hP : fibreContactSupportBound (fun i => w i.succ) N P)
      (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
      (hexcess :
        (R : Real) / (1 + (sigma : Real)) *
          (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) <
        (∑ᶠ nu : PolynomialCurvePlace E,
          (polynomialCurveIdealContact nu x I : Real)))
      (hlocal : MvPolynomial.aeval (fun i => x i.succ) P ≠ 0 →
        ∀ nu : PolynomialCurvePlace E,
          ((polynomialCurveIdealContact nu x I : Real) *
            ((1 + 2 * (sigma : Real)) * (N : Real))) ≤
            (R : Real) * max 0
              (polynomialCurveOrder nu
                (MvPolynomial.aeval (fun i => x i.succ) P) : Real)),
      MvPolynomial.aeval (fun i => x i.succ) P = 0) := by
  classical
  intro h
  letI := FibreContactCounterexample.essFiniteType_E
  have heval :
      MvPolynomial.aeval (fun i : Fin 1 => FibreContactCounterexample.x i.succ)
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) Complex) =
        FibreContactCounterexample.t := by
    simp
  have hsupport : fibreContactSupportBound (fun _ : Fin 1 => (0 : Rat)) 1
      (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) Complex) := by
    intro a ha
    norm_num
  have hexcess :
      ((3 : Rat) : Real) / (1 + ((1 : Rat) : Real)) *
        (∑ᶠ nu : PolynomialCurvePlace FibreContactCounterexample.E,
          polynomialCurvePole nu FibreContactCounterexample.x (fun _ => (0 : Rat))) <
      (∑ᶠ nu : PolynomialCurvePlace FibreContactCounterexample.E,
        (polynomialCurveIdealContact nu FibreContactCounterexample.x
          FibreContactCounterexample.I : Real)) := by
    rw [FibreContactCounterexample.total_pole, FibreContactCounterexample.total_contact]
    norm_num
  have hlocal :
      MvPolynomial.aeval (fun i : Fin 1 => FibreContactCounterexample.x i.succ)
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) Complex) ≠ 0 →
      ∀ nu : PolynomialCurvePlace FibreContactCounterexample.E,
        (polynomialCurveIdealContact nu FibreContactCounterexample.x
          FibreContactCounterexample.I : Real) *
          ((1 + 2 * ((1 : Rat) : Real)) * ((1 : Nat) : Real)) ≤
        ((3 : Rat) : Real) * max 0 (polynomialCurveOrder nu
          (MvPolynomial.aeval (fun i : Fin 1 => FibreContactCounterexample.x i.succ)
            (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) Complex)) : Real) := by
    intro _ nu
    rw [heval]
    by_cases hnu : nu = FibreContactCounterexample.infinityPlace
    · subst nu
      rw [FibreContactCounterexample.infinity_contact,
        FibreContactCounterexample.infinity_order_t]
      norm_num
    · rw [FibreContactCounterexample.contact_zero_of_ne nu hnu]
      simp only [Nat.cast_zero, zero_mul]
      exact mul_nonneg (by norm_num) (le_max_left _ _)
  have hbad := h (m := 1) (K := 0) FibreContactCounterexample.E
    FibreContactCounterexample.trdeg_E FibreContactCounterexample.x
    FibreContactCounterexample.generates FibreContactCounterexample.x_zero
    (fun _ => (0 : Rat)) 3 1 (by norm_num) (by norm_num)
    1 (by norm_num) (MvPolynomial.X (0 : Fin 1)) hsupport
    FibreContactCounterexample.I hexcess hlocal
  rw [heval] at hbad
  exact FibreContactCounterexample.t_ne_zero hbad
