-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomial_curve_aeval_pole_le_weighted_height
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:50:02.199593+00:00
-- url     : https://prove2.me/submissions/a63857ca-8642-4d6d-a9d4-4f9896ccfeef

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

/-!
Faithful translation of OpenAI `PolynomialPoleBound` / `WeightedPolynomialPole`:
real-valued pushforward of the place valuation, monomial/polynomial lower bounds via
`AddValuation.map_le_sum`, then convert to the `max(-ord, 0)` statement.
-/

namespace PoleBound

variable {K : Type*} [Field K]

/-- Push an integer-valued additive valuation to a real-valued one. -/
noncomputable def realValuation (v : AddValuation K (WithTop Int)) :
    AddValuation K (WithTop Real) :=
  v.map (Int.castAddHom Real).withTopMap (by simp)
    (Monotone.withTop_map Int.cast_mono)

theorem realValuation_eq (v : AddValuation K (WithTop Int)) (x : K) :
    realValuation v x = WithTop.map (Int.cast : Int → Real) (v x) :=
  rfl

theorem valuation_prod {σ : Type*} (v : AddValuation K (WithTop Real))
    (s : Finset σ) (f : σ → K) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

theorem monomial_order_lower {σ C : Type*} [CommRing C] [Algebra C K]
    (v : AddValuation K (WithTop Real))
    (x : σ → K) (w : σ → Real) (D : Real)
    (hx : ∀ i, ((-w i * D : Real) : WithTop Real) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop Real) ≤ v (algebraMap C K c))
    (d : σ →₀ Nat) (c : C) :
    ((-Finsupp.weight w d * D : Real) : WithTop Real) ≤
      v (MvPolynomial.aeval x (MvPolynomial.monomial d c)) := by
  classical
  rw [MvPolynomial.aeval_monomial, v.map_mul, Finsupp.prod, valuation_prod]
  have heq : ((-Finsupp.weight w d * D : Real) : WithTop Real) =
      ∑ i ∈ d.support, d i • ((-w i * D : Real) : WithTop Real) := by
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_sum]
    apply congrArg (fun r : Real => (r : WithTop Real))
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finset.sum_mul, neg_mul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [heq]
  calc
    (∑ i ∈ d.support, d i • ((-w i * D : Real) : WithTop Real)) ≤
        ∑ i ∈ d.support, v (x i ^ d i) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [v.map_pow]
      exact nsmul_le_nsmul_right (hx i) (d i)
    _ ≤ v (algebraMap C K c) + ∑ i ∈ d.support, v (x i ^ d i) :=
      le_add_of_nonneg_left (hc c)

theorem polynomial_order_lower {σ C : Type*} [CommRing C] [Algebra C K]
    (v : AddValuation K (WithTop Real))
    (x : σ → K) (w : σ → Real) (D N : Real) (hD : 0 ≤ D)
    (hx : ∀ i, ((-w i * D : Real) : WithTop Real) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop Real) ≤ v (algebraMap C K c))
    (p : MvPolynomial σ C)
    (hp : ∀ d ∈ p.support, Finsupp.weight w d ≤ N) :
    ((-N * D : Real) : WithTop Real) ≤ v (MvPolynomial.aeval x p) := by
  classical
  rw [p.as_sum, map_sum]
  apply v.map_le_sum
  intro d hd
  have hnum : -N * D ≤ -Finsupp.weight w d * D :=
    mul_le_mul_of_nonneg_right (neg_le_neg (hp d hd)) hD
  exact (WithTop.coe_le_coe.mpr hnum).trans
    (monomial_order_lower v x w D hx hc d (MvPolynomial.coeff d p))

/-- Real valuation equals the coerced integer order when the element is nonzero. -/
theorem realValuation_of_ne_zero (v : AddValuation K (WithTop Int)) (x : K) (hx : x ≠ 0) :
    realValuation v x = ((v x).untop₀ : Real) := by
  have hneTop : v x ≠ ⊤ := (AddValuation.ne_top_iff v).2 hx
  rw [realValuation_eq, ← WithTop.coe_untop₀_of_ne_top hneTop, WithTop.map_coe]
  rfl

end PoleBound

theorem solution
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (hN : 0 ≤ N)
    (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F) :
    max (-(polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real)) 0 ≤
      N * polynomialCurvePole nu x w := by
  classical
  let rv := PoleBound.realValuation nu.val
  let wr : Fin d → Real := fun i => (w i : Real)
  let D : Real := polynomialCurvePole nu x w
  let entry : Option (Fin d) → Real :=
    fun i => i.elim 0 (fun j => -(polynomialCurveOrder nu (x j) : Real) / (w j : Real))
  have hpole : D = Finset.univ.sup' (by simp) entry := by
    dsimp only [D, polynomialCurvePole, entry]
  have hD : 0 ≤ D := by
    rw [hpole]
    exact Finset.le_sup' entry (by simp : (none : Option (Fin d)) ∈ Finset.univ)
  have hrv0 : rv 0 = (⊤ : WithTop Real) := by
    change WithTop.map (Int.cast : Int → Real) (nu.val 0) = ⊤
    rw [AddValuation.map_zero]
    rfl
  -- Coordinate lower bounds
  have hx : ∀ j, ((-wr j * D : Real) : WithTop Real) ≤ rv (x j) := by
    intro j
    by_cases hx0 : x j = 0
    · rw [hx0, hrv0]
      exact le_top
    · have hle : entry (some j) ≤ D := by
        rw [hpole]
        exact Finset.le_sup' entry (by simp)
      have hdiv : -(polynomialCurveOrder nu (x j) : Real) / wr j ≤ D := by
        simpa [entry, wr] using hle
      have hord : -wr j * D ≤ (polynomialCurveOrder nu (x j) : Real) := by
        have := (div_le_iff₀ (hw j)).1 hdiv
        linarith
      have : rv (x j) =
          ((polynomialCurveOrder nu (x j) : Real) : WithTop Real) := by
        simpa [polynomialCurveOrder] using
          PoleBound.realValuation_of_ne_zero nu.val (x j) hx0
      rw [this]
      exact WithTop.coe_le_coe.mpr hord
  -- Constants nonnegative under the place (trivial on ℂ)
  have hc : ∀ c : Complex, (0 : WithTop Real) ≤ rv (algebraMap Complex E c) := by
    intro c
    by_cases hc0 : c = 0
    · rw [hc0, show (algebraMap Complex E) 0 = (0 : E) from map_zero _, hrv0]
      exact le_top
    · have hnv : nu.val (algebraMap Complex E c) = (0 : WithTop Int) :=
        nu.property.1 c hc0
      change (0 : WithTop Real) ≤
        WithTop.map (Int.cast : Int → Real) (nu.val (algebraMap Complex E c))
      rw [hnv, show (0 : WithTop Int) = ↑(0 : Int) from rfl, WithTop.map_coe,
        Int.cast_zero]
      exact le_rfl
  -- Weighted degree → Finsupp.weight
  have hp : ∀ a ∈ F.support, Finsupp.weight wr a ≤ N := by
    intro a ha
    have hlog := hF a ha
    have hwt : Finsupp.weight wr a = ∑ i : Fin d, wr i * (a i : Real) := by
      rw [Finsupp.weight_eq_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [nsmul_eq_mul, wr, mul_comm]
    rwa [← hwt] at hlog
  -- Core valuation lower bound (OpenAI polynomial_order_lower)
  have hbound : ((-N * D : Real) : WithTop Real) ≤ rv (MvPolynomial.aeval x F) :=
    PoleBound.polynomial_order_lower rv x wr D N hD hx hc F hp
  have hND : 0 ≤ N * D := mul_nonneg hN hD
  by_cases hF0 : MvPolynomial.aeval x F = 0
  · have hord0 : polynomialCurveOrder nu (MvPolynomial.aeval x F) = 0 := by
      rw [hF0]
      change (nu.val 0).untop₀ = 0
      rw [AddValuation.map_zero]
      exact WithTop.untop₀_top
    simp only [hord0, Int.cast_zero, neg_zero, max_self]
    exact hND
  · have hrv : rv (MvPolynomial.aeval x F) =
        ((polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real) : WithTop Real) := by
      simpa [polynomialCurveOrder] using
        PoleBound.realValuation_of_ne_zero nu.val _ hF0
    have hord_le :
        -N * D ≤ (polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real) := by
      rw [hrv] at hbound
      exact WithTop.coe_le_coe.mp hbound
    have hneg :
        -(polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real) ≤ N * D := by
      linarith
    exact max_le hneg hND
