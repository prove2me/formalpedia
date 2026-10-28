-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_support_finite_of_hasPrincipalDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:12:22.848813+00:00
-- url     : https://prove2.me/submissions/6ce310b7-31d5-4cc0-9f32-f4d4982389cb

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

open Valuation WithZero MonoidWithZeroHom
open OAI.PiExponent.FormalInterpolation
open AlgebraicCurve
open IsDiscreteValuationRing

/-!
Under `HasPrincipalDivisors`, transport each `PolynomialCurvePlace` to an
`AlgebraicCurve.Place` via the multiplicative form of its additive valuation.
The multiplicative form coincides with `Place.adicValuation`, so orders agree
and the nonzero-order locus injects into the finite Place support of the
principal divisor.
-/

noncomputable section

/-- Convert additive `WithTop ℤ` values to multiplicative `ℤᵐ⁰`. -/
def toZm0 : WithTop ℤ → ℤᵐ⁰
  | ⊤ => 0
  | (n : ℤ) => exp (-n)

@[simp] theorem toZm0_top : toZm0 (⊤ : WithTop ℤ) = 0 := rfl
@[simp] theorem toZm0_coe (n : ℤ) : toZm0 (n : WithTop ℤ) = exp (-n) := rfl

theorem toZm0_zero : toZm0 (0 : WithTop ℤ) = 1 := by
  change toZm0 (↑(0 : ℤ)) = 1
  rw [toZm0_coe, neg_zero, exp_zero]

theorem toZm0_eq_one_iff : ∀ a : WithTop ℤ, toZm0 a = 1 ↔ a = 0
  | ⊤ => by simp
  | (n : ℤ) => by
      simp only [toZm0_coe, WithTop.coe_eq_zero]
      exact (exp_eq_one).trans (neg_eq_zero.trans Iff.rfl)

theorem toZm0_add : ∀ a b : WithTop ℤ, toZm0 (a + b) = toZm0 a * toZm0 b
  | ⊤, _ => by simp
  | (a : ℤ), ⊤ => by simp
  | (a : ℤ), (b : ℤ) => by
      change toZm0 ↑(a + b) = toZm0 ↑a * toZm0 ↑b
      simp only [toZm0_coe, neg_add, exp_add]

theorem toZm0_antitone : Antitone toZm0 := by
  intro a b hab
  induction a using WithTop.recTopCoe generalizing b with
  | top =>
    have : b = ⊤ := le_antisymm le_top hab
    simp [this]
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp [zero_le]
    | coe b =>
      simp only [WithTop.coe_le_coe] at hab
      simpa using (exp_le_exp).2 (neg_le_neg hab)

theorem toZm0_min (a b : WithTop ℤ) :
    toZm0 (min a b) = max (toZm0 a) (toZm0 b) :=
  toZm0_antitone.map_min

/-- Inverse of `toZm0` on the nose. -/
def fromZm0 : ℤᵐ⁰ → WithTop ℤ :=
  fun γ => if γ = 0 then ⊤ else ↑(-log γ)

theorem fromZm0_toZm0 : ∀ a : WithTop ℤ, fromZm0 (toZm0 a) = a
  | ⊤ => by simp [fromZm0]
  | (n : ℤ) => by
      simp [fromZm0, exp_ne_zero, log_exp]

/-- Multiplicative form of an integer-valued additive valuation. -/
def mulOfAdd {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) : Valuation E ℤᵐ⁰ where
  toFun := fun x => toZm0 (v x)
  map_zero' := by simp [AddValuation.map_zero]
  map_one' := by simp [AddValuation.map_one, toZm0_zero]
  map_mul' := fun x y => by simp [AddValuation.map_mul, toZm0_add]
  map_add_le_max' := fun x y => by
    have h := v.map_add x y
    have := toZm0_antitone h
    simpa [toZm0_min] using this

theorem mulOfAdd_apply {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) (x : E) :
    mulOfAdd v x = toZm0 (v x) := rfl

theorem mulOfAdd_surjective {E : Type} [Field E]
    (v : AddValuation E (WithTop ℤ))
    (hsurj : ∀ k : ℤ, ∃ x : E, v x = (k : WithTop ℤ)) :
    Function.Surjective (mulOfAdd v) := by
  intro γ
  induction γ using WithZero.recZeroCoe with
  | zero =>
    exact ⟨0, by simp [mulOfAdd_apply, AddValuation.map_zero]⟩
  | coe g =>
    obtain ⟨x, hx⟩ := hsurj (-Multiplicative.toAdd g)
    refine ⟨x, ?_⟩
    rw [mulOfAdd_apply, hx, toZm0_coe, neg_neg]
    simp [exp]

theorem valueGroup_eq_top_of_surjective {E : Type} [Field E]
    (v : Valuation E ℤᵐ⁰) (hsurj : Function.Surjective v) :
    valueGroup (.ofClass v) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun g => ?_
  obtain ⟨x, hx⟩ := hsurj (g : ℤᵐ⁰)
  exact mem_valueGroup _ ⟨x, hx⟩

theorem mulOfAdd_isPrincipalIdealRing {E : Type} [Field E]
    (v : AddValuation E (WithTop ℤ))
    (hsurj : ∀ k : ℤ, ∃ x : E, v x = (k : WithTop ℤ)) :
    IsPrincipalIdealRing (mulOfAdd v).valuationSubring := by
  have hsurj' : Function.Surjective (mulOfAdd v) := mulOfAdd_surjective v hsurj
  have htop : valueGroup (.ofClass (mulOfAdd v)) = ⊤ :=
    valueGroup_eq_top_of_surjective _ hsurj'
  haveI : IsCyclic (valueGroup (.ofClass (mulOfAdd v))) := by
    rw [htop]; infer_instance
  haveI : Nontrivial (valueGroup (.ofClass (mulOfAdd v))) := by
    rw [htop]; infer_instance
  exact Valuation.valuationSubring_isPrincipalIdealRing (mulOfAdd v)

/-- In `ℤᵐ⁰`, every element strictly less than `1` is `≤ exp (-1)`. -/
theorem lt_one_le_exp_neg_one {γ : ℤᵐ⁰} (h : γ < 1) : γ ≤ exp (-1) := by
  induction γ using WithZero.recZeroCoe with
  | zero => exact bot_le
  | coe g =>
    have h' : exp (Multiplicative.toAdd g) < exp (0 : ℤ) := by
      simpa [exp, exp_zero] using h
    have hg : Multiplicative.toAdd g < 0 := (exp_lt_exp).1 h'
    have hle : Multiplicative.toAdd g ≤ (-1 : ℤ) := by omega
    have : exp (Multiplicative.toAdd g) ≤ exp (-1 : ℤ) := (exp_le_exp).2 hle
    simpa [exp] using this

theorem exp_neg_one_lt_one : (exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
  have : exp (-1 : ℤ) < exp (0 : ℤ) := (exp_lt_exp).2 (by decide)
  simpa [exp_zero] using this

/-- Two surjective `ℤᵐ⁰`-valued valuations that are equivalent are identical. -/
theorem eq_of_isEquiv_of_surjective {K : Type} [Field K]
    (v w : Valuation K ℤᵐ⁰)
    (hv : Function.Surjective v) (hw : Function.Surjective w)
    (h : v.IsEquiv w) : v = w := by
  have htopv : valueGroup (.ofClass v) = ⊤ := valueGroup_eq_top_of_surjective v hv
  have htopw : valueGroup (.ofClass w) = ⊤ := valueGroup_eq_top_of_surjective w hw
  haveI : IsCyclic (valueGroup (.ofClass v)) := by rw [htopv]; infer_instance
  haveI : Nontrivial (valueGroup (.ofClass v)) := by rw [htopv]; infer_instance
  haveI : IsCyclic (valueGroup (.ofClass w)) := by rw [htopw]; infer_instance
  haveI : Nontrivial (valueGroup (.ofClass w)) := by rw [htopw]; infer_instance
  haveI : IsRankOneDiscrete v := inferInstance
  haveI : IsRankOneDiscrete w := inferInstance
  obtain ⟨π, hπ⟩ := hv (exp (-1))
  have hπv_lt : v π < 1 := hπ ▸ exp_neg_one_lt_one
  have hπv_ne : v π ≠ 0 := by rw [hπ]; exact exp_ne_zero
  have hwπ_lt : w π < 1 := (IsEquiv.lt_one_iff_lt_one h).1 hπv_lt
  have hwπ_ne : w π ≠ 0 := (IsEquiv.eq_zero h).not.1 hπv_ne
  have hwπ : w π = exp (-1) := by
    refine le_antisymm (lt_one_le_exp_neg_one hwπ_lt) ?_
    obtain ⟨y, hy⟩ := hw (exp (-1))
    have hy_lt : w y < 1 := hy ▸ exp_neg_one_lt_one
    have : w y ≤ w π := by
      have hyv_lt : v y < 1 := (IsEquiv.lt_one_iff_lt_one h).2 hy_lt
      have : v y ≤ v π := by
        rw [hπ]; exact lt_one_le_exp_neg_one hyv_lt
      exact (IsEquiv.le_iff_le h).1 this
    simpa [hy] using this
  ext x
  by_cases hx : x = 0
  · subst hx; simp
  · have hvne : v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    set n := WithZero.log (v x)
    have hvx : v x = exp n := (exp_log hvne).symm
    have hv1 : v (x * π ^ n) = 1 := by
      rw [map_mul, map_zpow₀, hvx, hπ, ← exp_zsmul, ← exp_add]
      simp [zsmul_eq_mul]
    have hw1 : w (x * π ^ n) = 1 := (IsEquiv.eq_one_iff_eq_one h).1 hv1
    have hwx : w x * (w π) ^ n = 1 := by
      simpa [map_mul, map_zpow₀] using hw1
    have hwx' : w x * exp (-n) = 1 := by
      rw [hwπ, ← exp_zsmul, zsmul_eq_mul, mul_neg, mul_one] at hwx
      exact hwx
    have : w x = exp n := by
      have hinv : (exp (-n) : ℤᵐ⁰)⁻¹ = exp n := by rw [← exp_neg, neg_neg]
      rw [← hinv]
      exact eq_inv_of_mul_eq_one_left hwx'
    rw [this, hvx]

/-- Extract the underlying additive valuation. -/
def polyAddVal {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) : AddValuation E (WithTop ℤ) :=
  nu.val

theorem polyAddVal_trivial {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) {b : Complex} (hb : b ≠ 0) :
    polyAddVal nu (algebraMap Complex E b) = 0 :=
  nu.property.1 b hb

theorem polyAddVal_surj {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (k : ℤ) :
    ∃ f : E, polyAddVal nu f = (k : WithTop ℤ) :=
  nu.property.2 k

/-- The `AlgebraicCurve.Place` associated to a `PolynomialCurvePlace`. -/
def toPlace {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) : Place Complex E where
  toValuationSubring := (mulOfAdd (polyAddVal nu)).valuationSubring
  algebraMap_mem' := fun b => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hb : b = 0
    · subst hb; simp [mulOfAdd_apply, map_zero]
    · have hnv := polyAddVal_trivial nu hb
      simp [mulOfAdd_apply, hnv, toZm0_zero]
  ne_top' := by
    intro htop
    have hnt : ¬(mulOfAdd (polyAddVal nu)).IsNontrivial :=
      (Valuation.valuationSubring_eq_top_iff (mulOfAdd (polyAddVal nu))).1 htop
    refine hnt ⟨?_⟩
    obtain ⟨x, hx⟩ := polyAddVal_surj nu (1 : ℤ)
    refine ⟨x, ?_, ?_⟩
    · rw [mulOfAdd_apply, hx, toZm0_coe]; exact exp_ne_zero
    · rw [mulOfAdd_apply, hx, toZm0_coe]
      exact (exp_eq_one).not.2 (by decide : (-1 : ℤ) ≠ 0)
  isPrincipalIdealRing' := mulOfAdd_isPrincipalIdealRing (polyAddVal nu) (polyAddVal_surj nu)

theorem toPlace_valuationSubring {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) :
    (toPlace nu).toValuationSubring = (mulOfAdd (polyAddVal nu)).valuationSubring :=
  rfl

/-- The adic valuation of `toPlace nu` recovers the original valuation ring. -/
theorem toPlace_adicValuation_valuationSubring {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) :
    (toPlace nu).adicValuation.valuationSubring = (toPlace nu).toValuationSubring := by
  apply ValuationSubring.toSubring_injective
  have hmap :=
    map_algebraMap_eq_valuationSubring
      (A := (toPlace nu).toValuationSubring) (K := E)
  change Subring.map (algebraMap (toPlace nu).toValuationSubring E) ⊤ =
      (toPlace nu).adicValuation.valuationSubring.toSubring at hmap
  refine hmap.symm.trans ?_
  ext x
  simp only [Subring.mem_map, Subring.mem_top, true_and]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- Multiplicative form equals the Place adic valuation. -/
theorem mulOfAdd_eq_adicValuation {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) :
    mulOfAdd (polyAddVal nu) = (toPlace nu).adicValuation := by
  refine eq_of_isEquiv_of_surjective _ _
    (mulOfAdd_surjective (polyAddVal nu) (polyAddVal_surj nu))
    (IsDedekindDomain.HeightOneSpectrum.valuation_surjective
      E (toPlace nu).heightOneSpectrum) ?_
  rw [isEquiv_iff_valuationSubring, toPlace_adicValuation_valuationSubring,
    toPlace_valuationSubring]

/-- Orders agree after transport. -/
theorem polynomialCurveOrder_eq_Place_ord {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (f : E) :
    polynomialCurveOrder nu f = (toPlace nu).ord f := by
  simp only [polynomialCurveOrder, Place.ord, polyAddVal]
  -- polynomialCurveOrder uses nu.val; polyAddVal = nu.val
  change (nu.val f).untop₀ = -WithZero.log ((toPlace nu).adicValuation f)
  rw [← mulOfAdd_eq_adicValuation nu, mulOfAdd_apply]
  change (nu.val f).untop₀ = -WithZero.log (toZm0 (nu.val f))
  induction h : nu.val f using WithTop.recTopCoe with
  | top =>
    -- log 0 = 0
    simp [toZm0]
  | coe n =>
    simp [toZm0, log_exp]

theorem toPlace_injective {E : Type} [Field E] [Algebra Complex E] :
    Function.Injective (toPlace (E := E)) := by
  intro nu₁ nu₂ h
  apply Subtype.ext
  ext f
  have hord : polynomialCurveOrder nu₁ f = polynomialCurveOrder nu₂ f := by
    rw [polynomialCurveOrder_eq_Place_ord, polynomialCurveOrder_eq_Place_ord, h]
  by_cases hf : f = 0
  · subst hf; simp [AddValuation.map_zero]
  · have hne₁ : nu₁.val f ≠ ⊤ := (AddValuation.ne_top_iff nu₁.val).2 hf
    have hne₂ : nu₂.val f ≠ ⊤ := (AddValuation.ne_top_iff nu₂.val).2 hf
    have : (nu₁.val f).untop₀ = (nu₂.val f).untop₀ := hord
    rw [← WithTop.coe_untop₀_of_ne_top hne₁, ← WithTop.coe_untop₀_of_ne_top hne₂, this]

theorem solution
    {E : Type} [Field E] [Algebra Complex E]
    [HasPrincipalDivisors Complex E] (f : E) :
    Set.Finite {nu : PolynomialCurvePlace E | polynomialCurveOrder nu f ≠ 0} := by
  classical
  by_cases hf : f = 0
  · subst hf
    have hempty :
        {nu : PolynomialCurvePlace E | polynomialCurveOrder nu 0 ≠ 0} = ∅ := by
      ext nu
      simp [polynomialCurveOrder, AddValuation.map_zero, WithTop.untop₀_top]
    simp [hempty]
  · obtain ⟨D, hD, _⟩ := HasPrincipalDivisors.exists_divisor (K := Complex) (F := E) f hf
    have hPlaceFin : Set.Finite {w : Place Complex E | w.ord f ≠ 0} := by
      refine D.support.finite_toSet.subset ?_
      intro w hw
      exact Finsupp.mem_support_iff.mpr (by rw [hD w]; exact hw)
    let S := {nu : PolynomialCurvePlace E | polynomialCurveOrder nu f ≠ 0}
    let T := {w : Place Complex E | w.ord f ≠ 0}
    have himage : Set.MapsTo toPlace S T := by
      intro nu hnu
      change (toPlace nu).ord f ≠ 0
      rwa [← polynomialCurveOrder_eq_Place_ord]
    have hinj : Set.InjOn toPlace S := fun _ _ _ _ heq => toPlace_injective heq
    exact Set.Finite.of_finite_image (hPlaceFin.subset himage.image_subset) hinj
