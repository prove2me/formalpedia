-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finsum_max_neg_polynomialCurveOrder_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:33:57.295396+00:00
-- url     : https://prove2.me/submissions/9242c8f5-c89d-4732-8c74-5a37e45bc1de

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Mathlib.Tactic

open Valuation WithZero MonoidWithZeroHom
open scoped BigOperators
open IntermediateField
open OAI.PiExponent.FormalInterpolation
open AlgebraicCurve
open IsDiscreteValuationRing
open IsLocalRing

noncomputable section

/-! ## Additive ↔ multiplicative conversion (shared with the Place bridge) -/

def toZm0 : WithTop ℤ → ℤᵐ⁰
  | ⊤ => 0
  | (n : ℤ) => exp (-n)

@[simp] theorem toZm0_top : toZm0 (⊤ : WithTop ℤ) = 0 := rfl
@[simp] theorem toZm0_coe (n : ℤ) : toZm0 (n : WithTop ℤ) = exp (-n) := rfl

theorem toZm0_zero : toZm0 (0 : WithTop ℤ) = 1 := by
  change toZm0 (↑(0 : ℤ)) = 1
  rw [toZm0_coe, neg_zero, exp_zero]

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

def fromZm0 : ℤᵐ⁰ → WithTop ℤ :=
  fun γ => if γ = 0 then ⊤ else ↑(-log γ)

theorem fromZm0_toZm0 : ∀ a : WithTop ℤ, fromZm0 (toZm0 a) = a
  | ⊤ => by simp [fromZm0]
  | (n : ℤ) => by simp [fromZm0, exp_ne_zero, log_exp]

theorem toZm0_fromZm0 (γ : ℤᵐ⁰) : toZm0 (fromZm0 γ) = γ := by
  by_cases h : γ = 0
  · simp [h, fromZm0]
  · have hform : fromZm0 γ = ↑(-log γ) := by simp [fromZm0, h]
    rw [hform, toZm0_coe, neg_neg, exp_log h]

theorem fromZm0_one : fromZm0 (1 : ℤᵐ⁰) = 0 := by
  simp [fromZm0, log_one]

theorem fromZm0_mul (a b : ℤᵐ⁰) : fromZm0 (a * b) = fromZm0 a + fromZm0 b := by
  by_cases ha : a = 0
  · simp [ha, fromZm0]
  by_cases hb : b = 0
  · simp [hb, fromZm0]
  · have ha' : fromZm0 a = ↑(-log a) := by simp [fromZm0, ha]
    have hb' : fromZm0 b = ↑(-log b) := by simp [fromZm0, hb]
    have hab' : fromZm0 (a * b) = ↑(-log (a * b)) := by
      simp [fromZm0, mul_eq_zero, ha, hb]
    rw [ha', hb', hab', log_mul ha hb, neg_add, WithTop.coe_add]

theorem fromZm0_antitone : Antitone fromZm0 := by
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    have ha0 : a = 0 := le_zero_iff.mp hab
    subst ha0
    simp [fromZm0]
  by_cases ha : a = 0
  · subst ha
    simp [fromZm0]  -- fromZm0 b ≤ ⊤
  · have ha' : fromZm0 a = ↑(-log a) := by simp [fromZm0, ha]
    have hb' : fromZm0 b = ↑(-log b) := by simp [fromZm0, hb]
    rw [ha', hb', WithTop.coe_le_coe]
    have : log a ≤ log b :=
      (exp_le_exp).1 (by simpa [exp_log ha, exp_log hb] using hab)
    exact neg_le_neg this

theorem fromZm0_max (a b : ℤᵐ⁰) :
    fromZm0 (max a b) = min (fromZm0 a) (fromZm0 b) :=
  fromZm0_antitone.map_max

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

def addOfMul {E : Type} [Field E] (v : Valuation E ℤᵐ⁰) : AddValuation E (WithTop ℤ) :=
  AddValuation.of (fun x => fromZm0 (v x))
    (by simp [fromZm0, map_zero])
    (by simp [map_one, fromZm0_one])
    (fun x y => by
      have h := v.map_add x y
      have := fromZm0_antitone h
      simpa [fromZm0_max] using this)
    (fun x y => by simp [map_mul, fromZm0_mul])

theorem addOfMul_apply {E : Type} [Field E] (v : Valuation E ℤᵐ⁰) (x : E) :
    addOfMul v x = fromZm0 (v x) := rfl

theorem mulOfAdd_surjective {E : Type} [Field E]
    (v : AddValuation E (WithTop ℤ))
    (hsurj : ∀ k : ℤ, ∃ x : E, v x = (k : WithTop ℤ)) :
    Function.Surjective (mulOfAdd v) := by
  intro γ
  induction γ using WithZero.recZeroCoe with
  | zero => exact ⟨0, by simp [mulOfAdd_apply, AddValuation.map_zero]⟩
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
  haveI : IsCyclic (valueGroup (.ofClass (mulOfAdd v))) := by rw [htop]; infer_instance
  haveI : Nontrivial (valueGroup (.ofClass (mulOfAdd v))) := by rw [htop]; infer_instance
  exact Valuation.valuationSubring_isPrincipalIdealRing (mulOfAdd v)

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
  have hwπ : w π = exp (-1) := by
    refine le_antisymm (lt_one_le_exp_neg_one hwπ_lt) ?_
    obtain ⟨y, hy⟩ := hw (exp (-1))
    have hy_lt : w y < 1 := hy ▸ exp_neg_one_lt_one
    have : w y ≤ w π := by
      have hyv_lt : v y < 1 := (IsEquiv.lt_one_iff_lt_one h).2 hy_lt
      have : v y ≤ v π := by rw [hπ]; exact lt_one_le_exp_neg_one hyv_lt
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
    have hwx : w x * (w π) ^ n = 1 := by simpa [map_mul, map_zpow₀] using hw1
    have hwx' : w x * exp (-n) = 1 := by
      rw [hwπ, ← exp_zsmul, zsmul_eq_mul, mul_neg, mul_one] at hwx
      exact hwx
    have : w x = exp n := by
      have hinv : (exp (-n) : ℤᵐ⁰)⁻¹ = exp n := by rw [← exp_neg, neg_neg]
      rw [← hinv]
      exact eq_inv_of_mul_eq_one_left hwx'
    rw [this, hvx]

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

theorem mulOfAdd_eq_adicValuation {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) :
    mulOfAdd (polyAddVal nu) = (toPlace nu).adicValuation := by
  refine eq_of_isEquiv_of_surjective _ _
    (mulOfAdd_surjective (polyAddVal nu) (polyAddVal_surj nu))
    (IsDedekindDomain.HeightOneSpectrum.valuation_surjective
      E (toPlace nu).heightOneSpectrum) ?_
  rw [isEquiv_iff_valuationSubring, toPlace_adicValuation_valuationSubring,
    toPlace_valuationSubring]

theorem polynomialCurveOrder_eq_Place_ord {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (f : E) :
    polynomialCurveOrder nu f = (toPlace nu).ord f := by
  simp only [polynomialCurveOrder, Place.ord]
  change (nu.val f).untop₀ = -WithZero.log ((toPlace nu).adicValuation f)
  rw [← mulOfAdd_eq_adicValuation nu, mulOfAdd_apply]
  change (nu.val f).untop₀ = -WithZero.log (toZm0 (nu.val f))
  induction h : nu.val f using WithTop.recTopCoe with
  | top => simp [toZm0]
  | coe n => simp [toZm0, log_exp]

/-! ## Inverse: Place → PolynomialCurvePlace -/

theorem Place.ord_algebraMap {E : Type} [Field E] [Algebra Complex E]
    (w : Place Complex E) {b : Complex} (hb : b ≠ 0) :
    w.ord (algebraMap Complex E b) = 0 := by
  have hmem : algebraMap Complex E b ∈ w.toValuationSubring := w.algebraMap_mem' b
  have hne : algebraMap Complex E b ≠ 0 := by
    intro h0
    exact hb ((injective_iff_map_eq_zero (algebraMap Complex E)).1
      (RingHom.injective _) b h0)
  have hunit : IsUnit (⟨algebraMap Complex E b, hmem⟩ : w.toValuationSubring) := by
    by_contra hnu
    have hres0 : residue w.toValuationSubring ⟨algebraMap Complex E b, hmem⟩ = 0 := by
      by_contra hne
      exact hnu ((residue_ne_zero_iff_isUnit _).1 hne)
    have hinj : Function.Injective (algebraMap Complex w.ResidueField) :=
      RingHom.injective _
    have hcoe : (algebraMap Complex w.ResidueField) b =
        residue w.toValuationSubring (algebraMap Complex w.toValuationSubring b) := by
      rfl
    have : algebraMap Complex w.ResidueField b = 0 := by
      rw [hcoe]; exact hres0
    exact hb (hinj (by simpa using this))
  have hadic : w.adicValuation (algebraMap Complex E b) = 1 :=
    (w.adicValuation_coe_eq_one_iff ⟨_, hmem⟩).2 hunit
  simp [Place.ord, hadic, log_one]

def fromPlace {E : Type} [Field E] [Algebra Complex E]
    (w : Place Complex E) : PolynomialCurvePlace E :=
  ⟨addOfMul w.adicValuation, by
    constructor
    · intro b hb
      have hord := Place.ord_algebraMap w hb
      have hne0 : algebraMap Complex E b ≠ 0 := by
        intro h0
        exact hb ((injective_iff_map_eq_zero (algebraMap Complex E)).1
          (RingHom.injective _) b h0)
      have hne := w.adicValuation_ne_zero hne0
      have hlog : WithZero.log (w.adicValuation (algebraMap Complex E b)) = 0 := by
        simpa [Place.ord, neg_eq_zero] using hord
      have : w.adicValuation (algebraMap Complex E b) = 1 := by
        rw [← exp_log hne, hlog, exp_zero]
      simp [addOfMul_apply, this, fromZm0_one]
    · intro k
      obtain ⟨y, hy⟩ :=
        IsDedekindDomain.HeightOneSpectrum.valuation_surjective E w.heightOneSpectrum
          (exp (-k))
      refine ⟨y, ?_⟩
      change fromZm0 (w.adicValuation y) = (k : WithTop ℤ)
      rw [show w.adicValuation y = exp (-k) from hy]
      have : fromZm0 (exp (-k) : ℤᵐ⁰) = ↑k := by
        simp [fromZm0, exp_ne_zero, log_exp]
      exact this⟩

theorem fromPlace_ord {E : Type} [Field E] [Algebra Complex E]
    (w : Place Complex E) (f : E) :
    polynomialCurveOrder (fromPlace w) f = w.ord f := by
  simp only [polynomialCurveOrder, Place.ord, fromPlace, addOfMul_apply]
  by_cases hf : w.adicValuation f = 0
  · simp [hf, fromZm0]
  · have hform : fromZm0 (w.adicValuation f) = ↑(-log (w.adicValuation f)) := by
      simp [fromZm0, hf]
    rw [hform, WithTop.untop₀_coe]

theorem toPlace_fromPlace {E : Type} [Field E] [Algebra Complex E]
    (w : Place Complex E) : toPlace (fromPlace w) = w := by
  apply Place.ext
  -- valuation rings equal: mulOfAdd (addOfMul adic) = adic (via toZm0_fromZm0), same VR
  have hmul : mulOfAdd (addOfMul w.adicValuation) = w.adicValuation := by
    ext x; simp [mulOfAdd_apply, addOfMul_apply, toZm0_fromZm0]
  -- toPlace.fromPlace.VR = mulOfAdd(addOfMul adic).VR = adic.VR = w.VR
  have hadicVR : w.adicValuation.valuationSubring = w.toValuationSubring := by
    -- same as toPlace_adicValuation_valuationSubring argument
    apply ValuationSubring.toSubring_injective
    have hmap := map_algebraMap_eq_valuationSubring (A := w.toValuationSubring) (K := E)
    change Subring.map (algebraMap w.toValuationSubring E) ⊤ =
        w.adicValuation.valuationSubring.toSubring at hmap
    refine hmap.symm.trans ?_
    ext x
    simp only [Subring.mem_map, Subring.mem_top, true_and]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  change (mulOfAdd (polyAddVal (fromPlace w))).valuationSubring = w.toValuationSubring
  simp only [fromPlace, polyAddVal]
  rw [hmul, hadicVR]

theorem fromPlace_toPlace {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) : fromPlace (toPlace nu) = nu := by
  apply Subtype.ext
  ext f
  have hmul := mulOfAdd_eq_adicValuation nu
  -- fromPlace (toPlace nu) applies addOfMul to (toPlace nu).adicValuation
  change fromZm0 ((toPlace nu).adicValuation f) = nu.val f
  rw [← hmul, mulOfAdd_apply, fromZm0_toZm0]
  rfl

theorem fromPlace_injective {E : Type} [Field E] [Algebra Complex E] :
    Function.Injective (fromPlace (E := E)) := by
  intro w₁ w₂ h
  have := congrArg toPlace h
  simpa [toPlace_fromPlace] using this

theorem solution
    {E : Type} [Field E] [Algebra Complex E]
    (x : E) (hx : Transcendental Complex x)
    (hfin : FiniteDimensional (IntermediateField.adjoin Complex ({x} : Set E)) E) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (-(polynomialCurveOrder nu x : Real)) 0) =
      (Module.finrank (IntermediateField.adjoin Complex ({x} : Set E)) E : Real) := by
  classical
  obtain ⟨S, hSmem, hSsum⟩ :=
    exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
      (k := Complex) (F := E) x hx hfin
  let g : PolynomialCurvePlace E → ℝ :=
    fun nu => max (-(polynomialCurveOrder nu x : ℝ)) 0
  have hsupp : Function.support g ⊆ ↑(S.image fromPlace) := by
    intro nu hnu
    have hne : g nu ≠ 0 := hnu
    have hlt : polynomialCurveOrder nu x < 0 := by
      by_contra hge
      push_neg at hge
      have : g nu = 0 := by
        simp only [g]
        exact max_eq_right (neg_nonpos.2 (by exact_mod_cast hge))
      exact hne this
    have hPlace : (toPlace nu).ord x < 0 := by
      rwa [← polynomialCurveOrder_eq_Place_ord]
    have hmemS : toPlace nu ∈ S := (hSmem _).2 hPlace
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨toPlace nu, hmemS, fromPlace_toPlace nu⟩)
  have hsum :
      ∑ᶠ nu : PolynomialCurvePlace E, g nu =
        ∑ nu ∈ S.image fromPlace, g nu :=
    finsum_eq_finsetSum_of_support_subset g hsupp
  have hinj : Set.InjOn fromPlace (↑S : Set (Place Complex E)) :=
    fun _ _ _ _ h => fromPlace_injective h
  rw [hsum, Finset.sum_image hinj]
  have hord : ∀ P ∈ S, polynomialCurveOrder (fromPlace P) x = P.ord x :=
    fun P _ => fromPlace_ord P x
  have hneg : ∀ P ∈ S, P.ord x < 0 := fun P hP => (hSmem P).1 hP
  have hterm : ∀ P ∈ S,
      g (fromPlace P) = (-(P.ord x : ℝ)) := by
    intro P hP
    change max (-(polynomialCurveOrder (fromPlace P) x : ℝ)) 0 = (-(P.ord x : ℝ))
    rw [hord P hP]
    exact max_eq_left (le_of_lt (by exact_mod_cast neg_pos.2 (hneg P hP)))
  refine (Finset.sum_congr rfl fun P hP => hterm P hP).trans ?_
  have : (∑ P ∈ S, (-(P.ord x : ℝ))) =
      ((∑ P ∈ S, (-P.ord x) : ℤ) : ℝ) := by
    simp [Int.cast_sum, Int.cast_neg]
  rw [this, hSsum]
  exact_mod_cast rfl
