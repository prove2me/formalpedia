-- Prove2me | solution 1 for ModularCurve.exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/916bf53d-d451-5566-a658-248d999e5eed

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open ModularCurve

namespace GaussResidue

section ValuationHelpers

variable {K : Type*} [Field K]

theorem isUnit_iff_inv_mem (A : ValuationSubring K) {a : K} (ha : a ∈ A) (ha0 : a ≠ 0) :
    IsUnit (⟨a, ha⟩ : A) ↔ a⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu⟩
    have hmul : ((↑u⁻¹ : A) : K) * a = 1 := by
      have := congrArg (fun y : A => (y : K)) u.inv_mul
      simpa [hu] using this
    rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
  · intro h
    exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ ha0),
      Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩

theorem mem_nonunits_iff' (A : ValuationSubring K) (a : K) :
    a ∈ A.nonunits ↔ a ∈ A ∧ (a = 0 ∨ a⁻¹ ∉ A) := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨ha, hm⟩
    refine ⟨ha, ?_⟩
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · right
      intro hinv
      exact ((IsLocalRing.mem_maximalIdeal _).mp hm) ((isUnit_iff_inv_mem A ha ha0).mpr hinv)
  · rintro ⟨ha, h⟩
    refine ⟨ha, (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_⟩
    rcases h with h0 | hinv
    · subst h0
      exact not_isUnit_zero (by
        have : (⟨(0 : K), ha⟩ : A) = 0 := Subtype.ext rfl
        rwa [this] at hu)
    · have ha0 : a ≠ 0 := by
        rintro rfl
        have : (⟨(0 : K), ha⟩ : A) = 0 := Subtype.ext rfl
        rw [this] at hu; exact not_isUnit_zero hu
      exact hinv ((isUnit_iff_inv_mem A ha ha0).mp hu)

theorem mul_mem_nonunits (A : ValuationSubring K) {a b : K} (ha : a ∈ A.nonunits) (hb : b ∈ A) :
    a * b ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at ha ⊢
  rw [map_mul]
  calc A.valuation a * A.valuation b ≤ A.valuation a * 1 :=
        mul_le_mul_right ((A.valuation_le_one_iff b).mpr hb) _
    _ = A.valuation a := mul_one _
    _ < 1 := ha

end ValuationHelpers

section Gauss

variable (p : ℕ) [Fact p.Prime] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
  (W : ValuationSubring ↥F₀)

abbrev ιQ : LaurentSeries ℤ →+* LaurentSeries ℚ := coeffMap (Int.castRingHom ℚ)

abbrev ϖ : LaurentSeries ℤ →+* LaurentSeries (ZMod p) := coeffMap (Int.castRingHom (ZMod p))

theorem ιQ_injective : Function.Injective ιQ := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries ℚ => s.coeff n) h
  simp only [coeffMap_coeff, eq_intCast, Int.cast_inj] at h1
  exact h1

def IsPair (f : ↥F₀) (x y : LaurentSeries ℤ) : Prop :=
  ϖ p y ≠ 0 ∧ (f : LaurentSeries ℚ) * ιQ y = ιQ x

variable {p F₀}

theorem IsPair.mul {f g : ↥F₀} {x y x' y' : LaurentSeries ℤ} (h : IsPair p F₀ f x y)
    (h' : IsPair p F₀ g x' y') : IsPair p F₀ (f * g) (x * x') (y * y') := by
  refine ⟨?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero h.1 h'.1
  · rw [IntermediateField.coe_mul, map_mul, map_mul, ← h.2, ← h'.2]; ring

theorem IsPair.add {f g : ↥F₀} {x y x' y' : LaurentSeries ℤ} (h : IsPair p F₀ f x y)
    (h' : IsPair p F₀ g x' y') : IsPair p F₀ (f + g) (x * y' + x' * y) (y * y') := by
  refine ⟨?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero h.1 h'.1
  · rw [IntermediateField.coe_add, map_mul, map_add, map_mul, map_mul, ← h.2, ← h'.2]; ring

theorem isPair_one : IsPair p F₀ 1 1 1 := by
  refine ⟨by rw [map_one]; exact one_ne_zero, ?_⟩
  rw [IntermediateField.coe_one, map_one, one_mul]

theorem isPair_zero : IsPair p F₀ 0 0 1 := by
  refine ⟨by rw [map_one]; exact one_ne_zero, ?_⟩
  rw [IntermediateField.coe_zero, map_one, map_zero, zero_mul]

theorem IsPair.red_eq {f : ↥F₀} {x y x' y' : LaurentSeries ℤ} (h : IsPair p F₀ f x y)
    (h' : IsPair p F₀ f x' y') : ϖ p x * (ϖ p y)⁻¹ = ϖ p x' * (ϖ p y')⁻¹ := by
  have key : x * y' = x' * y := by
    apply ιQ_injective
    rw [map_mul, map_mul, ← h.2, ← h'.2]; ring
  rw [mul_inv_eq_iff_eq_mul₀ h.1, mul_assoc, mul_comm _ (ϖ p y), ← mul_assoc,
    eq_comm, mul_inv_eq_iff_eq_mul₀ h'.1, ← map_mul, ← map_mul, key, mul_comm]

variable (p F₀)

def divP (x : LaurentSeries ℤ) : LaurentSeries ℤ where
  coeff n := x.coeff n / p
  isPWO_support' := x.isPWO_support.mono (by
    intro n hn
    change x.coeff n / p ≠ 0 at hn
    change x.coeff n ≠ 0
    intro h0
    apply hn
    rw [h0, Int.zero_ediv])

theorem natCast_mul_divP {x : LaurentSeries ℤ} (hx : ϖ p x = 0) :
    ((p : ℤ) : LaurentSeries ℤ) * divP p x = x := by
  have hC : ((p : ℤ) : LaurentSeries ℤ) = HahnSeries.C (p : ℤ) :=
    (map_natCast (HahnSeries.C : ℤ →+* LaurentSeries ℤ) p).symm
  rw [hC, HahnSeries.C_mul_eq_smul]
  ext n
  rw [HahnSeries.coeff_smul, smul_eq_mul]
  change (p : ℤ) * (x.coeff n / p) = x.coeff n
  have hdvd : (p : ℤ) ∣ x.coeff n := by
    have h1 : (ϖ p x).coeff n = 0 := by rw [hx]; rfl
    rw [coeffMap_coeff, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    exact h1
  exact Int.mul_ediv_cancel' hdvd

theorem coe_p_inv : ((((p : ℕ) : ↥F₀)⁻¹ : ↥F₀) : LaurentSeries ℚ) = ((p : ℕ) : LaurentSeries ℚ)⁻¹ := by
  rw [IntermediateField.coe_inv]
  push_cast
  rfl

theorem ϖ_natCast_p : ϖ p ((p : ℤ) : LaurentSeries ℤ) = 0 := by
  rw [map_intCast, Int.cast_natCast, ← map_natCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p)) p,
    ZMod.natCast_self, map_zero]

theorem ιQ_natCast_p : ιQ ((p : ℤ) : LaurentSeries ℤ) = ((p : ℕ) : LaurentSeries ℚ) := by
  rw [map_intCast, Int.cast_natCast]

variable (hW : ∀ f : ↥F₀, f ∈ W ↔ ∃ x y : LaurentSeries ℤ, ϖ p y ≠ 0 ∧
    (f : LaurentSeries ℚ) * ιQ y = ιQ x)

include hW

theorem exists_isPair (f : ↥W) : ∃ xy : LaurentSeries ℤ × LaurentSeries ℤ, IsPair p F₀ f xy.1 xy.2 := by
  obtain ⟨x, y, hy, hxy⟩ := (hW f).mp f.2
  exact ⟨(x, y), hy, hxy⟩

def redFun (f : ↥W) : LaurentSeries (ZMod p) :=
  ϖ p (Classical.choose (exists_isPair p F₀ W hW f)).1 *
    (ϖ p (Classical.choose (exists_isPair p F₀ W hW f)).2)⁻¹

theorem redFun_eq {f : ↥W} {x y : LaurentSeries ℤ} (h : IsPair p F₀ f x y) :
    redFun p F₀ W hW f = ϖ p x * (ϖ p y)⁻¹ :=
  (Classical.choose_spec (exists_isPair p F₀ W hW f)).red_eq h

theorem redFun_mul_eq {f : ↥W} {x y : LaurentSeries ℤ} (h : IsPair p F₀ f x y) :
    redFun p F₀ W hW f * ϖ p y = ϖ p x := by
  rw [redFun_eq p F₀ W hW h, inv_mul_cancel_right₀ h.1]

def red : ↥W →+* LaurentSeries (ZMod p) where
  toFun := redFun p F₀ W hW
  map_one' := by
    have h := redFun_mul_eq p F₀ W hW (f := (1 : ↥W)) (by exact isPair_one)
    rwa [map_one, mul_one] at h
  map_mul' f g := by
    obtain ⟨⟨x, y⟩, h⟩ := exists_isPair p F₀ W hW f
    obtain ⟨⟨x', y'⟩, h'⟩ := exists_isPair p F₀ W hW g
    have hfg : IsPair p F₀ ((f * g : ↥W) : ↥F₀) (x * x') (y * y') := h.mul h'
    rw [redFun_eq p F₀ W hW hfg, redFun_eq p F₀ W hW h, redFun_eq p F₀ W hW h', map_mul, map_mul,
      mul_inv]
    ring
  map_zero' := by
    have h := redFun_mul_eq p F₀ W hW (f := (0 : ↥W)) (by exact isPair_zero)
    rwa [map_one, mul_one, map_zero] at h
  map_add' f g := by
    obtain ⟨⟨x, y⟩, h⟩ := exists_isPair p F₀ W hW f
    obtain ⟨⟨x', y'⟩, h'⟩ := exists_isPair p F₀ W hW g
    have hfg : IsPair p F₀ ((f + g : ↥W) : ↥F₀) (x * y' + x' * y) (y * y') := h.add h'
    rw [redFun_eq p F₀ W hW hfg, redFun_eq p F₀ W hW h, redFun_eq p F₀ W hW h', map_mul, map_add,
      map_mul, map_mul, mul_inv]
    have hy := h.1
    have hy' := h'.1
    field_simp

theorem red_apply (f : ↥W) : red p F₀ W hW f = redFun p F₀ W hW f := rfl

theorem p_inv_notMem : ((p : ℕ) : ↥F₀)⁻¹ ∉ W := by
  intro h
  obtain ⟨x, y, hy, hxy⟩ := (hW _).mp h
  apply hy
  have hp0 : ((p : ℕ) : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) p]
    exact HahnSeries.C_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have h1 : ιQ y = ιQ (((p : ℤ) : LaurentSeries ℤ) * x) := by
    rw [map_mul, ιQ_natCast_p, ← hxy, coe_p_inv, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  rw [ιQ_injective h1, map_mul, ϖ_natCast_p, zero_mul]

theorem p_mem_nonunits : ((p : ℕ) : ↥F₀) ∈ W.nonunits := by
  rw [mem_nonunits_iff']
  refine ⟨(hW _).mpr ⟨((p : ℤ) : LaurentSeries ℤ), 1, by rw [map_one]; exact one_ne_zero, ?_⟩,
    Or.inr (p_inv_notMem p F₀ W hW)⟩
  rw [map_one, mul_one, ιQ_natCast_p]
  push_cast
  rfl

theorem red_eq_zero_iff (f : ↥W) : red p F₀ W hW f = 0 ↔ (f : ↥F₀) ∈ W.nonunits := by
  obtain ⟨⟨x, y⟩, h⟩ := exists_isPair p F₀ W hW f
  have hred : red p F₀ W hW f * ϖ p y = ϖ p x := redFun_mul_eq p F₀ W hW h
  have hp0 : ((p : ℕ) : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) p]
    exact HahnSeries.C_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hp0F : ((p : ℕ) : ↥F₀) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  constructor
  · intro h0
    have hx : ϖ p x = 0 := by rw [← hred, h0, zero_mul]

    have hg : (f : ↥F₀) * ((p : ℕ) : ↥F₀)⁻¹ ∈ W := by
      rw [hW]
      refine ⟨divP p x, y, h.1, ?_⟩
      apply mul_left_cancel₀ hp0
      rw [IntermediateField.coe_mul, coe_p_inv]
      calc ((p : ℕ) : LaurentSeries ℚ) * (((f : ↥F₀) : LaurentSeries ℚ) *
            ((p : ℕ) : LaurentSeries ℚ)⁻¹ * ιQ y)
          = ((f : ↥F₀) : LaurentSeries ℚ) * ιQ y := by field_simp
        _ = ιQ x := h.2
        _ = ιQ (((p : ℤ) : LaurentSeries ℤ) * divP p x) := by rw [natCast_mul_divP p hx]
        _ = ((p : ℕ) : LaurentSeries ℚ) * ιQ (divP p x) := by rw [map_mul, ιQ_natCast_p]
    have hf : (f : ↥F₀) = ((p : ℕ) : ↥F₀) * ((f : ↥F₀) * ((p : ℕ) : ↥F₀)⁻¹) := by
      field_simp
    rw [hf]
    exact mul_mem_nonunits W (p_mem_nonunits p F₀ W hW) hg
  · intro hn
    by_contra h0
    have hx : ϖ p x ≠ 0 := by rw [← hred]; exact mul_ne_zero h0 h.1
    have hf0 : ((f : ↥F₀) : LaurentSeries ℚ) ≠ 0 := by
      intro e
      apply hx
      have h2 : ιQ x = ιQ 0 := by rw [← h.2, e, zero_mul, map_zero]
      rw [ιQ_injective h2, map_zero]
    have hf0' : (f : ↥F₀) ≠ 0 := fun e => hf0 (by rw [e]; rfl)
    have hinv : (f : ↥F₀)⁻¹ ∈ W := by
      rw [hW]
      refine ⟨y, x, hx, ?_⟩
      rw [IntermediateField.coe_inv, ← h.2, inv_mul_cancel_left₀ hf0]
    exact ((mem_nonunits_iff' W _).mp hn).2.elim hf0' (fun h' => h' hinv)

end Gauss

end GaussResidue

end

open ModularCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (W : ValuationSubring ↥F₀)
    (hW : ∀ f : ↥F₀, f ∈ W ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x) :
    ∃ red : ↥W →+* LaurentSeries (ZMod p),
      (∀ f : ↥W, red f = 0 ↔ (f : ↥F₀) ∈ W.nonunits) ∧
      ∀ (f : ↥W) (x y : LaurentSeries ℤ), coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 →
        ((f : ↥F₀) : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y =
          coeffMap (Int.castRingHom ℚ) x →
        red f * coeffMap (Int.castRingHom (ZMod p)) y = coeffMap (Int.castRingHom (ZMod p)) x :=
  ⟨GaussResidue.red p F₀ W hW, GaussResidue.red_eq_zero_iff p F₀ W hW,
    fun _ _ _ hy hxy => GaussResidue.redFun_mul_eq p F₀ W hW ⟨hy, hxy⟩⟩

end S_ModularCurve_exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring
end P2MW
export P2MW.S_ModularCurve_exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring (solution)
