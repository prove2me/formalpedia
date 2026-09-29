-- Prove2me | solution 1 for MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4d28ee69-326f-5939-a369-177a54fa1c55

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_MvPolynomial_finrank_piece_eq_of_maximal_growth
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

namespace PERSISTSOL

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)
def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by simp [Nat.macaulayPow]

theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

theorem d_le_top (d a : ℕ) : d ≤ top d a := le_top_of_choose_le d a d (by simp)

theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

theorem top_zero_left (a : ℕ) : top 0 a = a := by
  apply le_antisymm
  · have := choose_top_le 0 a; simpa using this
  · exact le_top_of_choose_le 0 a a (by simp)

theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by simp [rem, top_zero_left]

theorem top_zero_right (d : ℕ) : top d 0 = d := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have h1 : (d + 1).choose (d + 1) ≤ (top d 0).choose (d + 1) := Nat.choose_le_choose _ h
    have h2 := choose_top_le d 0
    simp at h1; omega
  · exact d_le_top d 0

theorem rem_zero_right (d : ℕ) : rem d 0 = 0 := by simp [rem]

theorem macaulayPow_zero_right : ∀ d : ℕ, Nat.macaulayPow d 0 = 0
  | 0 => macaulayPow_zero 0
  | d + 1 => by
      rw [macaulayPow_succ, top_zero_right, rem_zero_right, macaulayPow_zero_right d,
        Nat.choose_eq_zero_of_lt (by omega)]

theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    Nat.macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow_zero]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ]
      show _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : Nat.macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

theorem macaulayPow_mono : ∀ (d : ℕ) {a b : ℕ}, a ≤ b → Nat.macaulayPow d a ≤ Nat.macaulayPow d b
  | 0, a, b, _ => by simp [macaulayPow_zero]
  | d + 1, a, b, h => by
      have ht : top d a ≤ top d b := le_top_of_choose_le d b _ ((choose_top_le d a).trans h)
      rcases ht.eq_or_lt with ht | ht
      · rw [macaulayPow_succ, macaulayPow_succ, ht]
        have hr : rem d a ≤ rem d b := by
          have ha := rem_add_choose d a; have hb := rem_add_choose d b; rw [ht] at ha; omega
        have := macaulayPow_mono d hr
        omega
      · have h1 : Nat.macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 1 + 1) :=
          macaulayPow_lt_choose (d + 1) (top d a + 1) a (lt_choose_top_succ d a)
        have h2 : (top d a + 1 + 1).choose (d + 1 + 1) ≤ (top d b + 1).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ (by omega)
        have h3 : (top d b + 1).choose (d + 1 + 1) ≤ Nat.macaulayPow (d + 1) b := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

variable (n : ℕ)

noncomputable def Mon (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
    (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm)).toFinset

@[scoped simp] theorem mem_Mon (e : ℕ) (m : Fin (n + 1) →₀ ℕ) : m ∈ Mon n e ↔ m.degree = e := by
  simp [Mon]

noncomputable def MonW (w e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  (Mon n e).filter (fun m => ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0)

theorem mem_MonW (w e : ℕ) (m : Fin (n + 1) →₀ ℕ) :
    m ∈ MonW n w e ↔ m.degree = e ∧ ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0 := by
  simp [MonW]

theorem MonW_mono {w w' : ℕ} (h : w ≤ w') (e : ℕ) : MonW n w e ⊆ MonW n w' e := by
  intro m hm
  rw [mem_MonW] at hm ⊢
  exact ⟨hm.1, fun i hi => hm.2 i (h.trans hi)⟩

theorem MonW_of_le {w : ℕ} (h : n + 1 ≤ w) (e : ℕ) : MonW n w e = Mon n e := by
  ext m
  simp only [mem_MonW, mem_Mon, and_iff_left_iff_imp]
  intro _ i hi
  exact absurd (lt_of_lt_of_le i.2 (h.trans hi)) (lt_irrefl _)

noncomputable def var (j : ℕ) (h : j < n + 1) : Fin (n + 1) →₀ ℕ := Finsupp.single ⟨j, h⟩ 1

@[scoped simp] theorem var_apply (j : ℕ) (h : j < n + 1) (i : Fin (n + 1)) :
    var n j h i = if (i : ℕ) = j then 1 else 0 := by
  simp only [var, Finsupp.single_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

@[scoped simp] theorem degree_var (j : ℕ) (h : j < n + 1) : (var n j h).degree = 1 := by
  simp [var]

noncomputable def shift (j : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  if h : j < n + 1 then B.map (addRightEmbedding (var n j h)) else ∅

theorem shift_of_le {j : ℕ} (h : n + 1 ≤ j) (B : Finset (Fin (n + 1) →₀ ℕ)) : shift n j B = ∅ := by
  simp [shift, not_lt.mpr h]

theorem mem_shift {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ shift n j B ↔ ∃ b ∈ B, b + var n j h = u := by
  simp [shift, h]

theorem card_shift {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    (shift n j B).card = B.card := by
  simp [shift, h]

@[scoped simp] theorem shift_empty (j : ℕ) : shift n j (∅ : Finset (Fin (n + 1) →₀ ℕ)) = ∅ := by
  unfold shift; split_ifs <;> simp

theorem shift_mono (j : ℕ) {B B' : Finset (Fin (n + 1) →₀ ℕ)} (hB : B ⊆ B') :
    shift n j B ⊆ shift n j B' := by
  unfold shift; split_ifs
  · exact Finset.map_subset_map.mpr hB
  · exact Finset.Subset.refl _

theorem sub_var_add_var {j : ℕ} (h : j < n + 1) (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u ⟨j, h⟩) :
    u - var n j h + var n j h = u := by
  unfold var
  exact Finsupp.sub_add_single_one_cancel (by omega)

theorem add_var_sub_var {j : ℕ} (h : j < n + 1) (b : Fin (n + 1) →₀ ℕ) :
    b + var n j h - var n j h = b := by
  simp

theorem mem_shift_iff {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ))
    (u : Fin (n + 1) →₀ ℕ) :
    u ∈ shift n j B ↔ 1 ≤ u ⟨j, h⟩ ∧ u - var n j h ∈ B := by
  rw [mem_shift n h]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨?_, by simpa using hb⟩
    simp [var]
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, sub_var_add_var n h u h1⟩

theorem degree_sub_var {j : ℕ} (h : j < n + 1) (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u ⟨j, h⟩) :
    (u - var n j h).degree + 1 = u.degree := by
  conv_rhs => rw [← sub_var_add_var n h u hu]
  rw [map_add, degree_var]

theorem MonW_succ {j : ℕ} (h : j < n + 1) (e : ℕ) :
    MonW n (j + 1) (e + 1) = MonW n j (e + 1) ∪ shift n j (MonW n (j + 1) e) := by
  ext u
  rw [Finset.mem_union, mem_shift_iff n h, mem_MonW, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨hdeg, hsupp⟩
    by_cases huj : u ⟨j, h⟩ = 0
    · refine Or.inl ⟨hdeg, fun i hi => ?_⟩
      rcases hi.eq_or_lt with hij | hij
      · have : i = ⟨j, h⟩ := Fin.ext hij.symm
        rw [this]; exact huj
      · exact hsupp i hij
    · refine Or.inr ⟨by omega, ?_, fun i hi => ?_⟩
      · have := degree_sub_var n h u (by omega)
        omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply]
        rw [hsupp i hi]; simp
  · rintro (⟨hdeg, hsupp⟩ | ⟨h1, hdeg, hsupp⟩)
    · exact ⟨hdeg, fun i hi => hsupp i (by omega)⟩
    · refine ⟨?_, fun i hi => ?_⟩
      · have := degree_sub_var n h u h1
        omega
      · have := hsupp i hi
        simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply] at this
        have hij : (i : ℕ) ≠ j := by omega
        simpa [hij] using this

theorem disjoint_MonW_shift (j e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    Disjoint (MonW n j e) (shift n j B) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  by_cases h : j < n + 1
  · rw [mem_shift_iff n h] at hu'
    rw [mem_MonW] at hu
    have := hu.2 ⟨j, h⟩ le_rfl
    omega
  · rw [shift_of_le n (not_lt.mp h)] at hu'
    simp at hu'

theorem MonW_zero_succ (e : ℕ) : MonW n 0 (e + 1) = ∅ := by
  ext u
  simp only [mem_MonW, Finset.notMem_empty, iff_false, not_and]
  intro hdeg hsupp
  have : u = 0 := by
    ext i; exact hsupp i (Nat.zero_le _)
  rw [this, map_zero] at hdeg
  omega

theorem MonW_zero_right (w : ℕ) : MonW n w 0 = {0} := by
  ext u
  simp only [mem_MonW, Finset.mem_singleton, Finsupp.degree_eq_zero_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; simp

theorem card_MonW : ∀ (w e : ℕ), w ≤ n + 1 → (MonW n w e).card = (w + e - 1).choose e
  | w, 0, _ => by simp [MonW_zero_right]
  | 0, e + 1, _ => by
      rw [MonW_zero_succ, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega)]
  | w + 1, e + 1, hw => by
      rw [MonW_succ n (by omega), Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _),
        card_shift n (by omega), card_MonW w (e + 1) (by omega), card_MonW (w + 1) e hw,
        show w + 1 + (e + 1) - 1 = (w + e) + 1 by omega, Nat.choose_succ_succ',
        show w + (e + 1) - 1 = w + e by omega, show w + 1 + e - 1 = w + e by omega, add_comm]

theorem card_Mon (e : ℕ) : (Mon n e).card = (n + e).choose n := by
  rw [← MonW_of_le n le_rfl, card_MonW n (n + 1) e le_rfl, show n + 1 + e - 1 = n + e by omega,
    Nat.choose_symm_add]

theorem degree_eq_of_mem_support (K : Type) [Field K] {e : ℕ} {p : MvPolynomial (Fin (n + 1)) K}
    (hp : p.IsHomogeneous e) {m : Fin (n + 1) →₀ ℕ} (hm : m ∈ p.support) : m.degree = e := by
  have h : p ∈ homogeneousSubmodule (Fin (n + 1)) K e := hp
  rw [homogeneousSubmodule_eq_finsupp_supported] at h
  exact h hm

theorem finrank_piece_eq_card (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ)
    (D : Finset (Fin (n + 1) →₀ ℕ)) (hD : ∀ m ∈ D, m.degree = e)
    (hJ : ∀ p : MvPolynomial (Fin (n + 1)) K, p.IsHomogeneous e →
      (p ∈ J ↔ ∀ m ∈ D, coeff m p = 0)) :
    Module.finrank K (piece J e) = D.card := by
  classical
  set V := homogeneousSubmodule (Fin (n + 1)) K e with hV

  let φ : ↥V →ₗ[K] (↥D → K) :=
    { toFun := fun p m => coeff m.1 p.1
      map_add' := fun p q => by ext m; simp
      map_smul' := fun c p => by ext m; simp [coeff_smul] }
  have hφ : ∀ (p : ↥V) (m : ↥D), φ p m = coeff m.1 p.1 := fun _ _ => rfl

  have hker : LinearMap.ker φ = Submodule.comap V.subtype (J.restrictScalars K) := by
    ext p
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.restrictScalars_mem, Submodule.subtype_apply,
      hJ p.1 p.2, funext_iff]
    constructor
    · intro h m hm; exact h ⟨m, hm⟩
    · intro h m; exact h m.1 m.2

  have hsurj : Function.Surjective φ := by
    intro f
    let q : MvPolynomial (Fin (n + 1)) K := ∑ m : ↥D, f m • monomial m.1 (1 : K)
    have hq : q ∈ V :=
      Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (isHomogeneous_monomial _ (hD m.1 m.2))
    refine ⟨⟨q, hq⟩, funext fun m' => ?_⟩
    rw [hφ]
    simp only [q, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single m']
    · simp
    · intro m _ hm
      rw [if_neg]
      exact fun h => hm (Subtype.ext h)
    · intro h; exact absurd (Finset.mem_univ _) h
  have e₁ : piece J e ≃ₗ[K] (↥D → K) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)
  rw [e₁.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

theorem top_eq_of' (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) :
    top d a = k :=
  le_antisymm (Nat.lt_succ_iff.1 (top_lt_of_lt_choose d a (k + 1) h₂)) (le_top_of_choose_le d a k h₁)

theorem macaulayPow_choose (δ : ℕ) :
    Nat.macaulayPow (δ + 1) ((n + (δ + 1)).choose n) = (n + (δ + 2)).choose n := by
  have ha : (n + (δ + 1)).choose n = (n + (δ + 1)).choose (δ + 1) := Nat.choose_symm_add
  have ht : top δ ((n + (δ + 1)).choose n) = n + (δ + 1) := by
    refine top_eq_of' δ _ (n + (δ + 1)) (by rw [ha]) ?_
    rw [ha, Nat.choose_succ_succ' (n + (δ + 1)) δ]
    have : 0 < (n + (δ + 1)).choose δ := Nat.choose_pos (by omega)
    omega
  have hr : rem δ ((n + (δ + 1)).choose n) = 0 := by
    rw [rem, ht, ha, Nat.sub_self]
  rw [macaulayPow_succ, ht, hr, macaulayPow_zero_right, add_zero,
    show n + (δ + 1) + 1 = n + (δ + 2) by omega]
  exact Nat.choose_symm_add.symm

theorem finrank_piece_le (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K (piece J e) ≤ (n + e).choose n := by
  classical
  have h0 : Module.finrank K (piece (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)) e) = (Mon n e).card := by
    refine finrank_piece_eq_card n K ⊥ e (Mon n e) (fun m hm => (mem_Mon n e m).1 hm) fun p hp => ?_
    rw [Ideal.mem_bot]
    constructor
    · rintro rfl m _; exact coeff_zero m
    · intro h
      ext m
      rw [coeff_zero]
      by_cases hm : m ∈ p.support
      · exact h m ((mem_Mon n e m).2 (degree_eq_of_mem_support n K hp hm))
      · exact notMem_support_iff.1 hm
  rw [card_Mon] at h0

  let V := homogeneousSubmodule (Fin (n + 1)) K e
  have hbot : Submodule.comap V.subtype ((⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)).restrictScalars K) = ⊥ := by
    rw [Submodule.restrictScalars_bot, Submodule.comap_bot, Submodule.ker_subtype]
  let e₀ : piece (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)) e ≃ₗ[K] ↥V := Submodule.quotEquivOfEqBot _ hbot
  have hV : Module.finrank K ↥V = (n + e).choose n := by rw [← e₀.finrank_eq, h0]
  haveI : Module.Finite K ↥V :=
    Module.finite_of_finrank_pos (by rw [hV]; exact Nat.choose_pos (by omega))
  rw [← hV]
  exact Submodule.finrank_quotient_le _

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem homogeneousComponent_mem_of_span (K : Type) [Field K] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous d) ∧ J = Ideal.span s) :
    ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  have hhom : (Ideal.span s).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) :=
    Ideal.homogeneous_span _ _ fun p hp => ⟨d, (mem_homogeneousSubmodule d p).2 (hs p hp)⟩
  intro p hp i
  have := hhom i hp
  rwa [← DirectSum.Decomposition.decompose'_eq, MvPolynomial.decomposition.decompose'_apply] at this

end PERSISTSOL
p2m_reactivate "P2MW.S_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow.PERSISTSOL"

open PERSISTSOL in

theorem solution
    (n m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∀ e : ℕ, m ≤ e → Module.finrank K (piece J (e + 1)) = Nat.macaulayPow e (Module.finrank K (piece J e)) := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩

  let g : ℕ → ℕ := fun k => Nat.rec (Module.finrank K (piece J (m' + 1))) (fun k b => Nat.macaulayPow (m' + 1 + k) b) k
  have g_zero : g 0 = Module.finrank K (piece J (m' + 1)) := rfl
  have g_succ : ∀ k, g (k + 1) = Nat.macaulayPow (m' + 1 + k) (g k) := fun k => rfl
  let h : ℕ → ℕ := fun e => g (e - (m' + 1))
  have h_m : h (m' + 1) = Module.finrank K (piece J (m' + 1)) := by
    show g _ = _; rw [Nat.sub_self]; rfl
  have h_succ : ∀ e, m' + 1 ≤ e → h (e + 1) = Nat.macaulayPow e (h e) := by
    intro e he
    show g (e + 1 - (m' + 1)) = Nat.macaulayPow e (g (e - (m' + 1)))
    rw [show e + 1 - (m' + 1) = (e - (m' + 1)) + 1 by omega, g_succ, show m' + 1 + (e - (m' + 1)) = e by omega]

  have g_le : ∀ k, g k ≤ (n + (m' + 1 + k)).choose n := by
    intro k
    induction k with
    | zero => rw [g_zero, add_zero]; exact finrank_piece_le n K J _
    | succ k ih =>
      rw [g_succ]
      refine (macaulayPow_mono _ ih).trans ?_
      rw [show m' + 1 + k = (m' + k) + 1 by omega, macaulayPow_choose,
        show n + (m' + 1 + (k + 1)) = n + (m' + k + 2) by omega]
  have h_le : ∀ e, m' + 1 ≤ e → h e ≤ (n + e).choose n := by
    intro e he
    have := g_le (e - (m' + 1))
    rwa [show m' + 1 + (e - (m' + 1)) = e by omega] at this

  have key := MvPolynomial.finrank_piece_eq_of_maximal_growth n (m' + 1) h
    (fun e he K' _ J' hJ' hfin => by
      rw [h_succ e he, ← hfin]
      exact MvPolynomial.finrank_piece_succ_le_macaulayPow n e (by omega) K' J'
        (homogeneousComponent_mem_of_span n K' e J' hJ'))
    (fun e he => by
      obtain ⟨J', hJ', h1, h2⟩ :=
        MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow n e (by omega)
          (h e) (h_le e he) K
      exact ⟨K, inferInstance, J', hJ', h1, by rw [h2, h_succ e he]⟩)
    K J hJ h_m.symm (by rw [h_succ _ le_rfl, h_m]; exact hmax)
  intro e he
  rw [key (e + 1) (by omega), key e he, h_succ e he]

end S_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
end P2MW
export P2MW.S_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow (solution)
