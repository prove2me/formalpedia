-- Prove2me | solution 1 for MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e5df3eed-41cb-5649-932d-ddf6036185da

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow

set_option autoImplicit false

namespace LexGrowth

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

theorem degree_sub_single (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hu : 1 ≤ u i) :
    (u - Finsupp.single i 1).degree + 1 = u.degree := by
  conv_rhs => rw [← Finsupp.sub_add_single_one_cancel (u := u) (i := i) (by omega)]
  rw [map_add, Finsupp.degree_single]

theorem exists_one_le_of_degree_ne_zero (u : Fin (n + 1) →₀ ℕ) (hu : u.degree ≠ 0) :
    ∃ i, 1 ≤ u i := by
  rw [Finsupp.degree_eq_sum] at hu
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  exact ⟨i, by omega⟩

theorem exists_sub_single_pos (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hi : 1 ≤ u i)
    (hdeg : 2 ≤ u.degree) : ∃ i', 1 ≤ u i' ∧ 1 ≤ (u - Finsupp.single i' 1 : Fin (n + 1) →₀ ℕ) i := by
  by_cases h2 : 2 ≤ u i
  · refine ⟨i, hi, ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
  · have hui : u i = 1 := by omega
    have hsum : u i + ∑ k ∈ Finset.univ.erase i, u k = u.degree := by
      rw [Finsupp.degree_eq_sum]; exact Finset.add_sum_erase _ _ (Finset.mem_univ i)
    have hne : ∑ k ∈ Finset.univ.erase i, u k ≠ 0 := by omega
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    refine ⟨k, by omega, ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hki]; omega

noncomputable def BW : ℕ → ℕ → Finset (Fin (n + 1) →₀ ℕ)
  | 0, a => if a = 0 then ∅ else {0}
  | δ + 1, a => MonW n (top δ a - δ) (δ + 1) ∪ shift n (top δ a - δ) (BW δ (rem δ a))

theorem BW_succ (δ a : ℕ) :
    BW n (δ + 1) a = MonW n (top δ a - δ) (δ + 1) ∪ shift n (top δ a - δ) (BW n δ (rem δ a)) := rfl

theorem BW_zero_right : ∀ d : ℕ, BW n d 0 = ∅
  | 0 => by simp [BW]
  | δ + 1 => by
      rw [BW_succ, top_zero_right, rem_zero_right, BW_zero_right δ, Nat.sub_self, MonW_zero_succ,
        shift_empty, Finset.empty_union]

theorem card_MonW_succ_eq (w δ : ℕ) (hw : w ≤ n + 1) :
    (MonW n w (δ + 1)).card = (w + δ).choose (δ + 1) := by
  rw [card_MonW n w (δ + 1) hw, show w + (δ + 1) - 1 = w + δ by omega]

theorem top_sub_add (δ a : ℕ) : top δ a - δ + δ = top δ a := Nat.sub_add_cancel (d_le_top δ a)

theorem top_le_of_le (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) : top δ a ≤ w + δ := by
  by_contra h
  push Not at h
  have h1 : (w + δ + 1).choose (δ + 1) ≤ (top δ a).choose (δ + 1) := Nat.choose_le_choose _ h
  have h2 := choose_top_le δ a
  rw [Nat.choose_succ_succ'] at h1
  have h3 : 1 ≤ (w + δ).choose δ := Nat.choose_pos (by omega)
  omega

theorem j_le (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) : top δ a - δ ≤ w := by
  have := top_le_of_le w δ a ha; omega

theorem j_lt_of_rem_ne_zero (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) (hr : rem δ a ≠ 0) :
    top δ a - δ < w := by
  have hj := j_le w δ a ha
  rcases hj.lt_or_eq with h | h
  · exact h
  · exfalso
    have htop : top δ a = w + δ := by have := d_le_top δ a; omega
    have := rem_add_choose δ a
    rw [htop] at this
    omega

theorem rem_le_card (δ a : ℕ) (hj : top δ a - δ + 1 ≤ n + 1) :
    rem δ a ≤ (MonW n (top δ a - δ + 1) δ).card := by
  rw [card_MonW n _ _ hj, show top δ a - δ + 1 + δ - 1 = top δ a by have := d_le_top δ a; omega]
  exact (rem_lt δ a).le

theorem BW_subset : ∀ (d w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w d).card → BW n d a ⊆ MonW n w d
  | 0, w, a, hw, ha => by
      simp only [BW]
      split_ifs
      · exact Finset.empty_subset _
      · rw [MonW_zero_right]
  | δ + 1, w, a, hw, ha => by
      rw [card_MonW_succ_eq n w δ hw] at ha
      rw [BW_succ]
      have hj := j_le w δ a ha
      refine Finset.union_subset (MonW_mono n hj _) ?_
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty]; exact Finset.empty_subset _
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        have ih := BW_subset δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)
        refine (shift_mono n _ ih).trans ?_
        refine subset_trans ?_ (MonW_mono n (show top δ a - δ + 1 ≤ w by omega) (δ + 1))
        rw [MonW_succ n (show top δ a - δ < n + 1 by omega) δ]
        exact Finset.subset_union_right

theorem card_BW : ∀ (d w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w d).card → (BW n d a).card = a
  | 0, w, a, hw, ha => by
      rw [MonW_zero_right, Finset.card_singleton] at ha
      simp only [BW]
      split_ifs with h
      · simp [h]
      · simp; omega
  | δ + 1, w, a, hw, ha => by
      rw [card_MonW_succ_eq n w δ hw] at ha
      rw [BW_succ, Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _)]
      have hj := j_le w δ a ha
      rw [card_MonW_succ_eq n _ δ (hj.trans hw), top_sub_add]
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty, Finset.card_empty]
        have := rem_add_choose δ a; omega
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        rw [card_shift n (by omega), card_BW δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)]
        have := rem_add_choose δ a; omega

noncomputable def Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  (MonW n w (e + 1)).filter (fun u => ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B)

theorem mem_Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ Bplus n w e B ↔
      u ∈ MonW n w (e + 1) ∧ ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B := by
  simp [Bplus]

theorem Bplus_empty (w e : ℕ) : Bplus n w e (∅ : Finset (Fin (n + 1) →₀ ℕ)) = ∅ := by
  ext u
  simp only [mem_Bplus, Finset.notMem_empty, imp_false, not_le, Nat.lt_one_iff, iff_false, not_and,
    not_forall]
  intro hu
  rw [mem_MonW] at hu
  obtain ⟨i, hi⟩ := exists_one_le_of_degree_ne_zero n u (by omega)
  exact ⟨i, by omega⟩

theorem Bplus_MonW (w j δ : ℕ) (hjw : j ≤ w) :
    Bplus n w (δ + 1) (MonW n j (δ + 1)) = MonW n j (δ + 2) := by
  ext u
  rw [mem_Bplus, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨⟨hdeg, hsupp⟩, hdiv⟩
    refine ⟨hdeg, fun i hi => ?_⟩
    by_contra hui
    obtain ⟨i', hi', h1⟩ := exists_sub_single_pos n u i (by omega) (by omega)
    have := ((mem_MonW n _ _ _).1 (hdiv i' hi')).2 i hi
    omega
  · rintro ⟨hdeg, hsupp⟩
    refine ⟨⟨hdeg, fun i hi => hsupp i (hjw.trans hi)⟩, fun i hi => ?_⟩
    rw [mem_MonW]
    refine ⟨by have := degree_sub_single n u i hi; omega, fun k hk => ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp k hk, Nat.zero_sub]

theorem Bplus_union_shift (w j δ : ℕ) (hj : j < n + 1) (hjw : j + 1 ≤ w)
    (B' : Finset (Fin (n + 1) →₀ ℕ)) (hB' : B' ⊆ MonW n (j + 1) δ) :
    Bplus n w (δ + 1) (MonW n j (δ + 1) ∪ shift n j B') =
      MonW n j (δ + 2) ∪ shift n j (Bplus n (j + 1) δ B') := by

  have hB : MonW n j (δ + 1) ∪ shift n j B' ⊆ MonW n (j + 1) (δ + 1) := by
    refine Finset.union_subset (MonW_mono n (Nat.le_succ j) _) ?_
    rw [MonW_succ n hj δ]
    exact (shift_mono n j hB').trans Finset.subset_union_right
  have hvar : var n j hj = Finsupp.single ⟨j, hj⟩ 1 := rfl
  ext u
  rw [mem_Bplus, Finset.mem_union, mem_shift_iff n hj, mem_Bplus, mem_MonW, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨⟨hdeg, hsupp⟩, hdiv⟩

    have hsupp' : ∀ i : Fin (n + 1), j < (i : ℕ) → u i = 0 := by
      intro i hi
      by_contra hui
      obtain ⟨i', hi', h1⟩ := exists_sub_single_pos n u i (by omega) (by omega)
      have := ((mem_MonW n _ _ _).1 (hB (hdiv i' hi'))).2 i (by omega)
      omega
    by_cases huj : u ⟨j, hj⟩ = 0
    · refine Or.inl ⟨hdeg, fun i hi => ?_⟩
      rcases hi.eq_or_lt with hij | hij
      · have : i = ⟨j, hj⟩ := Fin.ext hij.symm
        rw [this]; exact huj
      · exact hsupp' i hij
    · refine Or.inr ⟨by omega, ⟨?_, fun i hi => ?_⟩, fun l hl => ?_⟩
      · have := degree_sub_var n hj u (by omega); omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp' i (by omega), Nat.zero_sub]
      ·
        have hul : 1 ≤ u l := by
          have : (u - var n j hj) l ≤ u l := by
            simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
          omega
        have hv := hdiv l hul
        rw [Finset.mem_union, mem_shift_iff n hj] at hv
        rcases hv with hv | ⟨-, hv⟩
        · exfalso
          have h0 := ((mem_MonW n _ _ _).1 hv).2 ⟨j, hj⟩ le_rfl
          by_cases hlj : l = ⟨j, hj⟩
          · subst hlj
            simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same, var] at h0 hl
            omega
          · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hlj] at h0
            omega
        · have : u - var n j hj - Finsupp.single l 1 = u - Finsupp.single l 1 - var n j hj := by
            ext k
            simp only [Finsupp.coe_tsub, Pi.sub_apply]
            omega
          rw [this]; exact hv
  · rintro (⟨hdeg, hsupp⟩ | ⟨h1, ⟨hdeg, hsupp⟩, hdiv⟩)
    ·
      refine ⟨⟨hdeg, fun i hi => hsupp i (by omega)⟩, fun i hi => ?_⟩
      refine Finset.mem_union_left _ ((mem_MonW n _ _ _).2 ⟨?_, fun k hk => ?_⟩)
      · have := degree_sub_single n u i hi; omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp k hk, Nat.zero_sub]
    ·
      have hu : u - var n j hj + var n j hj = u := sub_var_add_var n hj u h1
      refine ⟨⟨?_, fun i hi => ?_⟩, fun i hi => ?_⟩
      · have := degree_sub_var n hj u h1; omega
      · have h0 := hsupp i (by omega)
        simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply] at h0
        have hij : (i : ℕ) ≠ j := by omega
        simp only [hij, if_false] at h0
        omega
      · rw [Finset.mem_union, mem_shift_iff n hj]
        by_cases hij : i = ⟨j, hj⟩
        ·
          subst hij
          rw [← hvar]
          by_cases hujj : (u - var n j hj) ⟨j, hj⟩ = 0
          · left
            rw [mem_MonW]
            refine ⟨hdeg, fun k hk => ?_⟩
            rcases hk.eq_or_lt with hkj | hkj
            · have : k = ⟨j, hj⟩ := Fin.ext hkj.symm
              rw [this]; exact hujj
            · exact hsupp k hkj
          · right
            have := hdiv ⟨j, hj⟩ (by omega)
            rw [← hvar] at this
            refine ⟨?_, this⟩
            simp only [Finsupp.coe_tsub, Pi.sub_apply] at hujj ⊢
            omega
        · right
          have hii : 1 ≤ (u - var n j hj) i := by
            simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply]
            have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
            simp only [this, if_false]; omega
          have hv := hdiv i hii
          refine ⟨?_, ?_⟩
          · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hij]; omega
          · have : u - Finsupp.single i 1 - var n j hj = u - var n j hj - Finsupp.single i 1 := by
              ext k
              simp only [Finsupp.coe_tsub, Pi.sub_apply]
              omega
            rw [this]; exact hv

theorem card_Bplus_BW : ∀ (δ w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w (δ + 1)).card →
    (Bplus n w (δ + 1) (BW n (δ + 1) a)).card = Nat.macaulayPow (δ + 1) a := by
  intro δ
  induction δ with
  | zero =>
      intro w a hw ha
      rw [card_MonW_succ_eq n w 0 hw] at ha
      have hj := j_le w 0 a ha
      rw [BW_succ, rem_zero_left, BW_zero_right, shift_empty, Finset.union_empty,
        Bplus_MonW n w _ 0 hj, card_MonW n _ _ (hj.trans hw), macaulayPow_succ, macaulayPow_zero,
        Nat.sub_zero, show top 0 a + (0 + 2) - 1 = top 0 a + 1 by omega]
      simp
  | succ δ' ih =>
      intro w a hw ha
      set δ := δ' + 1 with hδ
      rw [card_MonW_succ_eq n w δ hw] at ha
      have hj := j_le w δ a ha
      rw [BW_succ, macaulayPow_succ]
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty, Finset.union_empty, Bplus_MonW n w _ δ hj,
          card_MonW n _ _ (hj.trans hw), macaulayPow_zero_right,
          show top δ a - δ + (δ + 2) - 1 = top δ a + 1 by have := d_le_top δ a; omega]
        simp
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hjn : top δ a - δ < n + 1 := by omega
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        have hB' := BW_subset n δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)
        rw [Bplus_union_shift n w _ δ hjn (by omega) _ hB',
          Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _), card_shift n hjn,
          card_MonW n _ _ (hj.trans hw),
          show top δ a - δ + (δ + 2) - 1 = top δ a + 1 by have := d_le_top δ a; omega,
          ih (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)]

theorem eq_of_le_of_degree_eq (g m : Fin (n + 1) →₀ ℕ) (h : g ≤ m) (hd : g.degree = m.degree) :
    g = m := by
  have h1 : g + (m - g) = m := add_tsub_cancel_of_le h
  have h2 : (m - g).degree = 0 := by
    have := congrArg Finsupp.degree h1
    rw [map_add] at this; omega
  rw [Finsupp.degree_eq_zero_iff] at h2
  rw [h2, add_zero] at h1
  exact h1

theorem exists_eq_sub_single (g u : Fin (n + 1) →₀ ℕ) (h : g ≤ u) (hd : g.degree + 1 = u.degree) :
    ∃ i, 1 ≤ u i ∧ g = u - Finsupp.single i 1 := by
  have h1 : g + (u - g) = u := add_tsub_cancel_of_le h
  have h2 : (u - g).degree = 1 := by
    have := congrArg Finsupp.degree h1
    rw [map_add] at this; omega
  obtain ⟨i, hi⟩ := exists_one_le_of_degree_ne_zero n (u - g) (by omega)
  have h3 : (u - g - Finsupp.single i 1).degree = 0 := by
    have := degree_sub_single n (u - g) i hi; omega
  rw [Finsupp.degree_eq_zero_iff] at h3
  have h4 : u - g = Finsupp.single i 1 := by
    have := Finsupp.sub_add_single_one_cancel (u := u - g) (i := i) (by omega)
    rw [h3, zero_add] at this
    exact this.symm
  refine ⟨i, ?_, ?_⟩
  · have : (u - g) i ≤ u i := by simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
    omega
  · rw [← h4]

    exact (tsub_tsub_cancel_of_le h).symm

open MvPolynomial AlgebraicGeometry.HilbertFunctor

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

theorem exists_ideal (δ a : ℕ) (ha : a ≤ (n + (δ + 1)).choose n) (K : Type) [Field K] :
    ∃ J : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous (δ + 1)) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J (δ + 1)) = a ∧
      Module.finrank K (piece J (δ + 1 + 1)) = Nat.macaulayPow (δ + 1) a := by
  classical

  have hcardMon : (MonW n (n + 1) (δ + 1)).card = (n + (δ + 1)).choose n := by
    rw [MonW_of_le n le_rfl, card_Mon]
  have ha' : a ≤ (MonW n (n + 1) (δ + 1)).card := hcardMon ▸ ha
  set B := BW n (δ + 1) a with hBdef
  have hB : B ⊆ MonW n (n + 1) (δ + 1) := BW_subset n (δ + 1) (n + 1) a le_rfl ha'
  have hBcard : B.card = a := card_BW n (δ + 1) (n + 1) a le_rfl ha'
  have hBplus : (Bplus n (n + 1) (δ + 1) B).card = Nat.macaulayPow (δ + 1) a :=
    card_Bplus_BW n δ (n + 1) a le_rfl ha'
  have hmemB : ∀ m ∈ B, m.degree = δ + 1 := fun m hm => ((mem_MonW n _ _ _).1 (hB hm)).1
  set G : Finset (Fin (n + 1) →₀ ℕ) := Mon n (δ + 1) \ B with hGdef
  have hmemG : ∀ m : Fin (n + 1) →₀ ℕ, m ∈ G ↔ m.degree = δ + 1 ∧ m ∉ B := fun m => by
    simp [hGdef, Finset.mem_sdiff]
  set s : Set (MvPolynomial (Fin (n + 1)) K) := (fun m => monomial m (1 : K)) '' (↑G : Set _) with hsdef
  refine ⟨Ideal.span s, ⟨s, ?_, rfl⟩, ?_, ?_⟩
  ·
    rintro p ⟨m, hm, rfl⟩
    exact isHomogeneous_monomial _ ((hmemG m).1 hm).1
  ·
    rw [← hBcard]
    refine finrank_piece_eq_card n K _ _ B hmemB fun p hp => ?_
    rw [hsdef, mem_ideal_span_monomial_image]
    constructor
    · intro h m hmB
      by_contra hc
      obtain ⟨g, hg, hgm⟩ := h m (by simpa [mem_support_iff] using hc)
      have hg' := (hmemG g).1 hg
      have : g = m := eq_of_le_of_degree_eq n g m hgm (by rw [hg'.1, hmemB m hmB])
      exact hg'.2 (this ▸ hmB)
    · intro h m hm
      refine ⟨m, (hmemG m).2 ⟨degree_eq_of_mem_support n K hp hm, fun hmB => ?_⟩, le_rfl⟩
      exact (mem_support_iff.1 hm) (h m hmB)
  ·
    rw [← hBplus]
    refine finrank_piece_eq_card n K _ _ (Bplus n (n + 1) (δ + 1) B) (fun u hu => ?_) fun p hp => ?_
    · exact ((mem_MonW n _ _ _).1 ((mem_Bplus n _ _ _ _).1 hu).1).1
    · rw [hsdef, mem_ideal_span_monomial_image]
      constructor
      · intro h u hu
        by_contra hc
        obtain ⟨g, hg, hgu⟩ := h u (by simpa [mem_support_iff] using hc)
        have hg' := (hmemG g).1 hg
        have hu' := (mem_Bplus n _ _ _ _).1 hu
        have hdeg : g.degree + 1 = u.degree := by
          rw [hg'.1, ((mem_MonW n _ _ _).1 hu'.1).1]
        obtain ⟨i, hi, rfl⟩ := exists_eq_sub_single n g u hgu hdeg
        exact hg'.2 (hu'.2 i hi)
      · intro h u hu
        have hdeg : u.degree = δ + 1 + 1 := degree_eq_of_mem_support n K hp hu

        have hnot : u ∉ Bplus n (n + 1) (δ + 1) B := fun hb => (mem_support_iff.1 hu) (h u hb)
        rw [mem_Bplus, mem_MonW] at hnot
        simp only [not_and, not_forall] at hnot
        obtain ⟨i, hi, hiB⟩ := hnot ⟨hdeg, fun i hi => absurd (lt_of_lt_of_le i.2 hi) (lt_irrefl _)⟩
        refine ⟨u - Finsupp.single i 1, (hmemG _).2 ⟨?_, hiB⟩, tsub_le_self⟩
        have := degree_sub_single n u i hi; omega

end LexGrowth
p2m_reactivate "P2MW.S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow.LexGrowth"

open LexGrowth AlgebraicGeometry.HilbertFunctor in
theorem solution
    (n d : ℕ) (hd : 1 ≤ d) (a : ℕ) (ha : a ≤ (n + d).choose n) (K : Type) [Field K] :
    ∃ J : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous d) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J d) = a ∧ Module.finrank K (piece J (d + 1)) = Nat.macaulayPow d a := by
  obtain ⟨δ, rfl⟩ : ∃ δ, d = δ + 1 := ⟨d - 1, by omega⟩
  exact exists_ideal n δ a ha K

end S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
end P2MW
export P2MW.S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow (solution)
