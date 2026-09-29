-- Prove2me | solution 1 for HarelTarjan.PointerLB.theorem1_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:14:16.849246+00:00
-- url     : https://prove2.me/submissions/654910b3-2ce5-488c-85c7-e1cfa525add1

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine



namespace HarelTarjan.PointerLB

open Finset

section accsec
variable {N : Type*} (ptr : N → Fin 2 → Option N)

def succS (X : Set N) : Set N := {b | ∃ m ∈ X, ∃ i : Fin 2, ptr m i = some b}

lemma acc_succ (j : ℕ) (a : N) : acc ptr (j + 1) a = acc ptr j a ∪ succS ptr (acc ptr j a) := rfl

lemma acc_mono_succ (j : ℕ) (a : N) : acc ptr j a ⊆ acc ptr (j + 1) a := by
  rw [acc_succ]; exact Set.subset_union_left

lemma acc_mono {j j' : ℕ} (h : j ≤ j') (a : N) : acc ptr j a ⊆ acc ptr j' a := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (acc_mono_succ ptr _ a)

lemma succS_mono {X Y : Set N} (h : X ⊆ Y) : succS ptr X ⊆ succS ptr Y := by
  rintro b ⟨m, hm, i, hi⟩; exact ⟨m, h hm, i, hi⟩

lemma acc_succ_sub (j : ℕ) (a : N) : acc ptr (j + 1) a ⊆ {a} ∪ succS ptr (acc ptr j a) := by
  induction j with
  | zero => rw [acc_succ]; rfl
  | succ j ih =>
    rw [acc_succ]
    apply Set.union_subset
    · exact ih.trans (Set.union_subset_union le_rfl (succS_mono ptr (acc_mono_succ ptr j a)))
    · exact Set.subset_union_right

lemma succS_encard (X : Set N) : (succS ptr X).encard ≤ 2 * X.encard := by
  have hsplit : succS ptr X = (⋃ i : Fin 2, {b | ∃ m ∈ X, ptr m i = some b}) := by
    ext b; simp only [succS, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨m, hm, i, hi⟩; exact ⟨i, m, hm, hi⟩
    · rintro ⟨i, m, hm, hi⟩; exact ⟨m, hm, i, hi⟩
  have hi : ∀ i : Fin 2, ({b | ∃ m ∈ X, ptr m i = some b} : Set N).encard ≤ X.encard := by
    intro i
    rw [← (Option.some_injective N).encard_image]
    refine le_trans (Set.encard_le_encard ?_) (Set.encard_image_le (fun m => ptr m i) X)
    rintro _ ⟨b, ⟨m, hm, hb⟩, rfl⟩; exact ⟨m, hm, hb⟩
  rw [hsplit]
  have : (⋃ i : Fin 2, {b | ∃ m ∈ X, ptr m i = some b} : Set N) =
      {b | ∃ m ∈ X, ptr m 0 = some b} ∪ {b | ∃ m ∈ X, ptr m 1 = some b} := by
    ext b; simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, h⟩; fin_cases i
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  rw [this]
  refine (Set.encard_union_le _ _).trans ?_
  rw [two_mul]; exact add_le_add (hi 0) (hi 1)

end accsec

theorem acc_encard_core {N : Type*} (ptr : N → Fin 2 → Option N) (a : N) (j : ℕ) :
    (acc ptr j a).encard + 1 ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => simp [acc]; norm_num
  | succ j ih =>
    have h1 := Set.encard_le_encard (acc_succ_sub ptr j a)
    have h2 := Set.encard_union_le ({a} : Set N) (succS ptr (acc ptr j a))
    have h3 := succS_encard ptr (acc ptr j a)
    rw [Set.encard_singleton] at h2
    calc (acc ptr (j + 1) a).encard + 1 ≤ (1 + 2 * (acc ptr j a).encard) + 1 := by
          gcongr; exact h1.trans (h2.trans (add_le_add le_rfl h3))
      _ = 2 * ((acc ptr j a).encard + 1) := by ring
      _ ≤ 2 * 2 ^ (j + 1) := by gcongr
      _ = 2 ^ (j + 1 + 1) := by ring


lemma lcp_append : ∀ (w u v : List Bool), lcp (w ++ u) (w ++ v) = w ++ lcp u v
  | [], u, v => rfl
  | a :: w, u, v => by
    simp only [List.cons_append]; rw [lcp.eq_1, if_pos rfl, lcp_append w u v]

lemma run_acc {N : Type*} (ptr : N → Fin 2 → Option N) (a b : N) {t : ℕ} {held : List N}
    (hr : Run ptr a b t held) : ∀ n ∈ held, n ∈ acc ptr t a ∨ n ∈ acc ptr t b := by
  induction hr with
  | start =>
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · left; simp [acc]
    · right; simp [acc]
  | @step t held m n i _ hm hptr ih =>
    intro x hx
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rcases ih m hm with h | h
      · left; rw [acc_succ]; exact Or.inr ⟨m, h, i, hptr⟩
      · right; rw [acc_succ]; exact Or.inr ⟨m, h, i, hptr⟩
    · rcases ih x hx with h | h
      · left; exact acc_mono_succ ptr t a h
      · right; exact acc_mono_succ ptr t b h

lemma answered_acc {N : Type*} (ptr : N → Fin 2 → Option N) (a b target : N) (k : ℕ)
    (h : AnsweredIn ptr a b target k) : target ∈ acc ptr k a ∨ target ∈ acc ptr k b := by
  obtain ⟨t, htk, held, hr, hmem⟩ := h
  rcases run_acc ptr a b hr target hmem with h | h
  · left; exact acc_mono ptr htk a h
  · right; exact acc_mono ptr htk b h

/-- leaves below the prefix `p` -/
def Lset (h : ℕ) (p : List Bool) : Set (Vertex h) := {x | IsLeaf x ∧ p <+: x.1}

lemma Lset_encard (h : ℕ) (p : List Bool) (r : ℕ) (hpr : p.length + r = h) :
    (Lset h p).encard = 2 ^ r := by
  have heq : Lset h p = (fun s : List.Vector Bool r => (⟨p ++ s.1, by
      rw [List.length_append, s.2]; omega⟩ : Vertex h)) '' Set.univ := by
    ext x
    simp only [Lset, IsLeaf, Set.mem_setOf_eq, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · rintro ⟨hl, s, hs⟩
      refine ⟨⟨s, ?_⟩, Subtype.ext hs⟩
      have := congrArg List.length hs; rw [List.length_append] at this; omega
    · rintro ⟨s, rfl⟩
      refine ⟨?_, s.1, rfl⟩
      simp only [List.length_append, s.2]; omega
  rw [heq, Function.Injective.encard_image]
  · rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]; simp
  · intro s s' hss
    have := congrArg (fun v : Vertex h => v.1) hss
    simp only [List.append_cancel_left_eq] at this
    exact Subtype.ext this

theorem half_core {N : Type*} {h k : ℕ} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hk : AnswersLeafQueriesIn ptr rep k)
    (w : Vertex h) (i : ℕ) (hi : 1 ≤ i) (hwi : w.1.length + i = h) :
    (2 ^ (i - 1) : ℕ∞) ≤
      {x : Vertex h | IsLeaf x ∧ IsAncestor w x ∧ w ∈ A ptr rep k x}.encard := by
  set L := Lset h (w.1 ++ [false])
  set R := Lset h (w.1 ++ [true])
  have hL : L.encard = 2 ^ (i - 1) := Lset_encard h _ (i - 1) (by simp; omega)
  have hR : R.encard = 2 ^ (i - 1) := Lset_encard h _ (i - 1) (by simp; omega)
  have hnca : ∀ x ∈ L, ∀ y ∈ R, nca x y = w := by
    rintro x ⟨_, s, hs⟩ y ⟨_, s', hs'⟩
    apply Subtype.ext
    simp only [nca]
    rw [← hs, ← hs', List.append_assoc, List.append_assoc, lcp_append]
    simp [lcp]
  have hanc : ∀ b : Bool, ∀ x ∈ Lset h (w.1 ++ [b]), IsAncestor w x := by
    rintro b x ⟨_, s, hs⟩
    exact ⟨[b] ++ s, by rw [← List.append_assoc, hs]⟩
  by_cases hall : ∀ x ∈ L, w ∈ A ptr rep k x
  · rw [← hL]
    apply Set.encard_le_encard
    intro x hx
    exact ⟨hx.1, hanc false x hx, hall x hx⟩
  · push_neg at hall
    obtain ⟨x0, hx0, hnot⟩ := hall
    rw [← hR]
    apply Set.encard_le_encard
    intro y hy
    refine ⟨hy.1, hanc true y hy, ?_⟩
    have hq := answered_acc ptr _ _ _ k (hk x0 y hx0.1 hy.1)
    rw [hnca x0 hx0 y hy] at hq
    rcases hq with hq | hq
    · exact absurd hq hnot
    · exact hq


def pre {h : ℕ} (x : Vertex h) (d : ℕ) : Vertex h :=
  ⟨x.1.take d, by rw [List.length_take]; exact (min_le_right _ _).trans x.2⟩

lemma pre_length {h : ℕ} (x : Vertex h) (hx : IsLeaf x) {d : ℕ} (hd : d ≤ h) :
    (pre x d).1.length = d := by
  simp only [pre, List.length_take]; unfold IsLeaf at hx; omega

lemma ancestor_iff {h : ℕ} (x w : Vertex h) {d : ℕ} (hw : w.1.length = d) :
    IsAncestor w x ↔ pre x d = w := by
  unfold IsAncestor
  rw [List.prefix_iff_eq_take, hw]
  constructor
  · intro h1; exact Subtype.ext h1.symm
  · intro h1; rw [← h1]; rfl

lemma mem_leaves {h : ℕ} (x : Vertex h) : x ∈ leaves h ↔ IsLeaf x := by
  unfold leaves IsLeaf
  simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨v, rfl⟩; exact v.2
  · intro hx; exact ⟨⟨x.1, hx⟩, rfl⟩

def Dset (h d : ℕ) (hd : d ≤ h) : Finset (Vertex h) :=
  (univ : Finset (List.Vector Bool d)).map
    ⟨fun v : List.Vector Bool d => (⟨v.1, by rw [v.2]; exact hd⟩ : Vertex h),
      fun _ _ hab => Subtype.ext (congrArg (fun v : Vertex h => v.1) hab)⟩

lemma card_Dset (h d : ℕ) (hd : d ≤ h) : (Dset h d hd).card = 2 ^ d := by
  simp [Dset, card_vector]

lemma mem_Dset {h d : ℕ} (hd : d ≤ h) (w : Vertex h) : w ∈ Dset h d hd ↔ w.1.length = d := by
  unfold Dset
  simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨v, rfl⟩; exact v.2
  · intro hw; exact ⟨(⟨w.1, hw⟩ : List.Vector Bool d), rfl⟩

theorem sum_core {N : Type*} {h k : ℕ} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hk : AnswersLeafQueriesIn ptr rep k) :
    (h : ℕ∞) * 2 ^ h ≤ 2 * ∑ x ∈ leaves h, (A ptr rep k x).encard := by
  classical
  -- step A
  have hA : ∀ x ∈ leaves h, (∑ i ∈ Icc 1 h, if pre x (h - i) ∈ A ptr rep k x then (1 : ℕ∞) else 0)
      ≤ (A ptr rep k x).encard := by
    intro x hx
    rw [mem_leaves] at hx
    rw [sum_boole]
    set F := (Icc 1 h).filter (fun i => pre x (h - i) ∈ A ptr rep k x)
    rw [← Set.encard_coe_eq_coe_finsetCard]
    apply Set.encard_le_encard_of_injOn (f := fun i => pre x (h - i))
    · intro i hi; simp only [F, coe_filter, Set.mem_setOf_eq] at hi; exact hi.2
    · intro i hi j hj hij
      simp only [F, coe_filter, mem_Icc, Set.mem_setOf_eq] at hi hj
      have := congrArg (fun v : Vertex h => v.1.length) hij
      simp only at this
      rw [pre_length x hx (by omega), pre_length x hx (by omega)] at this
      omega
  -- step C
  have hC : ∀ i ∈ Icc 1 h, (2 ^ (h - 1) : ℕ∞) ≤
      ∑ x ∈ leaves h, if pre x (h - i) ∈ A ptr rep k x then (1 : ℕ∞) else 0 := by
    intro i hi
    rw [mem_Icc] at hi
    rw [sum_boole]
    rw [card_eq_sum_card_fiberwise (f := fun x => pre x (h - i)) (t := Dset h (h - i) (by omega))
      (by
        intro x hx
        simp only [coe_filter, Set.mem_setOf_eq] at hx
        rw [mem_coe, mem_Dset]
        exact pre_length x ((mem_leaves x).1 hx.1) (by omega))]
    push_cast
    have hfib : ∀ w ∈ Dset h (h - i) (by omega), (2 ^ (i - 1) : ℕ∞) ≤
        ((((leaves h).filter (fun x => pre x (h - i) ∈ A ptr rep k x)).filter
          (fun x => pre x (h - i) = w)).card : ℕ∞) := by
      intro w hw
      rw [mem_Dset] at hw
      have hset : ({x : Vertex h | IsLeaf x ∧ IsAncestor w x ∧ w ∈ A ptr rep k x} : Set (Vertex h)) =
          ↑(((leaves h).filter (fun x => pre x (h - i) ∈ A ptr rep k x)).filter
            (fun x => pre x (h - i) = w)) := by
        ext x
        simp only [Set.mem_setOf_eq, coe_filter, mem_filter, mem_leaves]
        rw [ancestor_iff x w hw]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by rw [h2]; exact h3⟩, h2⟩
        · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2, by rw [← h2]; exact h3⟩
      rw [← Set.encard_coe_eq_coe_finsetCard, ← hset]
      exact half_core ptr rep hk w i hi.1 (by omega)
    refine le_trans ?_ (sum_le_sum hfib)
    rw [sum_const, card_Dset, nsmul_eq_mul]
    push_cast
    rw [← pow_add, show h - i + (i - 1) = h - 1 by omega]
  -- combine
  have hB : ∑ i ∈ Icc 1 h, (2 ^ (h - 1) : ℕ∞) ≤ ∑ x ∈ leaves h, (A ptr rep k x).encard := by
    refine le_trans (sum_le_sum hC) ?_
    rw [sum_comm]
    exact sum_le_sum hA
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul] at hB
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · subst h0; simp
  · calc (h : ℕ∞) * 2 ^ h = 2 * ((((h + 1 - 1 : ℕ)) : ℕ∞) * 2 ^ (h - 1)) := by
          rw [show h + 1 - 1 = h by omega]
          rw [show (2 : ℕ∞) ^ h = 2 * 2 ^ (h - 1) by
            rw [← pow_succ']; congr 1; omega]
          ring
      _ ≤ 2 * ∑ x ∈ leaves h, (A ptr rep k x).encard := by gcongr


lemma card_leaves (h : ℕ) : (leaves h).card = 2 ^ h := by
  simp [leaves, card_vector]

theorem thm1_core (h k : ℕ) {N : Type*} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hrep : Function.Injective rep)
    (hk : AnswersLeafQueriesIn ptr rep k) :
    Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ h)) - 2 < (k : ℝ) := by
  have hS := sum_core ptr rep hk
  have he : ∀ x, (A ptr rep k x).encard + 1 ≤ 2 ^ (k + 1) := by
    intro x
    have h1 : (A ptr rep k x).encard ≤ (acc ptr k (rep x)).encard := by
      rw [← hrep.encard_image]
      apply Set.encard_le_encard
      rintro _ ⟨t, ht, rfl⟩; exact ht
    exact le_trans (add_le_add h1 le_rfl) (acc_encard_core ptr (rep x) k)
  have hsum : ∑ x ∈ leaves h, ((A ptr rep k x).encard + 1) ≤ 2 ^ h * 2 ^ (k + 1) := by
    refine le_trans (sum_le_sum (fun x _ => he x)) ?_
    rw [sum_const, card_leaves, nsmul_eq_mul]; push_cast; rfl
  rw [sum_add_distrib, sum_const, card_leaves, nsmul_eq_mul, mul_one] at hsum
  have hmain : (((h + 2) * 2 ^ h : ℕ) : ℕ∞) ≤ ((2 ^ h * 2 ^ (k + 2) : ℕ) : ℕ∞) := by
    push_cast
    calc ((h : ℕ∞) + 2) * 2 ^ h = (h : ℕ∞) * 2 ^ h + 2 * 2 ^ h := by ring
      _ ≤ 2 * ∑ x ∈ leaves h, (A ptr rep k x).encard + 2 * 2 ^ h := by gcongr
      _ = 2 * (∑ x ∈ leaves h, (A ptr rep k x).encard + 2 ^ h) := by ring
      _ ≤ 2 * (2 ^ h * 2 ^ (k + 1)) := by
          gcongr; push_cast at hsum; exact hsum
      _ = 2 ^ h * 2 ^ (k + 2) := by ring
  have hnat : (h + 2) * 2 ^ h ≤ 2 ^ h * 2 ^ (k + 2) := by exact_mod_cast hmain
  have hlt : h < 2 ^ (k + 2) := by
    rw [mul_comm] at hnat
    have := Nat.le_of_mul_le_mul_left hnat (by positivity)
    omega
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · subst h0; simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  · have hlog : Real.logb 2 (h : ℝ) < (k : ℝ) + 2 := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast hpos)]
      rw [show ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      exact_mod_cast hlt
    linarith

end HarelTarjan.PointerLB

open HarelTarjan.PointerLB

theorem solution (h k : ℕ) {N : Type*} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hrep : Function.Injective rep)
    (hk : AnswersLeafQueriesIn ptr rep k) :
    Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ h)) - 2 < (k : ℝ) := by
  exact thm1_core h k ptr rep hrep hk
