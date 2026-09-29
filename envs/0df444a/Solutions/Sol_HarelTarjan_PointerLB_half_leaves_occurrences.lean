-- Prove2me | solution 1 for HarelTarjan.PointerLB.half_leaves_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:10:54.869681+00:00
-- url     : https://prove2.me/submissions/c6ab18db-05a1-47e6-91ce-9e1c2e42bec6

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

end HarelTarjan.PointerLB

open HarelTarjan.PointerLB

theorem solution {N : Type*} {h k : ℕ} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hk : AnswersLeafQueriesIn ptr rep k)
    (w : Vertex h) (i : ℕ) (hi : 1 ≤ i) (hwi : w.1.length + i = h) :
    (2 ^ (i - 1) : ℕ∞) ≤
      {x : Vertex h | IsLeaf x ∧ IsAncestor w x ∧ w ∈ A ptr rep k x}.encard := by
  exact half_core ptr rep hk w i hi hwi
