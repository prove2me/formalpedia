-- Prove2me | solution 1 for HarelTarjan.SymOrder.lemma2_descendants_range
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T09:06:51.203479+00:00
-- url     : https://prove2.me/submissions/26a1f3bf-b6ba-4683-8542-2aebb24c4724

/- Portions of the auxiliary development are adapted from the public Prove2Me
submission by mrfancypants, daef8fa4-1e8b-4109-b277-aa01e430c9ef (2026-09-29).
Source: https://prove2.me/api/v1/submissions/daef8fa4-1e8b-4109-b277-aa01e430c9ef/solution
Reused under the platform's Apache-2.0 public-contribution terms.
The final milestone statement and its packaging below are new. -/

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym
import Definitions.Def_HarelTarjan_SymOrder_Algorithms

namespace HarelTarjan.SymOrder

/-- Explicit symmetric-order number of a path in the complete binary tree of depth `d`. -/
def aux_nca_F : ℕ → List Bool → ℕ
  | d, [] => 2 ^ d
  | 0, _ :: _ => 0
  | d + 1, b :: t => (if b then 2 ^ (d + 1) else 0) + aux_nca_F d t

theorem aux_nca_F_nil (d : ℕ) : aux_nca_F d [] = 2 ^ d := by
  cases d <;> rfl

theorem aux_nca_F_cons (d : ℕ) (b : Bool) (t : List Bool) :
    aux_nca_F (d + 1) (b :: t) = (if b then 2 ^ (d + 1) else 0) + aux_nca_F d t := rfl

theorem aux_nca_bounds : ∀ (s : List Bool) (d : ℕ), s.length ≤ d →
    2 ^ (d - s.length) ≤ aux_nca_F d s ∧ aux_nca_F d s + 2 ^ (d - s.length) ≤ 2 ^ (d + 1)
  | [], d, _ => by
    simp only [aux_nca_F_nil, List.length_nil, Nat.sub_zero, pow_succ]; omega
  | b :: t, 0, h => by simp at h
  | b :: t, d + 1, h => by
    simp only [List.length_cons] at h
    have ih := aux_nca_bounds t d (by omega)
    rw [aux_nca_F_cons]
    simp only [List.length_cons, Nat.add_sub_add_right]
    have : (2:ℕ) ^ (d + 1 + 1) = 2 ^ (d + 1) + 2 ^ (d + 1) := by rw [pow_succ]; ring
    have hP : 0 < 2 ^ d := by positivity
    cases b <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega

theorem aux_nca_interval : ∀ (s t : List Bool) (d : ℕ), s.length ≤ d → t.length ≤ d →
    (s <+: t ↔ (aux_nca_F d s + 1 ≤ aux_nca_F d t + 2 ^ (d - s.length) ∧
      aux_nca_F d t + 1 ≤ aux_nca_F d s + 2 ^ (d - s.length)))
  | [], t, d, _, ht => by
    have := aux_nca_bounds t d ht
    have h1 : 1 ≤ 2 ^ (d - t.length) := Nat.one_le_two_pow
    simp only [List.nil_prefix, true_iff, aux_nca_F_nil, List.length_nil, Nat.sub_zero]
    rw [pow_succ] at this
    omega
  | a :: s, t, 0, hs, _ => by simp at hs
  | a :: s, [], d + 1, hs, _ => by
    simp only [List.length_cons] at hs
    have hb := aux_nca_bounds s d (by omega)
    simp only [List.prefix_nil, reduceCtorEq, false_iff, aux_nca_F_cons, aux_nca_F_nil,
      List.length_cons, Nat.add_sub_add_right]
    cases a <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega
  | a :: s, b :: t, d + 1, hs, ht => by
    simp only [List.length_cons] at hs ht
    have hb := aux_nca_bounds s d (by omega)
    have hb' := aux_nca_bounds t d (by omega)
    have h1 : 1 ≤ 2 ^ (d - t.length) := Nat.one_le_two_pow
    have ih := aux_nca_interval s t d (by omega) (by omega)
    simp only [List.cons_prefix_cons, aux_nca_F_cons, List.length_cons, Nat.add_sub_add_right]
    cases a <;> cases b <;>
      simp only [if_true, if_false, Bool.false_eq_true, true_and, false_and, reduceCtorEq,
        Bool.true_eq_false, false_iff, ih] <;> omega

theorem aux_nca_key_cons (b : Bool) (s : List Bool) :
    key (b :: s) = (if b then 2 else 0) :: key s := rfl

theorem aux_nca_key_nil : key [] = [1] := rfl

theorem aux_nca_lex : ∀ (s t : List Bool) (d : ℕ), s.length ≤ d → t.length ≤ d →
    (List.Lex (· < ·) (key s) (key t) ↔ aux_nca_F d s < aux_nca_F d t)
  | [], [], d, _, _ => by
    rw [aux_nca_key_nil, List.cons_lex_cons_iff]; simp
  | [], b :: t, 0, _, ht => by simp at ht
  | [], b :: t, d + 1, _, ht => by
    simp only [List.length_cons] at ht
    have hb' := aux_nca_bounds t d (by omega)
    have h1 : 1 ≤ 2 ^ (d - t.length) := Nat.one_le_two_pow
    have hP : 0 < 2 ^ d := by positivity
    rw [aux_nca_key_nil, aux_nca_key_cons, aux_nca_F_nil, aux_nca_F_cons, List.cons_lex_cons_iff]
    cases b <;> simp <;> omega
  | a :: s, [], 0, hs, _ => by simp at hs
  | a :: s, [], d + 1, hs, _ => by
    simp only [List.length_cons] at hs
    have hb := aux_nca_bounds s d (by omega)
    have h1 : 1 ≤ 2 ^ (d - s.length) := Nat.one_le_two_pow
    have hP : 0 < 2 ^ d := by positivity
    rw [aux_nca_key_nil, aux_nca_key_cons, aux_nca_F_nil, aux_nca_F_cons, List.cons_lex_cons_iff]
    cases a <;> simp <;> omega
  | a :: s, b :: t, 0, hs, _ => by simp at hs
  | a :: s, b :: t, d + 1, hs, ht => by
    simp only [List.length_cons] at hs ht
    have hb := aux_nca_bounds s d (by omega)
    have hb' := aux_nca_bounds t d (by omega)
    have h1 : 1 ≤ 2 ^ (d - s.length) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (d - t.length) := Nat.one_le_two_pow
    have hP : 0 < 2 ^ d := by positivity
    have ih := aux_nca_lex s t d (by omega) (by omega)
    rw [aux_nca_key_cons, aux_nca_key_cons, aux_nca_F_cons, aux_nca_F_cons, List.cons_lex_cons_iff]
    cases a <;> cases b <;> simp [ih] <;> omega

theorem aux_nca_le_iff (l m : List ℕ) : l ≤ m ↔ List.Lex (· < ·) l m ∨ l = m := by
  rw [le_iff_lt_or_eq]; rfl

theorem aux_nca_key_inj (s t : List Bool) (h : key s = key t) : s = t := by
  unfold key at h
  have h' := List.append_cancel_right h
  exact List.map_injective_iff.2 (by intro a b; cases a <;> cases b <;> simp) h'

theorem aux_nca_F_inj (s t : List Bool) (d : ℕ) (hs : s.length ≤ d) (ht : t.length ≤ d)
    (h : aux_nca_F d s = aux_nca_F d t) : s = t := by
  have hu1 : 1 ≤ 2 ^ (d - s.length) := Nat.one_le_two_pow
  have hw1 : 1 ≤ 2 ^ (d - t.length) := Nat.one_le_two_pow
  have p1 := (aux_nca_interval s t d hs ht).2 (by omega)
  have p2 := (aux_nca_interval t s d ht hs).2 (by omega)
  exact p1.eq_of_length (le_antisymm p1.length_le p2.length_le)

theorem aux_nca_order (s t : List Bool) (d : ℕ) (hs : s.length ≤ d) (ht : t.length ≤ d) :
    key s ≤ key t ↔ aux_nca_F d s ≤ aux_nca_F d t := by
  rw [aux_nca_le_iff, aux_nca_lex s t d hs ht]
  constructor
  · rintro (h | h)
    · exact h.le
    · rw [aux_nca_key_inj s t h]
  · intro h
    rcases h.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [aux_nca_F_inj s t d hs ht h])

theorem aux_nca_surj : ∀ (d m : ℕ), 1 ≤ m → m < 2 ^ (d + 1) →
    ∃ s : List Bool, s.length ≤ d ∧ aux_nca_F d s = m
  | 0, m, h1, h2 => ⟨[], by simp, by simp at h2; simp [aux_nca_F_nil]; omega⟩
  | d + 1, m, h1, h2 => by
    have hp : (2:ℕ) ^ (d + 1 + 1) = 2 ^ (d + 1) + 2 ^ (d + 1) := by rw [pow_succ]; ring
    rcases lt_trichotomy m (2 ^ (d + 1)) with h | h | h
    · obtain ⟨t, ht, hF⟩ := aux_nca_surj d m h1 h
      exact ⟨false :: t, by simp; omega, by simp [aux_nca_F_cons, hF]⟩
    · exact ⟨[], by simp, by simp [aux_nca_F_nil, h]⟩
    · obtain ⟨t, ht, hF⟩ := aux_nca_surj d (m - 2 ^ (d + 1)) (by omega) (by omega)
      exact ⟨true :: t, by simp; omega, by simp [aux_nca_F_cons, hF]; omega⟩

theorem aux_nca_sym {d : ℕ} (v : Vertex d) : sym v = aux_nca_F d v.1 := by
  unfold sym
  have hc : (Finset.Icc 1 (aux_nca_F d v.1)).card = aux_nca_F d v.1 := by simp
  rw [← hc]
  have hv := aux_nca_bounds v.1 d v.2
  have hv1 : 1 ≤ 2 ^ (d - v.1.length) := Nat.one_le_two_pow
  apply Finset.card_bij (fun u _ => aux_nca_F d u.1)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [aux_nca_order u.1 v.1 d u.2 v.2] at hu
    have := aux_nca_bounds u.1 d u.2
    have h1 : 1 ≤ 2 ^ (d - u.1.length) := Nat.one_le_two_pow
    simp only [Finset.mem_Icc]; omega
  · intro u _ w _ h
    exact Subtype.ext (aux_nca_F_inj u.1 w.1 d u.2 w.2 h)
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    obtain ⟨s, hs, hF⟩ := aux_nca_surj d m (by omega) (by omega)
    refine ⟨⟨s, hs⟩, ?_, hF⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [aux_nca_order s v.1 d hs v.2]
    omega


end HarelTarjan.SymOrder

open HarelTarjan.SymOrder

theorem solution {d : ℕ} (v w : Vertex d) :
    IsAncestor v w ↔
      (sym v + 1 ≤ sym w + 2 ^ height v ∧ sym w + 1 ≤ sym v + 2 ^ height v) := by
  rw [aux_nca_sym v, aux_nca_sym w]
  exact aux_nca_interval v.1 w.1 d v.2 w.2
