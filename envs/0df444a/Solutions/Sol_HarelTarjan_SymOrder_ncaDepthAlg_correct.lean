-- Prove2me | solution 1 for HarelTarjan.SymOrder.ncaDepthAlg_correct
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:29:12.311472+00:00
-- url     : https://prove2.me/submissions/daef8fa4-1e8b-4109-b277-aa01e430c9ef

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

theorem aux_nca_two_pow_add_eq_xor {m x : ℕ} (hx : x < 2 ^ m) : 2 ^ m + x = 2 ^ m ^^^ x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy j m with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [h.ne']
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hx]; simp
  · have hpow : 2 ^ (m + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 2 ^ m + x < 2 ^ j := by rw [pow_succ] at hpow; omega
    have h2 : x < 2 ^ j := by omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [h.ne]

theorem aux_nca_xor : ∀ (s t : List Bool) (d : ℕ), s.length ≤ d → t.length ≤ d →
    ¬ s <+: t → ¬ t <+: s →
    Nat.log 2 (aux_nca_F d s ^^^ aux_nca_F d t) + (lcp s t).length = d
  | [], t, d, _, _, h, _ => absurd (List.nil_prefix) h
  | a :: s, [], d, _, _, _, h => absurd (List.nil_prefix) h
  | a :: s, b :: t, 0, hs, _, _, _ => by simp at hs
  | a :: s, b :: t, d + 1, hs, ht, h1, h2 => by
    simp only [List.length_cons] at hs ht
    have hb := aux_nca_bounds s d (by omega)
    have hb' := aux_nca_bounds t d (by omega)
    have hs1 : 1 ≤ 2 ^ (d - s.length) := Nat.one_le_two_pow
    have ht1 : 1 ≤ 2 ^ (d - t.length) := Nat.one_le_two_pow
    have hxs : aux_nca_F d s < 2 ^ (d + 1) := by omega
    have hxt : aux_nca_F d t < 2 ^ (d + 1) := by omega
    have hlt : aux_nca_F d s ^^^ aux_nca_F d t < 2 ^ (d + 1) := Nat.xor_lt_two_pow hxs hxt
    simp only [List.cons_prefix_cons, not_and] at h1 h2
    rw [aux_nca_F_cons, aux_nca_F_cons]
    have hdiff : ∀ x y : ℕ, x < 2 ^ (d + 1) → y < 2 ^ (d + 1) → x ^^^ y < 2 ^ (d + 1) →
        Nat.log 2 (x ^^^ (2 ^ (d + 1) + y)) = d + 1 := by
      intro x y hx hy hxy
      rw [aux_nca_two_pow_add_eq_xor hy, ← Nat.xor_assoc, Nat.xor_comm x, Nat.xor_assoc,
        ← aux_nca_two_pow_add_eq_xor hxy]
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · omega
      · rw [pow_succ]; omega
    cases a <;> cases b
    · have ih := aux_nca_xor s t d (by omega) (by omega) (h1 rfl) (h2 rfl)
      simp only [lcp, if_true, Bool.false_eq_true, if_false, zero_add, List.length_cons]
      omega
    · simp only [lcp, Bool.false_eq_true, if_false, if_true, zero_add, List.length_nil,
        add_zero, reduceCtorEq]
      exact hdiff _ _ hxs hxt hlt
    · simp only [lcp, Bool.false_eq_true, if_false, if_true, zero_add, List.length_nil,
        add_zero, reduceCtorEq]
      rw [Nat.xor_comm]
      exact hdiff _ _ hxt hxs (by rw [Nat.xor_comm]; exact hlt)
    · have ih := aux_nca_xor s t d (by omega) (by omega) (h1 rfl) (h2 rfl)
      simp only [lcp, if_true, List.length_cons]
      rw [aux_nca_two_pow_add_eq_xor hxs, aux_nca_two_pow_add_eq_xor hxt, Nat.xor_assoc,
        ← Nat.xor_assoc (aux_nca_F d s), Nat.xor_comm (aux_nca_F d s), Nat.xor_assoc,
        ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      omega

theorem aux_nca_lcp_of_prefix : ∀ s t : List Bool, s <+: t → lcp s t = s
  | [], t, _ => by cases t <;> rfl
  | a :: s, [], h => by simp at h
  | a :: s, b :: t, h => by
    rw [List.cons_prefix_cons] at h
    obtain ⟨rfl, h⟩ := h
    simp [lcp, aux_nca_lcp_of_prefix s t h]

theorem aux_nca_lcp_comm : ∀ s t : List Bool, lcp s t = lcp t s
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: s, b :: t => by
    simp only [lcp]
    by_cases h : a = b
    · subst h; simp [aux_nca_lcp_comm s t]
    · simp [h, Ne.symm h]

end HarelTarjan.SymOrder

open HarelTarjan.SymOrder

theorem solution {d : ℕ} (v w : Vertex d) :
    ncaDepthAlg v w = depth (nca v w) := by
  unfold ncaDepthAlg depth nca height
  rw [aux_nca_sym v, aux_nca_sym w]
  have hv := v.2
  have hw := w.2
  simp only
  split_ifs with h1 h2
  · have hp := (aux_nca_interval v.1 w.1 d hv hw).2 h1
    rw [aux_nca_lcp_of_prefix _ _ hp]; omega
  · have hp := (aux_nca_interval w.1 v.1 d hw hv).2 h2
    rw [aux_nca_lcp_comm, aux_nca_lcp_of_prefix _ _ hp]; omega
  · have hn1 : ¬ v.1 <+: w.1 := fun hp => h1 ((aux_nca_interval v.1 w.1 d hv hw).1 hp)
    have hn2 : ¬ w.1 <+: v.1 := fun hp => h2 ((aux_nca_interval w.1 v.1 d hw hv).1 hp)
    have := aux_nca_xor v.1 w.1 d hv hw hn1 hn2
    omega
