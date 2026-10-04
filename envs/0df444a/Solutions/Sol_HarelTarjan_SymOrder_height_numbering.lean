-- Prove2me | solution 1 for HarelTarjan.SymOrder.height_numbering
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T09:06:51.959914+00:00
-- url     : https://prove2.me/submissions/86ac123b-b262-49ef-836e-72a782e22693

/- Portions of the auxiliary development are adapted from the public Prove2Me
submission by mrfancypants, bd26faaa-7f24-42d5-a222-5d318ccd3b56 (2026-09-29).
Source: https://prove2.me/api/v1/submissions/bd26faaa-7f24-42d5-a222-5d318ccd3b56/solution
Reused under the platform's Apache-2.0 public-contribution terms.
The final milestone statement and its packaging below are new. -/

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym

namespace HarelTarjan.SymOrder

theorem aux_ht1_lt (a b : ℕ) (l l' : List ℕ) :
    (a :: l) < (b :: l') ↔ a < b ∨ (a = b ∧ l < l') := by
  show List.Lex (· < ·) (a :: l) (b :: l') ↔ _
  constructor
  · intro h
    cases h with
    | cons h => exact Or.inr ⟨rfl, h⟩
    | rel h => exact Or.inl h
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

theorem aux_ht1_le (a b : ℕ) (l l' : List ℕ) :
    (a :: l) ≤ (b :: l') ↔ a < b ∨ (a = b ∧ l ≤ l') := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, aux_ht1_lt]
  constructor
  · rintro ((h | ⟨rfl, h⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, Or.inl h⟩
    · simp only [List.cons.injEq] at h
      exact Or.inr ⟨h.1, Or.inr h.2⟩
  · rintro (h | ⟨rfl, h | rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr rfl

theorem aux_ht1_key_nil : key [] = [1] := rfl

theorem aux_ht1_key_cons (b : Bool) (s : List Bool) :
    key (b :: s) = (if b then 2 else 0) :: key s := by
  simp [key]

theorem aux_ht1_paths_zero : pathsUpTo 0 = {[]} := by
  ext s
  simp [mem_pathsUpTo]

theorem aux_ht1_paths_succ (d : ℕ) :
    pathsUpTo (d + 1) = insert [] ((pathsUpTo d).map ⟨List.cons false, List.cons_injective⟩ ∪
      (pathsUpTo d).map ⟨List.cons true, List.cons_injective⟩) := by
  ext s
  cases s with
  | nil => simp [mem_pathsUpTo]
  | cons b t => cases b <;> simp [mem_pathsUpTo]

theorem aux_ht1_card_filter_succ (d : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    ((pathsUpTo (d + 1)).filter P).card = (if P [] then 1 else 0)
      + ((pathsUpTo d).filter (fun u => P (false :: u))).card
      + ((pathsUpTo d).filter (fun u => P (true :: u))).card := by
  simp only [Finset.card_filter]
  rw [aux_ht1_paths_succ, Finset.sum_insert, Finset.sum_union, Finset.sum_map, Finset.sum_map]
  · simp only [Function.Embedding.coeFn_mk]
    ring
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at ha hb
    obtain ⟨x, _, rfl⟩ := ha
    obtain ⟨y, _, hy⟩ := hb
    simp at hy
  · simp

theorem aux_ht1_card_paths (d : ℕ) : (pathsUpTo d).card + 1 = 2 ^ (d + 1) := by
  induction d with
  | zero => simp [aux_ht1_paths_zero]
  | succ n ih =>
    have h := aux_ht1_card_filter_succ n (fun _ => True)
    simp at h
    rw [h, pow_succ]
    omega

theorem aux_ht1_foldl (s : List Bool) (a : ℕ) :
    s.foldl (fun acc b => 2 * acc + if b then 1 else 0) a
      = a * 2 ^ s.length + s.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0 := by
  induction s generalizing a with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (2 * 0 + if b then 1 else 0)]
    cases b <;> simp <;> ring

theorem aux_ht1_count : ∀ (s : List Bool) (d : ℕ), s.length ≤ d →
    ((pathsUpTo d).filter (fun u => key u ≤ key s)).card
      = (2 * s.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0 + 1) * 2 ^ (d - s.length) := by
  intro s
  induction s with
  | nil =>
    intro d _
    cases d with
    | zero =>
      rw [aux_ht1_paths_zero, Finset.filter_singleton]
      simp
    | succ n =>
      rw [aux_ht1_card_filter_succ]
      simp [aux_ht1_key_nil, aux_ht1_key_cons, aux_ht1_le]
      have := aux_ht1_card_paths n
      omega
  | cons b s ih =>
    intro d hd
    cases d with
    | zero => simp at hd
    | succ n =>
      simp only [List.length_cons] at hd
      have hsn : s.length ≤ n := by omega
      rw [aux_ht1_card_filter_succ]
      simp only [aux_ht1_key_nil, aux_ht1_key_cons]
      cases b with
      | false =>
        simp only [aux_ht1_le, Bool.false_eq_true, if_false]
        simp
        rw [ih n hsn]
      | true =>
        simp only [aux_ht1_le, if_true]
        simp
        rw [ih n hsn]
        have hc := aux_ht1_card_paths n
        rw [aux_ht1_foldl s 1]
        obtain ⟨k, rfl⟩ : ∃ k, n = s.length + k := ⟨n - s.length, by omega⟩
        have e2 : s.length + k - s.length = k := by omega
        rw [e2]
        rw [pow_succ, pow_add] at hc
        nlinarith [hc]

theorem aux_ht1_sym {d : ℕ} (v : Vertex d) :
    sym v = ((pathsUpTo d).filter (fun u => key u ≤ key v.1)).card := by
  unfold sym
  apply Finset.card_bij (fun u _ => u.1)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_filter, mem_pathsUpTo]
    exact ⟨u.2, hu⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter, mem_pathsUpTo] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

theorem aux_ht1_sym_eq {d : ℕ} (v : Vertex d) :
    sym v = (2 * leftIndex v + 1) * 2 ^ height v := by
  rw [aux_ht1_sym, aux_ht1_count v.1 d v.2]
  rfl


private theorem index_bound (s : List Bool) :
    s.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0 < 2 ^ s.length := by
  induction s with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, List.length_cons, zero_mul, zero_add]
    rw [aux_ht1_foldl]
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true, zero_mul, zero_add,
      one_mul, pow_succ] <;> omega

private theorem index_surjective : ∀ k j : ℕ, j < 2 ^ k →
    ∃ s : List Bool, s.length = k ∧
      s.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0 = j
  | 0, j, hj => by
    have : j = 0 := by simpa using hj
    subst j
    exact ⟨[], rfl, rfl⟩
  | k + 1, j, hj => by
    have hq : j / 2 < 2 ^ k := by rw [pow_succ] at hj; omega
    obtain ⟨s, hs, hv⟩ := index_surjective k (j / 2) hq
    refine ⟨s ++ [decide (j % 2 = 1)], by simp [hs], ?_⟩
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hv]
    split_ifs <;> simp_all <;> omega

end HarelTarjan.SymOrder

open HarelTarjan.SymOrder

theorem solution {d : ℕ} :
    (∀ v : Vertex d, sym v = (2 * leftIndex v + 1) * 2 ^ height v) ∧
      ∀ h : ℕ, h ≤ d →
        (Finset.univ.filter (fun v : Vertex d => height v = h)).image sym =
          (Finset.range (2 ^ (d - h))).image (fun j => (2 * j + 1) * 2 ^ h) := by
  refine ⟨aux_ht1_sym_eq, ?_⟩
  intro h hhd
  ext n
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨leftIndex v, ?_, ?_⟩
    · have hb := index_bound v.1
      have hlen : v.1.length = d - h := by
        have hd := v.2
        unfold height at hv
        omega
      simpa [leftIndex, hlen] using hb
    · rw [aux_ht1_sym_eq, hv]
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨s, hs, hj'⟩ := index_surjective (d - h) j hj
    have hsd : s.length ≤ d := by omega
    let v : Vertex d := ⟨s, hsd⟩
    have hv : height v = h := by change d - s.length = h; omega
    refine ⟨v, hv, ?_⟩
    rw [aux_ht1_sym_eq, hv]
    change (2 * s.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0 + 1) * 2 ^ h = _
    rw [hj']
