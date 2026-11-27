-- Prove2me | solution 1 for HammingSumset729.Approximation.fact_A_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:06:00.107171+00:00
-- url     : https://prove2.me/submissions/28df6573-e775-498a-a2af-7e9c89e96a5e

import Definitions.Def_HammingSumset729_Approximation_Strings

set_option autoImplicit false
open scoped ENNReal NNReal
open HammingSumset729.Approximation

private lemma dist_card {α : Type*} [DecidableEq α] :
    ∀ (s t : List α), distance s t =
      ((Finset.range (min s.length t.length)).filter (fun k => s[k]? ≠ t[k]?)).card
  | [], t => by simp [distance]
  | a :: s, [] => by simp [distance]
  | a :: s, b :: t => by
    have ih := dist_card s t
    rw [Finset.card_filter] at ih ⊢
    simp only [distance, List.zip_cons_cons, List.filter_cons] at ih ⊢
    rw [List.length_cons, List.length_cons,
      show min (s.length + 1) (t.length + 1) = min s.length t.length + 1 by omega,
      Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, ← ih]
    by_cases h : a = b
    · subst h; simp
    · simp [h]

private lemma substring_get {α : Type*} (t : List α) (i len k : ℕ) (hk : k < len)
    (h : i + len ≤ t.length) : (substring t i len)[k]? = t[i + k]? := by
  simp [substring, List.getElem?_take, hk, List.getElem?_drop]

private lemma substring_len {α : Type*} (t : List α) (i len : ℕ)
    (h : i + len ≤ t.length) : (substring t i len).length = len := by
  simp [substring]; omega

private lemma shiftDist_card {α : Type*} [DecidableEq α] (t p : List α) (i : ℕ)
    (h : i + p.length ≤ t.length) :
    shiftDistance t p i =
      ((Finset.range p.length).filter (fun k => t[i + k]? ≠ p[k]?)).card := by
  rw [shiftDistance, dist_card, substring_len t i _ h, min_self]
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [substring_get t i _ k (Finset.mem_range.mp hk) h]

theorem solution {α : Type*} [DecidableEq α] (t p : List α)
    (x : ℝ) (hx : 0 ≤ x) (ell : ℕ) (hperiod : IsMinimalPeriod p (2 * x) ell)
    (i j : ℕ) (hij : i < j) (hi : i + p.length ≤ t.length)
    (hj : j + p.length ≤ t.length)
    (hdi : (shiftDistance t p i : ℝ) ≤ x)
    (hdj : (shiftDistance t p j : ℝ) ≤ x) : ell ≤ j - i := by
  obtain ⟨⟨_, hellle, _⟩, hmin⟩ := hperiod
  by_cases hd : p.length < j - i
  · omega
  push_neg at hd
  apply hmin
  refine ⟨by omega, hd, ?_⟩
  set d := j - i with hddef
  rw [dist_card]
  have hl1 : (p.drop d).length = p.length - d := by simp
  have hl2 : (p.take (p.length - d)).length = p.length - d := by simp
  rw [hl1, hl2, min_self]
  set S := (Finset.range (p.length - d)).filter
    (fun k => (p.drop d)[k]? ≠ (p.take (p.length - d))[k]?)
  set A := (Finset.range p.length).filter (fun k => t[i + k]? ≠ p[k]?)
  set B := (Finset.range p.length).filter (fun k => t[j + k]? ≠ p[k]?)
  set A2 := (Finset.range (p.length - d)).filter (fun k => t[i + (k + d)]? ≠ p[k + d]?)
  have hsub : S ⊆ A2 ∪ B := by
    intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk1, hk2⟩ := hk
    rw [List.getElem?_drop, List.getElem?_take, if_pos hk1] at hk2
    simp only [Finset.mem_union, A2, B, Finset.mem_filter, Finset.mem_range]
    by_cases hc : t[j + k]? = p[k]?
    · left
      refine ⟨hk1, ?_⟩
      have : i + (k + d) = j + k := by omega
      rw [this, hc]
      intro h'; apply hk2; rw [Nat.add_comm d k]; exact h'.symm
    · right; exact ⟨by omega, hc⟩
  have hcardA : A2.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun k => k + d)
    · intro k hk
      simp only [A2, A, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk ⊢
      exact ⟨by omega, hk.2⟩
    · intro a _ b _ h; simpa using h
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le A2 B
  rw [shiftDist_card t p i hi] at hdi
  rw [shiftDist_card t p j hj] at hdj
  have : (S.card : ℝ) ≤ (A.card : ℝ) + B.card := by exact_mod_cast (by omega)
  linarith
