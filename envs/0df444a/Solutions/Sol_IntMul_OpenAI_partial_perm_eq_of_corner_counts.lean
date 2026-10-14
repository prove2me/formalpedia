-- Prove2me | solution 1 for IntMul.OpenAI.partial_perm_eq_of_corner_counts
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T14:08:59.060729+00:00
-- url     : https://prove2.me/submissions/7789e3d0-4413-4eb6-8a9b-2ced10b11bfa

import Mathlib

open Finset

namespace PPUniqAux

variable {n : ℕ} {K : Type*} [One K] [DecidableEq K]

/-- Number of ones of `P` in rows `< X` and columns `≥ Y`. -/
def cnt (P : Matrix (Fin n) (Fin n) K) (X Y : ℕ) : ℕ :=
  (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card

lemma cnt_succ_row (P : Matrix (Fin n) (Fin n) K) (X Y : ℕ) :
    cnt P (X + 1) Y = cnt P X Y +
      (univ.filter fun x : Fin n × Fin n => x.1.val = X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hP : P x.1 x.2 = 1 <;> simp [hP] <;> omega
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    obtain ⟨a1, a2, -⟩ := h1
    obtain ⟨b1, b2, -⟩ := h2
    omega

lemma row_succ_col (P : Matrix (Fin n) (Fin n) K) (X Y : ℕ) :
    (univ.filter fun x : Fin n × Fin n => x.1.val = X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card =
      (univ.filter fun x : Fin n × Fin n => x.1.val = X ∧ x.2.val = Y ∧ P x.1 x.2 = 1).card +
      (univ.filter fun x : Fin n × Fin n => x.1.val = X ∧ Y + 1 ≤ x.2.val ∧ P x.1 x.2 = 1).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hP : P x.1 x.2 = 1 <;> simp [hP] <;> omega
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    obtain ⟨a1, a2, -⟩ := h1
    obtain ⟨b1, b2, -⟩ := h2
    omega

lemma single_cnt (P : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (univ.filter fun x : Fin n × Fin n => x.1.val = i.val ∧ x.2.val = j.val ∧ P x.1 x.2 = 1).card =
      if P i j = 1 then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨(i, j), ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · rintro rfl; exact ⟨rfl, rfl, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2, h3⟩
    have : x = (i, j) := Prod.ext (Fin.ext h1) (Fin.ext h2)
    subst this
    exact h h3

end PPUniqAux

open PPUniqAux in
theorem solution {n : ℕ} {K : Type*} [Zero K] [One K] [DecidableEq K]
    (P P' : Matrix (Fin n) (Fin n) K)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1) (h01' : ∀ i j, P' i j = 0 ∨ P' i j = 1)
    (h : ∀ X Y : ℕ,
      (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card =
      (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P' x.1 x.2 = 1).card) :
    P = P' := by
  have hc : ∀ X Y, cnt P X Y = cnt P' X Y := h
  have key : ∀ i j : Fin n, (if P i j = 1 then 1 else 0) = (if P' i j = 1 then 1 else 0) := by
    intro i j
    rw [← single_cnt P i j, ← single_cnt P' i j]
    have e1 := cnt_succ_row P i.val j.val
    have e2 := cnt_succ_row P' i.val j.val
    have e3 := row_succ_col P i.val j.val
    have e4 := row_succ_col P' i.val j.val
    have e5 := cnt_succ_row P i.val (j.val + 1)
    have e6 := cnt_succ_row P' i.val (j.val + 1)
    rw [hc, hc] at e1
    rw [hc, hc] at e5
    omega
  ext i j
  have := key i j
  rcases h01 i j with a | a <;> rcases h01' i j with b | b <;> rw [a, b] at this ⊢
  all_goals (simp at this; first | exact this | exact this.symm)
