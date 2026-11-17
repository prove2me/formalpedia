-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_three_regular_side1__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:17:55.380205+00:00
-- url     : https://prove2.me/submissions/bfcc2845-d46c-4f61-99b9-c10d45e828e2

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
theorem KnodelPrimeCordial.knodel_three_regular_side1__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).degree (1, j) = 3 := by
  have hj := j.isLt
  have hN5 : 5 ≤ n / 2 := by omega
  have mc : ∀ a N : ℕ, a < 2 * N → (a < N ∧ a % N = a) ∨ (N ≤ a ∧ a % N = a - N) := by
    intro a N h
    rcases Nat.lt_or_ge a N with h1 | h1
    · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
    · refine Or.inr ⟨h1, ?_⟩
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  have C := mc (j.val + n / 2 - 1) (n / 2) (by omega)
  have D := mc (j.val + n / 2 - 3) (n / 2) (by omega)
  have key : (KnodelPrimeCordial.knodel 3 n).neighborFinset (1, j) =
      {(0, j), (0, ⟨(j.val + n / 2 - 1) % (n / 2), Nat.mod_lt _ (by omega)⟩),
        (0, ⟨(j.val + n / 2 - 3) % (n / 2), Nat.mod_lt _ (by omega)⟩)} := by
    ext ⟨a, b⟩
    have hb := b.isLt
    have A := mc (b.val + 1) (n / 2) (by omega)
    have B := mc (b.val + 3) (n / 2) (by omega)
    have E : b.val % (n / 2) = b.val := Nat.mod_eq_of_lt hb
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    simp only [KnodelPrimeCordial.knodel, Prod.mk.injEq, Fin.ext_iff]
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, Fin.val_one, true_and, and_true,
        zero_ne_one, false_and, false_or, one_ne_zero]
      constructor
      · rintro ⟨k, hk, hjv⟩
        interval_cases k <;> norm_num at hjv <;> omega
      · rintro (h | h | h)
        · exact ⟨0, by norm_num, by norm_num; omega⟩
        · exact ⟨1, by norm_num, by norm_num; omega⟩
        · exact ⟨2, by norm_num, by norm_num; omega⟩
    · simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, key]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff, true_and]
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff, true_and, not_or]
    omega

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).degree (1, j) = 3 := by
  have hj := j.isLt
  have hN5 : 5 ≤ n / 2 := by omega
  have mc : ∀ a N : ℕ, a < 2 * N → (a < N ∧ a % N = a) ∨ (N ≤ a ∧ a % N = a - N) := by
    intro a N h
    rcases Nat.lt_or_ge a N with h1 | h1
    · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
    · refine Or.inr ⟨h1, ?_⟩
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  have C := mc (j.val + n / 2 - 1) (n / 2) (by omega)
  have D := mc (j.val + n / 2 - 3) (n / 2) (by omega)
  have key : (KnodelPrimeCordial.knodel 3 n).neighborFinset (1, j) =
      {(0, j), (0, ⟨(j.val + n / 2 - 1) % (n / 2), Nat.mod_lt _ (by omega)⟩),
        (0, ⟨(j.val + n / 2 - 3) % (n / 2), Nat.mod_lt _ (by omega)⟩)} := by
    ext ⟨a, b⟩
    have hb := b.isLt
    have A := mc (b.val + 1) (n / 2) (by omega)
    have B := mc (b.val + 3) (n / 2) (by omega)
    have E : b.val % (n / 2) = b.val := Nat.mod_eq_of_lt hb
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    simp only [KnodelPrimeCordial.knodel, Prod.mk.injEq, Fin.ext_iff]
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, Fin.val_one, true_and, and_true,
        zero_ne_one, false_and, false_or, one_ne_zero]
      constructor
      · rintro ⟨k, hk, hjv⟩
        interval_cases k <;> norm_num at hjv <;> omega
      · rintro (h | h | h)
        · exact ⟨0, by norm_num, by norm_num; omega⟩
        · exact ⟨1, by norm_num, by norm_num; omega⟩
        · exact ⟨2, by norm_num, by norm_num; omega⟩
    · simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, key]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff, true_and]
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff, true_and, not_or]
    omega

