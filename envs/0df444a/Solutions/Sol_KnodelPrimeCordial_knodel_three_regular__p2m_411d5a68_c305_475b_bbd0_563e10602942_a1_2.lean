-- Prove2me | solution 2 for KnodelPrimeCordial.knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:17:56.869193+00:00
-- url     : https://prove2.me/submissions/f6809972-4850-475d-9e08-4aa658e12a69

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
theorem KnodelPrimeCordial.knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (v : Fin 2 × Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).degree v = 3 := by
  have S0 : ∀ j : Fin (n / 2), (KnodelPrimeCordial.knodel 3 n).degree (0, j) = 3 := by
    intro j
    have hN : (KnodelPrimeCordial.knodel 3 n).neighborFinset (0, j) = {(1, j), (1, ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩), (1, ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩)} := by
      have hj := j.isLt
      ext ⟨a, b⟩
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
      simp only [KnodelPrimeCordial.knodel, Prod.mk.injEq]
      constructor
      · rintro (⟨-, ha, k, hk, hb⟩ | ⟨-, h1, -⟩)
        · interval_cases k
          · left; refine ⟨ha, Fin.ext ?_⟩
            rw [hb]; simp [Nat.mod_eq_of_lt hj]
          · right; left; exact ⟨ha, Fin.ext (by rw [hb]; norm_num)⟩
          · right; right; exact ⟨ha, Fin.ext (by rw [hb]; norm_num)⟩
        · exact absurd h1 (by decide)
      · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
        · left; refine ⟨by simp, ha, 0, by norm_num, ?_⟩
          rw [hb]; simp [Nat.mod_eq_of_lt hj]
        · left; refine ⟨by simp, ha, 1, by norm_num, ?_⟩
          rw [hb]; norm_num
        · left; refine ⟨by simp, ha, 2, by norm_num, ?_⟩
          rw [hb]; norm_num
    have hD : let x : Fin (n / 2) := j; let y : Fin (n / 2) := ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩; let z : Fin (n / 2) := ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩; x ≠ y ∧ x ≠ z ∧ y ≠ z := by
      intro x y z
      have hj := j.isLt
      have hN : 5 ≤ n / 2 := by omega
      have mc : ∀ a N : ℕ, a < 2 * N → (a < N ∧ a % N = a) ∨ (N ≤ a ∧ a % N = a - N) := by
        intro a N h
        rcases Nat.lt_or_ge a N with h1 | h1
        · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
        · refine Or.inr ⟨h1, ?_⟩
          rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
      have A := mc (j.val + 1) (n / 2) (by omega)
      have B := mc (j.val + 3) (n / 2) (by omega)
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have h' := congrArg Fin.val h <;>
        simp only [x, y, z] at h' <;> omega
    obtain ⟨h1, h2, h3⟩ := hD
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hN]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
      intro _; exact h3
    · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or, not_and]
      exact ⟨fun _ => h1, fun _ => h2⟩
  have S1 : ∀ j : Fin (n / 2), (KnodelPrimeCordial.knodel 3 n).degree (1, j) = 3 := by
    intro j
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
  obtain ⟨a, j⟩ := v
  fin_cases a
  · exact S0 j
  · exact S1 j

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (v : Fin 2 × Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).degree v = 3 := by
  have S0 : ∀ j : Fin (n / 2), (KnodelPrimeCordial.knodel 3 n).degree (0, j) = 3 := by
    intro j
    have hN : (KnodelPrimeCordial.knodel 3 n).neighborFinset (0, j) = {(1, j), (1, ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩), (1, ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩)} := by
      have hj := j.isLt
      ext ⟨a, b⟩
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
      simp only [KnodelPrimeCordial.knodel, Prod.mk.injEq]
      constructor
      · rintro (⟨-, ha, k, hk, hb⟩ | ⟨-, h1, -⟩)
        · interval_cases k
          · left; refine ⟨ha, Fin.ext ?_⟩
            rw [hb]; simp [Nat.mod_eq_of_lt hj]
          · right; left; exact ⟨ha, Fin.ext (by rw [hb]; norm_num)⟩
          · right; right; exact ⟨ha, Fin.ext (by rw [hb]; norm_num)⟩
        · exact absurd h1 (by decide)
      · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
        · left; refine ⟨by simp, ha, 0, by norm_num, ?_⟩
          rw [hb]; simp [Nat.mod_eq_of_lt hj]
        · left; refine ⟨by simp, ha, 1, by norm_num, ?_⟩
          rw [hb]; norm_num
        · left; refine ⟨by simp, ha, 2, by norm_num, ?_⟩
          rw [hb]; norm_num
    have hD : let x : Fin (n / 2) := j; let y : Fin (n / 2) := ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩; let z : Fin (n / 2) := ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩; x ≠ y ∧ x ≠ z ∧ y ≠ z := by
      intro x y z
      have hj := j.isLt
      have hN : 5 ≤ n / 2 := by omega
      have mc : ∀ a N : ℕ, a < 2 * N → (a < N ∧ a % N = a) ∨ (N ≤ a ∧ a % N = a - N) := by
        intro a N h
        rcases Nat.lt_or_ge a N with h1 | h1
        · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
        · refine Or.inr ⟨h1, ?_⟩
          rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
      have A := mc (j.val + 1) (n / 2) (by omega)
      have B := mc (j.val + 3) (n / 2) (by omega)
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have h' := congrArg Fin.val h <;>
        simp only [x, y, z] at h' <;> omega
    obtain ⟨h1, h2, h3⟩ := hD
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hN]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
      intro _; exact h3
    · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or, not_and]
      exact ⟨fun _ => h1, fun _ => h2⟩
  have S1 : ∀ j : Fin (n / 2), (KnodelPrimeCordial.knodel 3 n).degree (1, j) = 3 := by
    intro j
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
  obtain ⟨a, j⟩ := v
  fin_cases a
  · exact S0 j
  · exact S1 j

