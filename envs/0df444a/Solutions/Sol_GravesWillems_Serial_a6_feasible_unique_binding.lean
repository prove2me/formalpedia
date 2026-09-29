-- Prove2me | solution 1 for GravesWillems.Serial.a6_feasible_unique_binding
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:07:21.571319+00:00
-- url     : https://prove2.me/submissions/7f39df24-c53b-4220-999b-10a565c26309

import Mathlib
import Definitions.Def_GravesWillems_Serial_programP

namespace GravesWillems.Serial

theorem aux_a6fub_sum (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) :
    ∀ i, 1 ≤ i → i ≤ N →
      ∑ m ∈ Finset.Icc 1 i, a6 N T D m = D (∑ m ∈ Finset.Icc 1 i, T m) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hkN
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [a6]
    · rw [Finset.sum_Icc_succ_top (by omega), ih hk (by omega)]
      have h1 : k + 1 ≠ 1 := by omega
      have h2 : k + 1 ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨by omega, hkN⟩
      simp only [a6, h1, h2, if_false, if_true, Nat.add_sub_cancel]
      ring

theorem aux_a6fub_S_mono (T : ℕ → ℕ) (i : ℕ) :
    ∑ m ∈ Finset.Icc 1 i, T m ≤ ∑ m ∈ Finset.Icc 1 (i + 1), T m := by
  rw [Finset.sum_Icc_succ_top (by omega)]
  omega

end GravesWillems.Serial

open GravesWillems.Serial

theorem solution (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ)
    (hD0 : D 0 = 0) (hD : Monotone D) :
    Feasible N T D (a6 N T D) ∧
    (∀ i ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 i, a6 N T D m = D (∑ m ∈ Finset.Icc 1 i, T m)) ∧
    ∀ B : ℕ → ℝ,
      (∀ i ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 i, B m = D (∑ m ∈ Finset.Icc 1 i, T m)) →
      ∀ i ∈ Finset.Icc 1 N, B i = a6 N T D i := by
  have hsum : ∀ i ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 i, a6 N T D m = D (∑ m ∈ Finset.Icc 1 i, T m) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact aux_a6fub_sum N T D i hi.1 hi.2
  refine ⟨⟨fun i hi => (hsum i hi).ge, ?_⟩, hsum, ?_⟩
  · intro i hi
    rw [Finset.mem_Icc] at hi
    by_cases h1 : i = 1
    · subst h1
      simp only [a6, if_true]
      rw [← hD0]
      exact hD (Nat.zero_le _)
    · have h2 : i ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨by omega, hi.2⟩
      simp only [a6, h1, h2, if_false, if_true]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel, sub_nonneg]
      exact hD (aux_a6fub_S_mono T k)
  · intro B hB i hi
    have hi' := Finset.mem_Icc.mp hi
    by_cases h1 : i = 1
    · subst h1
      have := hB 1 hi
      simpa [a6] using this
    · have h2 : i ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨by omega, hi'.2⟩
      simp only [a6, h1, h2, if_false, if_true]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hk := hB k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hk1 := hB (k + 1) hi
      rw [Finset.sum_Icc_succ_top (by omega)] at hk1
      rw [← hk, ← hk1]
      ring
