-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_three_offsets_distinct__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:06:12.76114+00:00
-- url     : https://prove2.me/submissions/4ea9f7cf-7d2e-4b95-b12d-88247a56915d

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
theorem KnodelPrimeCordial.knodel_three_offsets_distinct__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) : let x : Fin (n / 2) := j; let y : Fin (n / 2) := ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩; let z : Fin (n / 2) := ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩; x ≠ y ∧ x ≠ z ∧ y ≠ z := by
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

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) : let x : Fin (n / 2) := j; let y : Fin (n / 2) := ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩; let z : Fin (n / 2) := ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩; x ≠ y ∧ x ≠ z ∧ y ≠ z := by
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

