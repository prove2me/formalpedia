-- Prove2me | solution 1 for KernelRamsey.noClique_chain
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:59:26.035538+00:00
-- url     : https://prove2.me/submissions/4e8a06e0-dcf7-4fd3-961b-594cc30ff190

import Mathlib
import Definitions.Def_KernelRamsey_Mask
open KernelRamsey

theorem solution (rows : List Nat) (k : Nat) :
    ∀ n : Nat, (∀ p : Nat, p < n → noClique rows p k ((2 ^ p - 1) &&& row rows p) = true) →
      noClique rows n (k + 1) (2 ^ n - 1) = true := by
  intro n
  induction n with
  | zero => intro _; simp [noClique]
  | succ n ih =>
    intro h
    have hne : (2 ^ (n + 1) - 1 : Nat) ≠ 0 := by
      have : 2 ≤ 2 ^ (n + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hlog : Nat.log2 (2 ^ (n + 1) - 1) = n := by
      rw [Nat.log2_eq_iff hne]
      have h1 : 2 ^ n ≤ 2 ^ (n + 1) - 1 := by
        have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
        have : 0 < 2 ^ n := by positivity
        omega
      exact ⟨h1, by have : 0 < 2 ^ (n + 1) := by positivity
                    omega⟩
    have hxor : (2 ^ (n + 1) - 1) ^^^ 2 ^ n = 2 ^ n - 1 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
      by_cases h1 : i < n
      · have : n ≠ i := by omega
        simp [h1, this, show i < n + 1 by omega]
      · by_cases h2 : i = n
        · subst h2; simp
        · have h3 : ¬ i < n + 1 := by omega
          simp [h1, h2, h3, Ne.symm h2]
    have hne' : ((2 ^ (n + 1) - 1 : Nat) == 0) = false := by simpa using hne
    simp only [noClique, hne', Bool.false_eq_true, ↓reduceIte, hlog, hxor, Bool.and_eq_true]
    exact ⟨h n (by omega), ih (fun p hp => h p (by omega))⟩
