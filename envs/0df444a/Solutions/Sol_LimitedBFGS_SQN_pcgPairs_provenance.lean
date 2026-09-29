-- Prove2me | solution 1 for LimitedBFGS.SQN.pcgPairs_provenance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T21:37:44.021583+00:00
-- url     : https://prove2.me/submissions/c003d8c5-cde9-494f-99f6-359dd49f6673

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs
import Definitions.Def_LimitedBFGS_SQN_sqnIter

open Matrix
open LimitedBFGS.SQN

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (m : ℕ) (k : ℕ) :
    ∀ p ∈ pcgPairs A b H₀ x₀ m k, ∃ j < k, p = pcgPair A b H₀ x₀ j := by
  induction k with
  | zero =>
      intro p hp
      simp [pcgPairs] at hp
  | succ k ih =>
      intro p hp
      have hp' : p ∈ pcgPairs A b H₀ x₀ m (k + 1) := by
        simpa only [Nat.succ_eq_add_one] using hp
      rw [pcgPairs] at hp'
      have hmem : p ∈ pcgPairs A b H₀ x₀ m k ++ [pcgPair A b H₀ x₀ k] :=
        List.mem_of_mem_drop hp'
      rcases List.mem_append.mp hmem with h_old | h_new
      · obtain ⟨j, hj, hpj⟩ := ih p h_old
        exact ⟨j, by omega, hpj⟩
      · obtain ⟨rfl⟩ := List.mem_singleton.mp h_new
        exact ⟨k, by omega, rfl⟩
