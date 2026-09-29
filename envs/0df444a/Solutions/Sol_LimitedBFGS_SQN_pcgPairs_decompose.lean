-- Prove2me | solution 1 for LimitedBFGS.SQN.pcgPairs_decompose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T20:59:03.102452+00:00
-- url     : https://prove2.me/submissions/18258693-a625-485f-965f-04e2e18a85ea

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs

open Matrix
open LimitedBFGS.SQN

namespace LimitedBFGS.SQN

private theorem prov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (m k : ℕ) :
    ∀ p ∈ pcgPairs A b H₀ x₀ m k, ∃ j < k, p = pcgPair A b H₀ x₀ j := by
  induction k with
  | zero =>
      intro p hp
      rw [pcgPairs] at hp
      simp at hp
  | succ k ih =>
      intro p hp
      -- The definition appends the newest pair and then drops; membership in the
      -- dropped list is first weakened back to membership in the appended list.
      have hp' : p ∈ (pcgPairs A b H₀ x₀ m k ++ [pcgPair A b H₀ x₀ k]) := by
        rw [pcgPairs] at hp
        exact List.mem_of_mem_drop hp
      rcases List.mem_append.mp hp' with hpold | hpnew
      · obtain ⟨j, hj, heq⟩ := ih p hpold
        exact ⟨j, by omega, heq⟩
      · have hqp : p = pcgPair A b H₀ x₀ k := by simpa using hpnew
        subst hqp
        exact ⟨k, by omega, rfl⟩

end LimitedBFGS.SQN

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    (∀ p ∈ pcgPairs A b H₀ x₀ m k, ∃ j < k, p = pcgPair A b H₀ x₀ j) ∧
      pcgPairs A b H₀ x₀ m (k + 1) =
        (pcgPairs A b H₀ x₀ m k).drop ((pcgPairs A b H₀ x₀ m k).length + 1 - m) ++
          [pcgPair A b H₀ x₀ k] := by
  constructor
  · exact prov A b H₀ x₀ m k
  · -- The trim never discards the pair just appended: with `1 ≤ m` the drop amount
    -- `old.length + 1 - m` stays within `old.length`, so the newest pair survives.
    have hle : (pcgPairs A b H₀ x₀ m k).length + 1 - m
        ≤ (pcgPairs A b H₀ x₀ m k).length := by omega
    simp only [pcgPairs, List.length_append, List.length_singleton]
    exact List.drop_append_of_le_length hle
