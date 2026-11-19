-- Prove2me | solution 1 for Kyprianou.Ch01.firstGridTriggerPrefixCharacterisationPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:04:45.4262+00:00
-- url     : https://prove2.me/submissions/fdecc9cf-dc06-424d-8f3a-49540f66666c

import Mathlib.Data.Nat.Find
import Mathlib.Logic.Pairwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
set_option autoImplicit false

/-- First trigger before a sentinel is equivalent to a finite non-triggering prefix. -/
theorem solution
    {Ω : Type*} (p : ℕ → Ω → Prop) (N : ℕ) :
    let τ : Ω → ℕ := fun ω => by
      classical
      exact Nat.find (show ∃ k : ℕ, k = N ∨ p k ω from ⟨N, Or.inl rfl⟩)
    (∀ ω, τ ω ≤ N) ∧
      ∀ n : ℕ, n < N → ∀ ω : Ω,
        (n < τ ω ↔ ∀ k : ℕ, k ≤ n → ¬ p k ω) := by
  classical
  let hex (ω : Ω) : ∃ k : ℕ, k = N ∨ p k ω := ⟨N, Or.inl rfl⟩
  let τ : Ω → ℕ := fun ω => Nat.find (hex ω)
  change (∀ ω, τ ω ≤ N) ∧
    ∀ n : ℕ, n < N → ∀ ω : Ω,
      (n < τ ω ↔ ∀ k : ℕ, k ≤ n → ¬p k ω)
  constructor
  · intro ω
    exact Nat.find_le (h := hex ω) (Or.inl rfl)
  · intro n hn ω
    constructor
    · intro hgt k hk hp
      have hle : τ ω ≤ k := Nat.find_le (h := hex ω) (Or.inr hp)
      exact (not_le_of_gt (lt_of_le_of_lt hk hgt)) hle
    · intro hp
      by_contra hnot
      have hle : τ ω ≤ n := Nat.le_of_not_gt hnot
      have hf : τ ω = N ∨ p (τ ω) ω := Nat.find_spec (hex ω)
      rcases hf with hf | hhit
      · have hN : N ≤ n := by calc
          N = τ ω := hf.symm
          _ ≤ n := hle
        exact (not_le_of_gt hn) hN
      · exact hp (τ ω) hle hhit
