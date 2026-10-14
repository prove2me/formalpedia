-- Prove2me | solution 1 for MDPComplexity.CircuitValue.expCost_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:07:29.181986+00:00
-- url     : https://prove2.me/submissions/cfa1cf0c-e9c4-43a1-aa04-c2d24068a01f

import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model



namespace MDPComplexity.CircuitValue

open Finset BigOperators

theorem expCost_eq_zero_iff_core {S : Type} [Fintype S] [DecidableEq S] (M : MDP S)
    (hc : ∀ s i t, 0 ≤ M.c s i t) (s₀ : S) (δ : M.Policy) (T : ℕ) :
    M.expCost s₀ δ T = 0 ↔
      ∀ x : Fin (T + 1) → S, 0 < M.trajProb s₀ δ T x →
        ∀ t : Fin (T + 1), M.c (x t) (δ (x t) (t : ℕ)) (t : ℕ) = 0 := by
  have hp : ∀ x, 0 ≤ M.trajProb s₀ δ T x := by
    intro x
    unfold MDP.trajProb
    apply mul_nonneg
    · split_ifs <;> norm_num
    · exact Finset.prod_nonneg (fun t _ => M.p_nonneg _ _ _ _)
  have hcost : ∀ x, 0 ≤ M.trajCost δ T x := fun x =>
    Finset.sum_nonneg (fun t _ => hc _ _ _)
  have hcz : ∀ x, M.trajCost δ T x = 0 ↔ ∀ t : Fin (T + 1), M.c (x t) (δ (x t) (t : ℕ)) (t : ℕ) = 0 := by
    intro x
    unfold MDP.trajCost
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hc _ _ _)]
    simp
  unfold MDP.expCost
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (hp x) (hcost x))]
  constructor
  · intro h x hx
    have := h x (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hx.ne'
    · exact (hcz x).mp h1
  · intro h x _
    rcases (hp x).lt_or_eq with h1 | h1
    · rw [(hcz x).mpr (h x h1), mul_zero]
    · rw [← h1, zero_mul]

end MDPComplexity.CircuitValue

open MDPComplexity.CircuitValue


theorem solution {S : Type} [Fintype S] [DecidableEq S] (M : MDP S)
    (hc : ∀ s i t, 0 ≤ M.c s i t) (s₀ : S) (δ : M.Policy) (T : ℕ) :
    M.expCost s₀ δ T = 0 ↔
      ∀ x : Fin (T + 1) → S, 0 < M.trajProb s₀ δ T x →
        ∀ t : Fin (T + 1), M.c (x t) (δ (x t) (t : ℕ)) (t : ℕ) = 0 := by
  exact expCost_eq_zero_iff_core M hc s₀ δ T
