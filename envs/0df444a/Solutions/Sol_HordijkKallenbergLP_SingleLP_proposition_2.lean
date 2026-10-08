-- Prove2me | solution 1 for HordijkKallenbergLP.SingleLP.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:34:43.604392+00:00
-- url     : https://prove2.me/submissions/3357772d-0d71-4796-8003-32bbe79ac1b2

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model

set_option autoImplicit false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology HordijkKallenbergLP.SingleLP in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    ∀ i ∈ Ex M z.1, ∀ j ∉ Ex M z.1, M.trans i (f i) j = 0 := by
  intro i hi j hj
  obtain ⟨⟨h3, -, h5⟩, -⟩ := hopt
  have hx : ∀ p, 0 ≤ z.1 p := fun p => (h5 p).1
  have hsj : stateSum M z.1 j = 0 := by
    have h0 : 0 ≤ stateSum M z.1 j := Finset.sum_nonneg (fun p _ => hx p)
    simp only [Ex, Set.mem_setOf_eq, not_lt] at hj
    linarith
  have key := h3 j
  have hδ : ∑ p : Pair M, (if p.1.1 = j then (1:ℝ) else 0) * z.1 p = stateSum M z.1 j := by
    unfold stateSum
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  have hsum : ∑ p : Pair M, M.trans p.1.1 p.1.2 j * z.1 p = 0 := by
    have hsplit : ∑ p : Pair M,
        ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.1 p
        = ∑ p : Pair M, (if p.1.1 = j then (1:ℝ) else 0) * z.1 p
          - ∑ p : Pair M, M.trans p.1.1 p.1.2 j * z.1 p := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hsplit, hδ, hsj] at key
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun p _ => mul_nonneg (M.trans_nonneg _ _ _) (hx p))).1 hsum ⟨(i, f i), hf i⟩
    (Finset.mem_univ _)
  have hpos := (hsel i).1 hi
  rcases mul_eq_zero.1 hterm with h | h
  · exact h
  · exact absurd h hpos.ne'
