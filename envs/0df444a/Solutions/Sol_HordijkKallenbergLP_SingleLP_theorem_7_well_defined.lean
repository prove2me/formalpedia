-- Prove2me | solution 1 for HordijkKallenbergLP.SingleLP.theorem_7_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:41:07.975992+00:00
-- url     : https://prove2.me/submissions/84eec19e-c068-42f1-b746-736378388cff

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model

set_option autoImplicit false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology HordijkKallenbergLP.SingleLP in
theorem e9645e31_aux_le {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) (y : Pair M → ℝ) (hy : ∀ p, 0 ≤ y p) (j : S) :
    ∑ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * y p
      ≤ stateSum M y j := by
  unfold stateSum
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro p _
  have h1 := M.trans_nonneg p.1.1 p.1.2 j
  have h2 := hy p
  split_ifs <;> nlinarith

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology HordijkKallenbergLP.SingleLP in
theorem e9645e31_aux_pos {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) (x : Pair M → ℝ) (i : S) (h : 0 < stateSum M x i) :
    ∃ a, ∃ ha : a ∈ M.admissible i, 0 < x ⟨(i, a), ha⟩ := by
  unfold stateSum at h
  by_contra hc
  push_neg at hc
  have : ∑ p ∈ Finset.univ.filter (fun p : Pair M => p.1.1 = i), x p ≤ 0 := by
    apply Finset.sum_nonpos
    intro p hp
    obtain ⟨⟨i', a⟩, ha⟩ := p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    subst hp
    exact hc a ha
  linarith


open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology HordijkKallenbergLP.SingleLP in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hz : z ∈ dualFeasible M β) :
    (∀ j : S, β j ≤ stateSum M z.1 j + stateSum M z.2 j) ∧
      ∃ (f : S → A) (hf : ∀ i, f i ∈ M.admissible i), IsSelection M z.1 z.2 f hf := by
  obtain ⟨_, h4, h5⟩ := hz
  have hle : ∀ j : S, β j ≤ stateSum M z.1 j + stateSum M z.2 j := by
    intro j
    have := e9645e31_aux_le M z.2 (fun p => (h5 p).2) j
    have := h4 j
    linarith
  refine ⟨hle, ?_⟩
  have key : ∀ i : S, ∃ a, ∃ ha : a ∈ M.admissible i,
      (i ∈ Ex M z.1 → 0 < z.1 ⟨(i, a), ha⟩) ∧ (i ∉ Ex M z.1 → 0 < z.2 ⟨(i, a), ha⟩) := by
    intro i
    by_cases hi : i ∈ Ex M z.1
    · obtain ⟨a, ha, hpos⟩ := e9645e31_aux_pos M z.1 i hi
      exact ⟨a, ha, fun _ => hpos, fun h => absurd hi h⟩
    · have hx : stateSum M z.1 i ≤ 0 := by
        simp only [Ex, Set.mem_setOf_eq, not_lt] at hi
        exact hi
      have hy : 0 < stateSum M z.2 i := by
        have := hle i
        have := hβpos i
        linarith
      obtain ⟨a, ha, hpos⟩ := e9645e31_aux_pos M z.2 i hy
      exact ⟨a, ha, fun h => absurd h hi, fun _ => hpos⟩
  choose f hf hsel using key
  exact ⟨f, hf, hsel⟩
