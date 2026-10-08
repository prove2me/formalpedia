-- Prove2me | solution 1 for KallenbergLP.AverageLP.proposition_4_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:12:51.654982+00:00
-- url     : https://prove2.me/submissions/d033fb75-ffda-482e-8ba1-40a7747dbe1d

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

set_option autoImplicit false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter KallenbergLP.AverageLP in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    IsClosedUnder (Pf M f) (Ex M z.1) := by
  intro i hi j hj
  obtain ⟨⟨h1, _h2, h3⟩, _⟩ := hopt
  have hx : 0 < z.1 ⟨(i, f i), hf i⟩ := (hsel i).1 hi
  have hj' : ¬ 0 < stateSum M z.1 j := hj
  have e : stateSum M z.1 j = ∑ p : Pair M, if p.1.1 = j then z.1 p else 0 := by
    unfold stateSum; rw [Finset.sum_filter]
  have hsum : ∑ p : Pair M, M.trans p.1.1 p.1.2 j * z.1 p = stateSum M z.1 j := by
    have h := h1 j
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul] at h
    rw [e]; linarith
  have hle : M.trans i (f i) j * z.1 ⟨(i, f i), hf i⟩
      ≤ ∑ p : Pair M, M.trans p.1.1 p.1.2 j * z.1 p :=
    Finset.single_le_sum (f := fun p : Pair M => M.trans p.1.1 p.1.2 j * z.1 p)
      (fun p _ => mul_nonneg (M.trans_nonneg _ _ _) (h3 p).1)
      (Finset.mem_univ (⟨(i, f i), hf i⟩ : Pair M))
  show M.trans i (f i) j = 0
  have h0 := M.trans_nonneg i (f i) j
  by_contra hne
  have : 0 < M.trans i (f i) j * z.1 ⟨(i, f i), hf i⟩ :=
    mul_pos (lt_of_le_of_ne h0 (Ne.symm hne)) hx
  linarith [not_lt.mp hj']
