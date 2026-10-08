-- Prove2me | solution 1 for KallenbergLP.AverageLP.proposition_4_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:41:19.678988+00:00
-- url     : https://prove2.me/submissions/c66f2dbd-16e6-4683-ab03-4c7af140011c

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
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hopt : IsDualOptimal M β z) :
    IsClosedUnder (weightMatrix M (dualPolicyWeight M z.1 z.2)) (Ex M z.1) := by
  intro i hi j hj
  obtain ⟨⟨h1, _h2, h3⟩, _⟩ := hopt
  have hi' : 0 < stateSum M z.1 i := hi
  have hj' : ¬ 0 < stateSum M z.1 j := hj
  have e : stateSum M z.1 j = ∑ p : Pair M, if p.1.1 = j then z.1 p else 0 := by
    unfold stateSum; rw [Finset.sum_filter]
  have hsum : ∑ p : Pair M, M.trans p.1.1 p.1.2 j * z.1 p = stateSum M z.1 j := by
    have h := h1 j
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul] at h
    rw [e]; linarith
  have key : ∀ a (ha : a ∈ M.admissible i), M.trans i a j * z.1 ⟨(i, a), ha⟩ = 0 := by
    intro a ha
    have hle : M.trans i a j * z.1 ⟨(i, a), ha⟩
        ≤ ∑ p : Pair M, M.trans p.1.1 p.1.2 j * z.1 p :=
      Finset.single_le_sum (f := fun p : Pair M => M.trans p.1.1 p.1.2 j * z.1 p)
        (fun p _ => mul_nonneg (M.trans_nonneg _ _ _) (h3 p).1)
        (Finset.mem_univ (⟨(i, a), ha⟩ : Pair M))
    have h0 : 0 ≤ M.trans i a j * z.1 ⟨(i, a), ha⟩ :=
      mul_nonneg (M.trans_nonneg _ _ _) (h3 _).1
    linarith [not_lt.mp hj']
  show ∑ a ∈ M.admissible i, dualPolicyWeight M z.1 z.2 i a * M.trans i a j = 0
  apply Finset.sum_eq_zero
  intro a ha
  have hw : dualPolicyWeight M z.1 z.2 i a = z.1 ⟨(i, a), ha⟩ / stateSum M z.1 i := by
    unfold dualPolicyWeight
    simp only [dif_pos ha, if_pos hi']
  rw [hw]
  calc z.1 ⟨(i, a), ha⟩ / stateSum M z.1 i * M.trans i a j
      = (M.trans i a j * z.1 ⟨(i, a), ha⟩) / stateSum M z.1 i := by ring
    _ = 0 := by rw [key a ha, zero_div]
