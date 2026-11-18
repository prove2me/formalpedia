-- Prove2me | solution 1 for Kyprianou.Ch06.properOverlapFirstMarkWitnessFollowsWinningClock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:15:19.162542+00:00
-- url     : https://prove2.me/submissions/b3313c48-77fa-466f-b623-630c857eef61

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstMarkWitnessFollowsEarlierCompetingClock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (A C : Set E)
    (firstMark : Option E) (tauB : WithTop NNReal)
    (hFinite : tauB ≠ ⊤)
    (hBefore : tauB < sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u (A \ C)}))
    (hTau : sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A}) =
      min tauB (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u (A \ C)})))
    (hInitD : N omega 0 (A \ C) = 0)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega (tauB.untopD 0) (S ∪ T) =
        N omega (tauB.untopD 0) S +
          N omega (tauB.untopD 0) T)
    (hWitness : ∃ x : E,
      firstMark = some x ∧ x ∈ A ∧
      0 < N omega ((sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})).untopD 0) ({x} : Set E)) :
    firstMark ∈ (some '' (A ∩ C)) := by
  have hTauEq : sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A}) = tauB := by
    rw [hTau, min_eq_left (le_of_lt hBefore)]
  rcases hWitness with ⟨x, hMark, hxA, hPositive⟩
  have hUnion : (A ∩ C) ∪ (A \ C) = A := by
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  have hxSplit : x ∈ (A ∩ C) ∪ (A \ C) := by
    simpa only [hUnion] using hxA
  have hPositiveB : 0 < N omega (tauB.untopD 0) ({x} : Set E) := by
    simpa only [hTauEq] using hPositive
  exact Kyprianou.Ch06.firstMarkWitnessFollowsEarlierCompetingClock
    N omega (A ∩ C) (A \ C) firstMark tauB
    hFinite hBefore hInitD hAdd ⟨x, hMark, hxSplit, hPositiveB⟩
