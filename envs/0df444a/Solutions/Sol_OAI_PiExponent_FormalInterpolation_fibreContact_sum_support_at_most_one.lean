-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_sum_support_at_most_one
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:50:56.447229+00:00
-- url     : https://prove2.me/submissions/d0d69b1e-37d0-4450-8223-801194be2f1f

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution {K : Nat} (a : Fin K → Nat)
    (hexclusive : ∀ j k : Fin K, j ≠ k →
      ¬ (0 < a j ∧ 0 < a k)) :
    (∑ j : Fin K, a j) = 0 ∨
      ∃ j : Fin K, (∑ k : Fin K, a k) = a j := by
  classical
  by_cases hsum : (∑ j : Fin K, a j) = 0
  · exact Or.inl hsum
  · right
    have hexists : ∃ j : Fin K, 0 < a j := by
      by_contra h
      have hzero : ∀ j : Fin K, a j = 0 := by
        intro j
        have hn : ¬ 0 < a j := by
          intro hp
          exact h ⟨j, hp⟩
        omega
      have htotal : (∑ j : Fin K, a j) = 0 := by
        simp [hzero]
      exact hsum htotal
    obtain ⟨j, hj⟩ := hexists
    refine ⟨j, ?_⟩
    apply Finset.sum_eq_single j
    · intro k hk hkj
      have hnot := hexclusive j k (Ne.symm hkj)
      by_contra hne
      have hpk : 0 < a k := by omega
      exact hnot ⟨hj, hpk⟩
    · intro hmem
      simp at hmem