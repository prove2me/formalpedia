-- Prove2me | solution 1 for LittleCharity.EFX.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:03:25.327427+00:00
-- url     : https://prove2.me/submissions/066cd024-81be-4ce8-b107-a97be9e1f11a

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

open LittleCharity.EFX

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hmono : IsMonotoneVal v) (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (hEFX : IsEFX v X)
    (hU1 : ∃ k, v k (X k) < v k (pool X))
    (i : Fin n) (Z : Finset (Fin m))
    (hZ : IsMinimalEnviedSubset v X (pool X) Z)
    (hi : v i (X i) < v i Z) :
    let X' := Function.update X i Z
    IsPartialAllocation X' ∧ IsEFX v X' ∧
    welfare v X < welfare v X' ∧
    pool X' = X i ∪ (pool X \ Z) := by
  intro X'
  obtain ⟨hZpool, _, hZmin⟩ := hZ
  have hZdisj : ∀ k, Disjoint Z (X k) := by
    intro k
    rw [Finset.disjoint_left]
    intro x hxZ hxk
    have := hZpool hxZ
    unfold pool at this
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and, not_exists] at this
    exact this k hxk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a = i
    · subst ha
      have hb : b ≠ a := fun h => hab h.symm
      simp only [X', Function.update_self, Function.update_of_ne hb]
      exact hZdisj b
    · by_cases hb : b = i
      · subst hb
        simp only [X', Function.update_self, Function.update_of_ne ha]
        exact (hZdisj a).symm
      · simp only [X', Function.update_of_ne ha, Function.update_of_ne hb]
        exact hX hab
  · intro a b g' hg'
    by_cases hb : b = i
    · subst hb
      simp only [X', Function.update_self] at hg' ⊢
      by_cases ha : a = b
      · subst ha
        simp only [Function.update_self]
        exact hmono a _ _ (Finset.erase_subset _ _)
      · rw [Function.update_of_ne ha]
        exact hZmin _ (Finset.erase_ssubset hg') a
    · simp only [X', Function.update_of_ne hb] at hg' ⊢
      by_cases ha : a = i
      · subst ha
        simp only [Function.update_self]
        have := hEFX a b g' hg'
        linarith
      · rw [Function.update_of_ne ha]
        exact hEFX a b g' hg'
  · unfold welfare
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : j = i
      · subst hj
        simp only [X', Function.update_self]
        exact hi.le
      · simp only [X', Function.update_of_ne hj]
        exact le_rfl
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      simp only [X', Function.update_self]
      exact hi
  · ext x
    unfold pool
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and, not_exists,
      Finset.mem_union, X']
    constructor
    · intro h
      by_cases hxi : x ∈ X i
      · exact Or.inl hxi
      · right
        refine ⟨fun k hk => ?_, ?_⟩
        · by_cases hki : k = i
          · subst hki; exact hxi hk
          · exact h k (by rw [Function.update_of_ne hki]; exact hk)
        · intro hxZ; exact h i (by simpa using hxZ)
    · rintro (hxi | ⟨hk, hxZ⟩)
      · intro k hk
        by_cases hki : k = i
        · subst hki
          simp only [Function.update_self] at hk
          exact (Finset.disjoint_left.1 (hZdisj k) hk) hxi
        · rw [Function.update_of_ne hki] at hk
          exact (Finset.disjoint_left.1 (hX (Ne.symm hki)) hxi) hk
      · intro k hk'
        by_cases hki : k = i
        · subst hki
          simp only [Function.update_self] at hk'
          exact hxZ hk'
        · rw [Function.update_of_ne hki] at hk'
          exact hk k hk'
