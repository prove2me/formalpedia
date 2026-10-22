-- Prove2me | solution 1 for LittleCharity.EFX.lemma_4_a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:44:20.262817+00:00
-- url     : https://prove2.me/submissions/e77f1f2a-9ce0-4c7d-8a55-08a944dd02d0

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
set_option autoImplicit false

open LittleCharity.EFX

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hmono : IsMonotoneVal v) (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (g : Fin m) (hg : g ∈ pool X) (i : Fin n)
    (hEFX' : IsEFX v (Function.update X i (insert g (X i)))) :
    let X' := Function.update X i (insert g (X i))
    IsPartialAllocation X' ∧ IsEFX v X' ∧
    welfare v X ≤ welfare v X' ∧
    (pool X').card + 1 = (pool X).card := by
  intro X'
  have hgX : ∀ j, g ∉ X j := by
    intro j hj
    simp only [pool, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and, not_exists] at hg
    exact hg j hj
  refine ⟨?_, hEFX', ?_, ?_⟩
  · intro k l hkl
    by_cases hk : k = i
    · subst hk
      have hl : l ≠ k := hkl.symm
      simp only [X', Function.update_self, Function.update_of_ne hl]
      rw [Finset.disjoint_insert_left]
      exact ⟨hgX l, hX hkl⟩
    · by_cases hl : l = i
      · subst hl
        simp only [X', Function.update_self, Function.update_of_ne hk]
        rw [Finset.disjoint_insert_right]
        exact ⟨hgX k, hX hkl⟩
      · simp only [X', Function.update_of_ne hk, Function.update_of_ne hl]
        exact hX hkl
  · unfold welfare
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only [X', Function.update_self]
      exact hmono j _ _ (Finset.subset_insert _ _)
    · simp only [X', Function.update_of_ne hj]
      exact le_rfl
  · have hpool : pool X' = (pool X).erase g := by
      ext a
      simp only [pool, X', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and,
        not_exists, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · rintro rfl
          have := h i
          simp at this
        · intro j hj
          by_cases hji : j = i
          · subst hji
            have := h j
            simp only [Function.update_self, Finset.mem_insert, not_or] at this
            exact this.2 hj
          · have := h j
            rw [Function.update_of_ne hji] at this
            exact this hj
      · rintro ⟨hne, h⟩ j
        by_cases hji : j = i
        · subst hji
          simp only [Function.update_self, Finset.mem_insert, not_or]
          exact ⟨hne, h j⟩
        · simp only [Function.update_of_ne hji]
          exact h j
    rw [hpool, Finset.card_erase_of_mem hg]
    have : 0 < (pool X).card := Finset.card_pos.2 ⟨g, hg⟩
    omega
