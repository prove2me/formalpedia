-- Prove2me | solution 1 for LittleCharity.EFX.lemma_4_b
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:02:38.325199+00:00
-- url     : https://prove2.me/submissions/f9e17dff-403e-41e3-98c0-f9e68edb036e

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

open LittleCharity.EFX

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hmono : IsMonotoneVal v) (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (hEFX : IsEFX v X)
    (hU0 : ¬ U0Applicable v X) :
    ∀ s, IsSource v X s → ∀ g ∈ pool X,
      (∃ j, j ≠ s ∧ v j (X j) < v j (insert g (X s))) ∧
      (∀ Z, IsMinimalEnviedSubset v X (insert g (X s)) Z →
        Z.card ≤ (X s).card) := by
  intro s hs g hg
  have hgX : ∀ k, g ∉ X k := by
    intro k hk
    unfold pool at hg
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and, not_exists] at hg
    exact hg k hk
  have hnoEFX : ¬ IsEFX v (Function.update X s (insert g (X s))) := fun h => hU0 ⟨g, hg, s, h⟩
  have hsub : ∀ i, v i (X i) ≤ v i (insert g (X i)) := fun i => hmono i _ _ (Finset.subset_insert _ _)
  refine ⟨?_, ?_⟩
  · unfold IsEFX at hnoEFX
    push Not at hnoEFX
    obtain ⟨i, j, g', hg', hviol⟩ := hnoEFX
    by_cases hj : j = s
    · subst hj
      simp only [Function.update_self] at hg' hviol
      by_cases hi : i = j
      · subst hi
        simp only [Function.update_self] at hviol
        have := hmono i ((insert g (X i)).erase g') (insert g (X i)) (Finset.erase_subset _ _)
        linarith
      · rw [Function.update_of_ne hi] at hviol
        refine ⟨i, hi, ?_⟩
        have := hmono i ((insert g (X j)).erase g') (insert g (X j)) (Finset.erase_subset _ _)
        linarith
    · rw [Function.update_of_ne hj] at hg' hviol
      by_cases hi : i = s
      · subst hi
        simp only [Function.update_self] at hviol
        have h1 := hEFX i j g' hg'
        have h2 := hsub i
        linarith
      · rw [Function.update_of_ne hi] at hviol
        have := hEFX i j g' hg'
        linarith
  · intro Z hZ
    obtain ⟨hZsub, _, hZmin⟩ := hZ
    by_cases hgZ : g ∈ Z
    · -- Z.erase g ⊆ X s, and it is a proper subset
      have hsubX : Z.erase g ⊆ X s := by
        intro x hx
        have hxZ := Finset.mem_of_mem_erase hx
        have hxne := Finset.ne_of_mem_erase hx
        have := hZsub hxZ
        rcases Finset.mem_insert.1 this with h | h
        · exact absurd h hxne
        · exact h
      have hne : Z.erase g ≠ X s := by
        intro heq
        apply hnoEFX
        have hZeq : Z = insert g (X s) := by
          rw [← heq]; exact (Finset.insert_erase hgZ).symm
        intro i j g' hg'
        by_cases hj : j = s
        · subst hj
          simp only [Function.update_self] at hg' ⊢
          by_cases hi : i = j
          · subst hi
            simp only [Function.update_self]
            have hss : (insert g (X i)).erase g' ⊂ Z := by
              rw [hZeq]; exact Finset.erase_ssubset hg'
            exact le_trans (hZmin _ hss i) (hsub i)
          · rw [Function.update_of_ne hi]
            have hss : (insert g (X j)).erase g' ⊂ Z := by
              rw [hZeq]; exact Finset.erase_ssubset hg'
            exact hZmin _ hss i
        · rw [Function.update_of_ne hj] at hg' ⊢
          by_cases hi : i = s
          · subst hi
            simp only [Function.update_self]
            exact le_trans (hEFX i j g' hg') (hsub i)
          · rw [Function.update_of_ne hi]
            exact hEFX i j g' hg'
      have hss : Z.erase g ⊂ X s := lt_of_le_of_ne hsubX hne
      have := Finset.card_lt_card hss
      have hc := Finset.card_erase_add_one hgZ
      omega
    · have : Z ⊆ X s := by
        intro x hx
        have := hZsub hx
        rcases Finset.mem_insert.1 this with h | h
        · exact absurd (h ▸ hx) hgZ
        · exact h
      exact Finset.card_le_card this
