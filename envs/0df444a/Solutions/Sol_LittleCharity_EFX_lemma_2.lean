-- Prove2me | solution 1 for LittleCharity.EFX.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:01:38.042221+00:00
-- url     : https://prove2.me/submissions/ceb6da70-4fd5-498f-a3a3-c787ef9a0ea2

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

open LittleCharity.EFX

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X)
    (c : List (Fin n)) (hc : c.Nodup) (hne : c ≠ [])
    (hcycle : ∀ a ∈ c, Envies v X a (c.formPerm a)) :
    IsPartialAllocation (X ∘ c.formPerm) ∧
    pool (X ∘ c.formPerm) = pool X ∧
    (IsEFX v X → IsEFX v (X ∘ c.formPerm)) ∧
    welfare v X < welfare v (X ∘ c.formPerm) := by
  set σ := c.formPerm with hσ
  have hfix : ∀ i, i ∉ c → σ i = i := fun i hi => List.formPerm_apply_of_notMem hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hX (fun h => hij (σ.injective h))
  · unfold pool
    congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨σ i, hi⟩
    · rintro ⟨j, hj⟩; exact ⟨σ.symm j, by simpa using hj⟩
  · intro hE i j g hg
    have hg' : g ∈ X (σ j) := hg
    have h1 := hE i (σ j) g hg'
    by_cases hi : i ∈ c
    · have := hcycle i hi
      unfold Envies at this
      show v i ((X (σ j)).erase g) ≤ v i (X (σ i))
      linarith
    · show v i ((X (σ j)).erase g) ≤ v i (X (σ i))
      rw [hfix i hi]; exact h1
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil c hne
    unfold welfare
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i ∈ c
      · have := hcycle i hi
        unfold Envies at this
        show v i (X i) ≤ v i (X (σ i))
        exact this.le
      · show v i (X i) ≤ v i (X (σ i))
        rw [hfix i hi]
    · refine ⟨a, Finset.mem_univ _, ?_⟩
      have := hcycle a ha
      unfold Envies at this
      exact this
