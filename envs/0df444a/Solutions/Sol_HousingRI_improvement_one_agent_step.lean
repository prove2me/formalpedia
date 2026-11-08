-- Prove2me | solution 1 for HousingRI.improvement_one_agent_step
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:31:45.09584+00:00
-- url     : https://prove2.me/submissions/15674c4b-2ff6-416f-af0e-4b8f10d8ef5e

import Mathlib
import Definitions.Def_HousingRI_IsStrict
import Definitions.Def_HousingRI_IsImprovement

open HousingRI in
theorem solution {N : Type*} [DecidableEq N] (i j : N) (A Ã : N → N → ℝ)
    (himp : IsImprovement i A Ã) (hji : j ≠ i) :
    IsImprovement i A (Function.update A j (Ã j)) ∧
      IsImprovement i (Function.update A j (Ã j)) Ã ∧
      (IsStrict A → IsStrict Ã → IsStrict (Function.update A j (Ã j))) := by
  have hAj : Function.update A j (Ã j) j = Ã j := Function.update_self _ _ _
  have hAo : ∀ j', j' ≠ j → Function.update A j (Ã j) j' = A j' :=
    fun j' h => Function.update_of_ne h _ _
  obtain ⟨h1, h2, h3, h4⟩ := himp
  have hAi : Function.update A j (Ã j) i = A i := hAo i (Ne.symm hji)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b
    rw [hAi]
  · intro j' hj' k hk
    by_cases h : j' = j
    · rw [h] at hk ⊢
      rw [hAj]
      exact h2 j hji k hk
    · rw [hAo j' h]
      exact ⟨fun e => le_of_eq e.symm, id⟩
  · intro j' hj' k l hk hl hjk hjl
    by_cases h : j' = j
    · rw [h] at hjk hjl ⊢
      rw [hAj]
      exact h3 j hji k l hk hl hjk hjl
    · simp only [hAo j' h]
  · intro j' hj' k hk hle
    by_cases h : j' = j
    · rw [h] at hle ⊢
      rw [hAj] at hle
      exact h4 j hji k hk hle
    · rw [hAo j' h] at hle
      exact hle
  · intro a b
    rw [hAi]
    exact h1 a b
  · intro j' hj' k hk
    by_cases h : j' = j
    · rw [h, hAj]
      exact ⟨fun e => le_of_eq e.symm, id⟩
    · rw [hAo j' h] at hk ⊢
      exact h2 j' hj' k hk
  · intro j' hj' k l hk hl hjk hjl
    by_cases h : j' = j
    · simp only [h, hAj]
    · rw [hAo j' h] at hjk hjl ⊢
      exact h3 j' hj' k l hk hl hjk hjl
  · intro j' hj' k hk hle
    by_cases h : j' = j
    · rw [h] at hle ⊢
      rw [hAj]
      exact hle
    · rw [hAo j' h]
      exact h4 j' hj' k hk hle
  · intro hA hÃ i' a b ha hb hab
    by_cases h : i' = j
    · rw [h] at ha hb ⊢
      rw [hAj] at ha hb ⊢
      exact hÃ j a b ha hb hab
    · rw [hAo i' h] at ha hb ⊢
      exact hA i' a b ha hb hab
