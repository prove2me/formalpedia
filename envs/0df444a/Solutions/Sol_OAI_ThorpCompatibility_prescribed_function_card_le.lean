-- Prove2me | solution 1 for OAI.ThorpCompatibility.prescribed_function_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:31:15.300184+00:00
-- url     : https://prove2.me/submissions/bc0bb01e-70a2-4b35-9886-bc4aa4937dd5

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/PermutationCount.lean:L35-L54
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.prescribed_function_card_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Theorems.Thm_OAI_ThorpCompatibility_prescribed_permutation_card

-- ---- from OAI.Probability.ThorpCompatibility.PermutationCount ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma prescribed_function_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → α) :
    (Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x)).card ≤
      (Fintype.card α - s.card).factorial := by
  classical
  by_cases h : ∃ σ : Equiv.Perm α, ∀ x ∈ s, σ x = f x
  · obtain ⟨σ, hσ⟩ := h
    have he : Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x) =
        Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = σ x) := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro h x hx
      · rw [h x hx, hσ x hx]
      · rw [h x hx, hσ x hx]
    rw [he, prescribed_permutation_card]
  · have he : Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro τ _ hτ
      exact h ⟨τ, hτ⟩
    simp [he]

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → α) :
    (Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x)).card ≤
      (Fintype.card α - s.card).factorial := by
  first
    | exact OAI.ThorpCompatibility.prescribed_function_card_le s f
    | exact OAI.ThorpCompatibility.prescribed_function_card_le
    | (apply OAI.ThorpCompatibility.prescribed_function_card_le <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.prescribed_function_card_le <;> assumption)
