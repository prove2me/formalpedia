-- Prove2me | solution 1 for OAI.ThorpCompatibility.prescribed_permutation_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:29:42.785481+00:00
-- url     : https://prove2.me/submissions/6ee4e48d-481f-4908-9b38-fd2024f199ef

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/PermutationCount.lean:L8-L33
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.prescribed_permutation_card. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling

-- ---- from OAI.Probability.ThorpCompatibility.PermutationCount ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma prescribed_permutation_card {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (σ : Equiv.Perm α) :
    (Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = σ x)).card =
      (Fintype.card α - s.card).factorial := by
  classical
  have hs : Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = σ x) =
      (permsOfFinset sᶜ).image (fun π => σ * π) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨σ⁻¹ * τ, ?_, by simp⟩
      rw [mem_perms_of_finset_iff]
      intro x hx
      simp only [Finset.mem_compl]
      intro hxs
      apply hx
      simp [Equiv.Perm.mul_apply, h x hxs]
    · rintro ⟨π, hπ, rfl⟩ x hx
      have he : π x = x := by
        by_contra he
        have := mem_perms_of_finset_iff.mp hπ he
        simp [hx] at this
      simp [Equiv.Perm.mul_apply, he]
  rw [hs, Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel h),
    card_perms_of_finset, Finset.card_compl]

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (σ : Equiv.Perm α) :
    (Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = σ x)).card =
      (Fintype.card α - s.card).factorial := by
  first
    | exact OAI.ThorpCompatibility.prescribed_permutation_card s σ
    | exact OAI.ThorpCompatibility.prescribed_permutation_card
    | (apply OAI.ThorpCompatibility.prescribed_permutation_card <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.prescribed_permutation_card <;> assumption)
