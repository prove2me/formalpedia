-- Prove2me | solution 1 for GlobalTheory.BorelCoh.exists_equivariant_proj_of_irreducible_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:29:49.719804+00:00
-- url     : https://prove2.me/submissions/de9287d9-cf2d-4f9a-88e5-e75d8e735b22

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_BasicForm
import Definitions.Def_PositivityTheory_AutomorphicForms_PublishedInputs_BorelInjectivity_EquivariantProjections_ExistsEquivariantProjOfLeSumIrreducible
import Theorems.Thm_GlobalTheory_BorelCoh_exists_equivariant_proj_of_le_sum_irreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BorelCoh CategoryTheory
open scoped ContDiff Matrix
open GlobalTheory GlobalTheory.BorelCoh
namespace GlobalTheory.BorelCoh
theorem _root_.solution : ∀ (M O ι : Type) [AddCommGroup M] [Module ℂ M] [Fintype ι] [DecidableEq ι] (act : O → Module.End ℂ M) (V : ι → Submodule ℂ M), (∀ i o, ∀ x ∈ V i, act o x ∈ V i) → (∀ i, V i ≠ ⊥) → (∀ i (W : Submodule ℂ M), W ≤ V i → (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V i) → (∀ i j, i ≠ j → ∀ f : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ V i, f (act o x) = act o (f x)) → (∀ x ∈ V i, f x ∈ V j) → ∀ x ∈ V i, f x = 0) → ∀ i, ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧ (∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p x ∈ V i) ∧ (∀ x ∈ V i, p x = x) ∧ ∀ j, j ≠ i → ∀ x ∈ V j, p x = 0 := by
  intro M O ι _ _ _ _ act V h1 h2 h3 h4 i
  have hirr : ∀ j, V j ≤ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) := fun j =>
    le_iSup₂_of_le (f := fun (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W) => W) (V j) ⟨h1 j, h2 j, h3 j⟩ le_rfl
  obtain ⟨p, hpe, hpV, hpid⟩ := exists_equivariant_proj_of_le_sum_irreducible act (V i) (h1 i) (hirr i)
  exact ⟨p, hpe, fun x _ => hpV x, hpid,
    fun j hji x hx => h4 j i hji p (fun o y hy => hpe o y (hirr j hy)) (fun y _ => hpV y) x hx⟩
end GlobalTheory.BorelCoh
