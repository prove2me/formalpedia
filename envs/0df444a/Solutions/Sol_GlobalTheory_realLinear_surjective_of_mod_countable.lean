-- Prove2me | solution 1 for GlobalTheory.realLinear_surjective_of_mod_countable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:40.106933+00:00
-- url     : https://prove2.me/submissions/8bdd2ff8-bb9b-4087-a2fe-ea6b197ad85f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_subsingleton_of_countable_realModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
namespace GlobalTheory
theorem _root_.solution (L : M →ₗ[ℝ] N) {Γ : Set N} (hΓ : Γ.Countable)
    (h : ∀ y, ∃ x, y - L x ∈ Γ) : Function.Surjective L := by
  have : Countable Γ := hΓ
  have : Countable (N ⧸ LinearMap.range L) := by
    refine Function.Surjective.countable (f := fun γ : Γ ↦ (LinearMap.range L).mkQ γ) fun q ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨x, hx⟩ := h y
    exact ⟨⟨_, hx⟩, by simp [Submodule.Quotient.mk_eq_zero]⟩
  have := subsingleton_of_countable_realModule (N ⧸ LinearMap.range L)
  exact LinearMap.range_eq_top.1 (Submodule.Quotient.subsingleton_iff.1 this)
end GlobalTheory
