-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.map_left_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:12:36.155799+00:00
-- url     : https://prove2.me/submissions/da0ff0c1-a171-411d-a606-e64174163154

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_mem_fix
import Theorems.Thm_GlobalTheory_BCT_DimFac_contractRight_map
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_contractRight_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.BCT.DimFac
theorem _root_.solution {σ : Representation ℂ Γ W} {L : Subgroup Γ} {t : W ⊗[ℂ] M}
    (ht : ∀ g ∈ L, TensorProduct.map (σ g) LinearMap.id t = t) (p : W →ₗ[ℂ] W) (hp : ∀ x ∈ fixed σ L, p x = x) :
    TensorProduct.map p LinearMap.id t = t := by
  by_contra h
  obtain ⟨l, hl⟩ := exists_contractRight_ne_zero (sub_ne_zero.2 h)
  apply hl
  rw [map_sub, contractRight_map, LinearMap.comp_id, hp, sub_self]
  refine mem_fix.2 fun g hg => ?_
  conv_rhs => rw [← ht g hg, contractRight_map, LinearMap.comp_id]
end GlobalTheory.BCT.DimFac
