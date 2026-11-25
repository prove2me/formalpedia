-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.map_right_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:01:32.374799+00:00
-- url     : https://prove2.me/submissions/b443022c-3faa-433f-a27f-400629f70c1b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_mem_fix
import Theorems.Thm_GlobalTheory_BCT_DimFac_contractLeft_map
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_contractLeft_ne_zero


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
theorem _root_.solution {τ : Representation ℂ Γ M} {L : Subgroup Γ} {t : W ⊗[ℂ] M}
    (ht : ∀ g ∈ L, TensorProduct.map LinearMap.id (τ g) t = t) (p : M →ₗ[ℂ] M) (hp : ∀ x ∈ fixed τ L, p x = x) :
    TensorProduct.map LinearMap.id p t = t := by
  by_contra h
  obtain ⟨l, hl⟩ := exists_contractLeft_ne_zero (sub_ne_zero.2 h)
  apply hl
  rw [map_sub, contractLeft_map, LinearMap.comp_id, hp, sub_self]
  refine mem_fix.2 fun g hg => ?_
  conv_rhs => rw [← ht g hg, contractLeft_map, LinearMap.comp_id]
end GlobalTheory.BCT.DimFac
