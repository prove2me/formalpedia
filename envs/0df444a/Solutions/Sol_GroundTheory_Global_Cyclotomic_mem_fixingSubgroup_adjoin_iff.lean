-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.mem_fixingSubgroup_adjoin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:14.593583+00:00
-- url     : https://prove2.me/submissions/4215c912-0d02-4c1f-80c1-e9a224f7da91

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (S : Set E) (σ : Gal(E/F)) :
    σ ∈ (adjoin F S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h x hx => h x (subset_adjoin F S hx), fun h x hx => ?_⟩
  have := adjoin_algHom_ext F (φ₁ := (σ : E →ₐ[F] E).comp (adjoin F S).val)
    (φ₂ := (adjoin F S).val) (fun y hy => h y hy)
  exact congrArg (fun φ : adjoin F S →ₐ[F] E => φ ⟨x, hx⟩) this
end GroundTheory.Global.Cyclotomic
