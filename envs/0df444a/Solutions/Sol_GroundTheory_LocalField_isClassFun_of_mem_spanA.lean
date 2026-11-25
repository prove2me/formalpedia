-- Prove2me | solution 1 for GroundTheory.LocalField.isClassFun_of_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:43:28.56437+00:00
-- url     : https://prove2.me/submissions/7f021709-ac75-42af-ae55-e7dd1e252987

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_isClassFun_of_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
variable {G : Type*} [Group G] [Fintype G]
variable (E : Subgroup G → Prop)
variable {E}
namespace GroundTheory.LocalField
theorem _root_.solution {ζ : ℂ} {f : G → ℂ} (hf : f ∈ spanA E ζ) : IsClassFun f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, g, hg, rfl⟩ := hx
    intro s t
    simp [isClassFun_of_mem_spanZ hg s t]
  | zero => intro g h; rfl
  | add x y _ _ hx hy => intro g h; simp [hx g h, hy g h]
  | smul n x _ hx => intro g h; simp [hx g h]
end GroundTheory.LocalField
