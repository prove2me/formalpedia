-- Prove2me | solution 1 for GroundTheory.LocalField.isClassFun_of_mem_spanZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:06:55.531025+00:00
-- url     : https://prove2.me/submissions/11588719-d2b6-43a9-8f62-a6616c6dd2db

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
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
theorem _root_.solution {f : G → ℂ} (hf : f ∈ spanZ E) : IsClassFun f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    exact isClassFun_indFun _ _
  | zero => intro g h; rfl
  | add x y _ _ hx hy => intro g h; simp [hx g h, hy g h]
  | smul n x _ hx => intro g h; simp [hx g h]
end GroundTheory.LocalField
