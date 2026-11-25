-- Prove2me | solution 1 for GroundTheory.LocalField.restrictAb_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:49.316256+00:00
-- url     : https://prove2.me/submissions/1152aa1a-b6b9-479e-9b46-80793fef07be

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_restrictAb_topologicalAbelianizationEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
namespace GroundTheory.LocalField
theorem _root_.solution (E : IntermediateField F Ω) [Normal F E]
    (h : E ≤ maximalAbelianExtension F Ω) : Function.Surjective (restrictAb E h) := by
  intro ρ
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) ρ
  exact ⟨_, restrictAb_topologicalAbelianizationEquiv E h τ⟩
end GroundTheory.LocalField
