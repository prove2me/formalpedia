-- Prove2me | solution 1 for GroundTheory.LocalField.isAbelianGalois_of_le_maximalAbelianExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:28.06181+00:00
-- url     : https://prove2.me/submissions/80e57324-aa44-4abb-8903-d32f8fb361c6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_restrictAb_surjective

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
    (h : E ≤ maximalAbelianExtension F Ω) : IsAbelianGalois F E := by
  have : IsGalois F E :=
    have := Algebra.isSeparable_tower_bot_of_isSeparable F E Ω
    IsGalois.mk
  refine { toIsMulCommutative := ⟨⟨fun σ τ => ?_⟩⟩ }
  obtain ⟨σ', rfl⟩ := restrictAb_surjective E h σ
  obtain ⟨τ', rfl⟩ := restrictAb_surjective E h τ
  rw [← map_mul, ← map_mul, mul_comm' σ' τ']
end GroundTheory.LocalField
