-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:51.886208+00:00
-- url     : https://prove2.me/submissions/317b2462-d564-499e-b5df-573dd8235f7a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters

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
variable {G : Type*} [Group G]
namespace GroundTheory.LocalField
namespace IsCharacter
theorem _root_.solution {χ ψ : G → ℂ} (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    IsCharacter (χ * ψ) := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  obtain ⟨W, _, _, _, σ, rfl⟩ := hψ
  exact ⟨TensorProduct ℂ V W, inferInstance, inferInstance, inferInstance, ρ.tprod σ, char_tensor ρ σ⟩
end IsCharacter
end GroundTheory.LocalField
