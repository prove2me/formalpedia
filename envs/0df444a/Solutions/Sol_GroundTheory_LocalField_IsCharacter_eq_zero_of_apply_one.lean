-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.eq_zero_of_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:35.680801+00:00
-- url     : https://prove2.me/submissions/0db4398b-bb46-4770-8901-53113daa4996

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford

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
theorem _root_.solution {χ : G → ℂ} (h : IsCharacter χ) (h1 : χ 1 = 0) : χ = 0 := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := h
  rw [char_one, Nat.cast_eq_zero, Module.finrank_zero_iff] at h1
  funext g
  have : ρ g = 0 := LinearMap.ext fun v ↦ Subsingleton.elim _ _
  simp [Representation.character, this]
end IsCharacter
end GroundTheory.LocalField
