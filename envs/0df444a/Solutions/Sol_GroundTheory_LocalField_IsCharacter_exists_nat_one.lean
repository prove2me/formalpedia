-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.exists_nat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:38.059019+00:00
-- url     : https://prove2.me/submissions/b7c4e214-0bdb-4ab0-81a4-ff2ab17c35f5

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
theorem _root_.solution {χ : G → ℂ} (h : IsCharacter χ) : ∃ n : ℕ, χ 1 = n := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := h
  exact ⟨finrank ℂ V, char_one ρ⟩
end IsCharacter
end GroundTheory.LocalField
