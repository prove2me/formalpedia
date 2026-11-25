-- Prove2me | solution 1 for GroundTheory.LocalField.IsIrrCharacter.one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:03.685826+00:00
-- url     : https://prove2.me/submissions/0242e56b-cbd2-4841-bb63-5051f1f0a600

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_exists_one

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
universe u
variable {G : Type*} [Group G] [Fintype G]
omit [Fintype G]
namespace GroundTheory.LocalField
namespace IsIrrCharacter
theorem _root_.solution {χ : G → ℂ} (h : IsIrrCharacter χ) : χ 1 ≠ 0 := by
  obtain ⟨n, hn, h1⟩ := h.exists_one
  rw [h1]
  exact Nat.cast_ne_zero.mpr hn.ne'
end IsIrrCharacter
end GroundTheory.LocalField
