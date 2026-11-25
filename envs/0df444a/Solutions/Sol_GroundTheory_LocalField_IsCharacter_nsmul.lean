-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:52.799825+00:00
-- url     : https://prove2.me/submissions/ceebb408-1962-46af-9a0d-c97ef92dd7c9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_isCharacter_zero
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
variable {G : Type*} [Group G]
namespace GroundTheory.LocalField
namespace IsCharacter
theorem _root_.solution {χ : G → ℂ} (hχ : IsCharacter χ) (n : ℕ) : IsCharacter (n • χ) := by
  induction n with
  | zero => simpa using isCharacter_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add hχ
end IsCharacter
end GroundTheory.LocalField
