-- Prove2me | solution 1 for GroundTheory.LocalField.mem_irrChars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:44.642474+00:00
-- url     : https://prove2.me/submissions/8fe37dbd-7bc7-46c0-964f-715a0886c4e9

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
universe u
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution {χ : G → ℂ} : χ ∈ irrChars G ↔ IsIrrCharacter χ := by
  simp [irrChars]
end GroundTheory.LocalField
