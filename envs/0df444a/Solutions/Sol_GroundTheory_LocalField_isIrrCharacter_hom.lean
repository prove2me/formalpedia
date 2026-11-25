-- Prove2me | solution 1 for GroundTheory.LocalField.isIrrCharacter_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:07.829071+00:00
-- url     : https://prove2.me/submissions/25435aac-1665-446b-b178-a1bb5f7d9e5d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Theorems.Thm_GroundTheory_LocalField_character_linRep
import Theorems.Thm_GroundTheory_LocalField_isIrrCharacter_character


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
theorem _root_.solution (l : G →* ℂˣ) : IsIrrCharacter (fun g ↦ (l g : ℂ)) := by
  rw [← character_linRep]
  exact isIrrCharacter_character _
end GroundTheory.LocalField
