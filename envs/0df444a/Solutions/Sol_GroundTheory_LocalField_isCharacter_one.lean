-- Prove2me | solution 1 for GroundTheory.LocalField.isCharacter_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:31.636803+00:00
-- url     : https://prove2.me/submissions/77c2a6b2-9c12-428d-9639-ab068ff2ad18

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
theorem _root_.solution : IsCharacter (1 : G → ℂ) := by
  refine ⟨ℂ, inferInstance, inferInstance, inferInstance, Representation.trivial ℂ G ℂ, ?_⟩
  funext g
  simp [Representation.character, Representation.trivial]
end GroundTheory.LocalField
