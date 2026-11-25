-- Prove2me | solution 1 for GroundTheory.LocalField.character_linRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:49:05.102871+00:00
-- url     : https://prove2.me/submissions/98c2a0e8-b6c5-4237-8823-c13ec007d0fb

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
theorem _root_.solution (l : G →* ℂˣ) : (linRep l).character = fun g ↦ (l g : ℂ) := by
  funext g
  simp [Representation.character, linRep]
end GroundTheory.LocalField
