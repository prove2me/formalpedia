-- Prove2me | solution 1 for GroundTheory.LocalField.linRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:19.778846+00:00
-- url     : https://prove2.me/submissions/028031f8-a8c0-42c0-ae39-4ad371687682

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
theorem _root_.solution (l : G →* ℂˣ) (g : G) (z : ℂ) : linRep l g z = (l g : ℂ) * z := rfl
end GroundTheory.LocalField
