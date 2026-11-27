-- Prove2me | solution 1 for GroundTheory.LocalField.openCompletion.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:43.700944+00:00
-- url     : https://prove2.me/submissions/b712a9fc-8938-40b5-8c12-190520db93e7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_OpenCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
open GroundTheory.LocalField.openCompletion
variable {G}
omit [IsTopologicalGroup G]
namespace GroundTheory.LocalField.openCompletion
theorem _root_.solution {a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)} :
    a ∈ openCompletion G ↔
      ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H' :=
  Iff.rfl
end GroundTheory.LocalField.openCompletion
