-- Prove2me | solution 1 for GroundTheory.LocalField.openCompletion.apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:19.694638+00:00
-- url     : https://prove2.me/submissions/63983777-0dae-42d9-9b84-65459f0bee0b

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
theorem _root_.solution (a : openCompletion G) {H H' : openFiniteIndex G} (h : (H : Subgroup G) ≤ H') :
    quotientMapOfLE h ((a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H) =
      (a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H' :=
  a.2 H H' h
end GroundTheory.LocalField.openCompletion
