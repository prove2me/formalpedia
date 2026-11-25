-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:45.938852+00:00
-- url     : https://prove2.me/submissions/920352cc-1341-4ae0-a46b-8a03515b8b66

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_flatMap_replicate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) :
    canon m = ((letters n).map fun a => e a ^ m a).prod :=
  word_flatMap_replicate _ _
end GroundTheory.Automorphic.HarishChandra
