-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mem_of_mem_support_toFinsupp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:45.307659+00:00
-- url     : https://prove2.me/submissions/bb85542f-cb70-4083-9c2b-787e8fbf2668

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp

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
theorem _root_.solution {w : List (Fin n × Fin n)} {a : Fin n × Fin n}
    (ha : a ∈ (Multiset.toFinsupp (w : Multiset _)).support) : a ∈ w := by
  rw [Multiset.toFinsupp_support, Multiset.mem_toFinset] at ha
  exact Multiset.mem_coe.1 ha
end GroundTheory.Automorphic.HarishChandra
