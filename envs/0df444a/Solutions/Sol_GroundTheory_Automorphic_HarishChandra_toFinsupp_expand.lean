-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.toFinsupp_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:06.55862+00:00
-- url     : https://prove2.me/submissions/28e63a2b-9044-45e2-b142-683261c4203c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_count_expand

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
    Multiset.toFinsupp ((expand m : List _) : Multiset _) = m := by
  ext a
  rw [Multiset.toFinsupp_apply, count_expand]
end GroundTheory.Automorphic.HarishChandra
