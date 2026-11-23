-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.perm_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:52.010571+00:00
-- url     : https://prove2.me/submissions/02b0fecc-1c7d-4620-bb39-c8c117cb9a59

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
theorem _root_.solution (w : List (Fin n × Fin n)) :
    w.Perm (expand (Multiset.toFinsupp (w : Multiset _))) := by
  refine Multiset.coe_eq_coe.1 ?_
  ext a
  rw [count_expand, Multiset.toFinsupp_apply]
end GroundTheory.Automorphic.HarishChandra
