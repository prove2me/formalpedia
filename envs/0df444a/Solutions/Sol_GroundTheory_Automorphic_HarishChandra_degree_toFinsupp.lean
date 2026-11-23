-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.degree_toFinsupp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:39.165778+00:00
-- url     : https://prove2.me/submissions/df34e435-2bbb-486b-bfcb-9148352d925a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_perm_expand
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_length_expand

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
    Finsupp.degree (Multiset.toFinsupp (w : Multiset (Fin n × Fin n))) = w.length := by
  rw [← length_expand]
  exact (perm_expand w).length_eq.symm
end GroundTheory.Automorphic.HarishChandra
