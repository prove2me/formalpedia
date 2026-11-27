-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mem_support_of_mem_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:29.419801+00:00
-- url     : https://prove2.me/submissions/48d28c7f-c78a-47ef-8e15-459b39384721

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
theorem _root_.solution {m : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n}
    (ha : a ∈ expand m) : a ∈ m.support := by
  rw [Finsupp.mem_support_iff, ← count_expand]
  exact (Multiset.count_pos.2 (Multiset.mem_coe.2 ha)).ne'
end GroundTheory.Automorphic.HarishChandra
