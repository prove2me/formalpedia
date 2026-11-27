-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_mem_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:42.149549+00:00
-- url     : https://prove2.me/submissions/c74bc2fa-a358-42fe-b504-fb3cf3fdf8c4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_length_expand
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_filt

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
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) : canon m ∈ filt (n := n) m.degree :=
  word_mem_filt (length_expand m).le
end GroundTheory.Automorphic.HarishChandra
