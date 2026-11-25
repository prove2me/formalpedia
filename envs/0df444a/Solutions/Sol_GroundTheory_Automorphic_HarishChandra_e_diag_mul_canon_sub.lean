-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_diag_mul_canon_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:47.130979+00:00
-- url     : https://prove2.me/submissions/bf1f0bf8-a591-4cd5-9f60-da366eaf9205

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_word_sub
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_rootAt_expand

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
theorem _root_.solution (k : Fin n) (m : Fin n × Fin n →₀ ℕ) :
    e (k, k) * canon m - canon m * e (k, k) = (wt m k : ℂ) • canon m := by
  rw [canon, e_diag_mul_word_sub, sum_rootAt_expand]
end GroundTheory.Automorphic.HarishChandra
