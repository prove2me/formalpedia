-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.totalDegree_hcProjLin_capelli_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:24.643803+00:00
-- url     : https://prove2.me/submissions/3288a91d-b688-458b-89ff-33a69b98be8b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_capelli_sub_mem

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
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (k : ℕ) :
    (hcProjLin (capelli (n := n) (k + 1)) - psum (Fin n) ℂ (k + 1)).totalDegree < k + 1 :=
  Nat.lt_succ_of_le (mem_polyLE.1 (hcProjLin_capelli_sub_mem k))
end GroundTheory.Automorphic.HarishChandra
