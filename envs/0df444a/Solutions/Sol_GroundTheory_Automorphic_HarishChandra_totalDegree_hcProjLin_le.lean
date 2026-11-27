-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.totalDegree_hcProjLin_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:27.377556+00:00
-- url     : https://prove2.me/submissions/cbc2bba0-a609-4885-9de8-c6feb27f7300

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_mem_polyLE

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
theorem _root_.solution {d : ℕ} {u : U n} (hu : u ∈ filt d) :
    (hcProjLin u).totalDegree ≤ d :=
  mem_polyLE.1 (hcProjLin_mem_polyLE hu)
end GroundTheory.Automorphic.HarishChandra
