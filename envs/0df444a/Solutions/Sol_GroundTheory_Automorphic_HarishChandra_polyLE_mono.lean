-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.polyLE_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:00.587351+00:00
-- url     : https://prove2.me/submissions/11dab14d-73e8-4beb-9314-f3e3865c4780

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_polyLE

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
theorem _root_.solution {d d' : ℕ} (h : d ≤ d') : polyLE n d ≤ polyLE n d' :=
  fun _ hp => mem_polyLE.2 ((mem_polyLE.1 hp).trans h)
end GroundTheory.Automorphic.HarishChandra
