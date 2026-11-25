-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mem_centralizerT_of_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:37.205815+00:00
-- url     : https://prove2.me/submissions/4b55398d-5180-4e2f-ad1c-af5c6670af4a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection

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
theorem _root_.solution {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    z ∈ centralizerT n :=
  Subalgebra.center_le_centralizer ℂ (cartanSet n) hz
end GroundTheory.Automorphic.HarishChandra
