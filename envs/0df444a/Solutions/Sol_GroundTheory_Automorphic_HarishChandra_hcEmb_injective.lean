-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.hcEmb_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:10.58588+00:00
-- url     : https://prove2.me/submissions/408bce41-d948-40d9-b56a-137aabf35ea7

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
theorem _root_.solution : Function.Injective (hcEmb (n := n)) :=
  Function.LeftInverse.injective hcProjLin_hcEmb
end GroundTheory.Automorphic.HarishChandra
