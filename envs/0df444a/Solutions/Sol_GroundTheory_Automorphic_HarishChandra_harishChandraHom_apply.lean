-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.harishChandraHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:45.111328+00:00
-- url     : https://prove2.me/submissions/2858c560-2cd1-4a6f-81e9-3feb151b7416

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
theorem _root_.solution (z : Subalgebra.center ℂ (U n)) :
    harishChandraHom z = translate (-rhoVec n) (hcProjLin (z : U n)) := rfl
end GroundTheory.Automorphic.HarishChandra
