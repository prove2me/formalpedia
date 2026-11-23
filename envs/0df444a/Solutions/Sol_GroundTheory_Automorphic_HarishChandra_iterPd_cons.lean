-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.iterPd_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:14.343405+00:00
-- url     : https://prove2.me/submissions/0320e11d-9d48-4044-a8e8-25c3517ef443

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero

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
theorem _root_.solution (a : Fin n × Fin n) (w : List (Fin n × Fin n)) (f : Poly n) :
    iterPd (a :: w) f = pderiv (a.2, a.1) (iterPd w f) := rfl
end GroundTheory.Automorphic.HarishChandra
