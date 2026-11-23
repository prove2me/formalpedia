-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.iterPd_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:50.7388+00:00
-- url     : https://prove2.me/submissions/e5a34a97-123c-41c8-9fd9-69a4a2cfbdba

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
theorem _root_.solution (f : Poly n) : iterPd [] f = f := rfl
end GroundTheory.Automorphic.HarishChandra
