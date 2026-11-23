-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.geDeg_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:48.282221+00:00
-- url     : https://prove2.me/submissions/82168959-c403-4fbb-a013-b7acf3471793

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
theorem _root_.solution {t t' : ℕ} (h : t' ≤ t) : (geDeg t : Submodule ℂ (Poly n)) ≤ geDeg t' :=
  fun _ hf s hs => hf s (lt_of_lt_of_le hs h)
end GroundTheory.Automorphic.HarishChandra
