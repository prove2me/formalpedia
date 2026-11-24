-- Prove2me | solution 1 for GroundTheory.Global.homeomorphMixedSpace_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:30:36.442419+00:00
-- url     : https://prove2.me/submissions/7de3e3c1-a89e-4dd7-b2f3-e8c0951abf1b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]
namespace GroundTheory.Global
theorem _root_.solution (x y : K∞) :
    homeomorphMixedSpace K (x - y) = homeomorphMixedSpace K x - homeomorphMixedSpace K y := by
  simp only [homeomorphMixedSpace_apply, map_sub]
end GroundTheory.Global
