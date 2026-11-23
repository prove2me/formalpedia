-- Prove2me | solution 1 for GroundTheory.Global.homeomorphMixedSpace_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:51.057409+00:00
-- url     : https://prove2.me/submissions/e13c8d7b-2024-46f6-b88c-dbfbaa5249a6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice

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
theorem _root_.solution (x : K∞) :
    homeomorphMixedSpace K x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl
end GroundTheory.Global
