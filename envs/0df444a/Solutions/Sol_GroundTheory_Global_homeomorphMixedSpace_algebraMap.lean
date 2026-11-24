-- Prove2me | solution 1 for GroundTheory.Global.homeomorphMixedSpace_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:29:53.79098+00:00
-- url     : https://prove2.me/submissions/f548eaae-a726-4ba9-8a4e-1dc024bec2cd

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
theorem _root_.solution (k : K) :
    homeomorphMixedSpace K (algebraMap K K∞ k) = mixedEmbedding K k := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
end GroundTheory.Global
