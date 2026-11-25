-- Prove2me | solution 1 for GroundTheory.GroupCoh.augSES_f_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:54:20.791025+00:00
-- url     : https://prove2.me/submissions/bbd67760-3e83-4b75-8cf0-58aa0f0470ff

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_GroundTheory_GroupCoh_whiskerRight_retract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (X : Rep.{u} k G) (t : (augIdeal k G ⊗ X : Rep k G)) :
    LinearMap.rTensor X.V (augIdealRetract k G) (((augSES k G).obj X).f.hom t) = t :=
  whiskerRight_retract _ _ augIdealRetract_ι X t
end GroundTheory.GroupCoh
