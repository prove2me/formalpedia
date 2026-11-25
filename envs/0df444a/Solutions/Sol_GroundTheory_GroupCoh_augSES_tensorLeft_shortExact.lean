-- Prove2me | solution 1 for GroundTheory.GroupCoh.augSES_tensorLeft_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:54:46.620483+00:00
-- url     : https://prove2.me/submissions/2b16b4ab-23e1-4473-ace0-9d22f6791f67

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_GroundTheory_GroupCoh_whiskerLeft_retract
import Theorems.Thm_GroundTheory_GroupCoh_shortExact_map_tensorLeft
import Theorems.Thm_GroundTheory_GroupCoh_augSES_f_retract
import Theorems.Thm_GroundTheory_GroupCoh_augSES_shortExact

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
theorem _root_.solution (A B : Rep.{u} k G) :
    (((augSES k G).obj B).map (tensorLeft A)).ShortExact :=
  shortExact_map_tensorLeft (augSES_shortExact B) A
    (Function.LeftInverse.injective (whiskerLeft_retract _ _ (augSES_f_retract B) A))
end GroundTheory.GroupCoh
