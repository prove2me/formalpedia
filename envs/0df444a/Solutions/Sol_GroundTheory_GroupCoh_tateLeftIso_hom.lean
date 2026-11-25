-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateLeftIso_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:10:30.410868+00:00
-- url     : https://prove2.me/submissions/4c690498-c230-49bb-8d8d-34479d769e29

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorRight_shortExact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A B : Rep.{u} k G) (r : ℤ) :
    (tateLeftIso A B r).hom = tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl := rfl
end GroundTheory.GroupCoh
