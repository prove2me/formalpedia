-- Prove2me | solution 1 for GroundTheory.GroupCoh.moduleIso_hom_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:46.261634+00:00
-- url     : https://prove2.me/submissions/043cf8e1-bcae-4c77-9e66-2485128ae04c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift

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
theorem _root_.solution {M N : ModuleCat.{u} k} (e : M ≅ N) : Function.Injective e.hom.hom :=
  fun x y h => by
    have := congrArg e.inv.hom h
    rwa [e.hom_inv_id_apply, e.hom_inv_id_apply] at this
end GroundTheory.GroupCoh
