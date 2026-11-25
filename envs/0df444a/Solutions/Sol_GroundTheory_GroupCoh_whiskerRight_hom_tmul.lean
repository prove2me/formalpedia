-- Prove2me | solution 1 for GroundTheory.GroupCoh.whiskerRight_hom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:35:14.653702+00:00
-- url     : https://prove2.me/submissions/2647669e-2a18-4035-847b-abef1122884a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES

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
variable {A B : Rep.{u} k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : A ⟶ B) (Y : Rep.{u} k G) (a : A) (y : Y) :
    (f ▷ Y).hom (a ⊗ₜ[k] y : (A ⊗ Y : Rep k G)) = f.hom a ⊗ₜ[k] y := rfl
end GroundTheory.GroupCoh
