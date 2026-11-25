-- Prove2me | solution 1 for GroundTheory.GroupCoh.whiskerLeft_hom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:49:33.292171+00:00
-- url     : https://prove2.me/submissions/c2c11446-3674-4280-9465-d6abacc7a088

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
theorem _root_.solution (Y : Rep.{u} k G) (f : A ⟶ B) (y : Y) (a : A) :
    (Y ◁ f).hom (y ⊗ₜ[k] a : (Y ⊗ A : Rep k G)) = y ⊗ₜ[k] f.hom a := rfl
end GroundTheory.GroupCoh
