-- Prove2me | solution 1 for GroundTheory.GroupCoh.injective_whiskerLeft_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:49:18.039564+00:00
-- url     : https://prove2.me/submissions/8bea3e3a-d937-41c1-9516-14edff1db312

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_GroundTheory_GroupCoh_whiskerLeft_hom_eq_lTensor

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
variable (V : Rep.{u} k G) [Module.Flat k V.V] {X₁ X₂ : Rep.{u} k G} (f : X₁ ⟶ X₂)
namespace GroundTheory.GroupCoh
theorem _root_.solution (hf : Function.Injective f.hom) :
    Function.Injective (V ◁ f).hom := by
  intro s t hst
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := V.V) f.hom.toLinearMap hf
  rw [← whiskerLeft_hom_eq_lTensor, ← whiskerLeft_hom_eq_lTensor, hst]
end GroundTheory.GroupCoh
