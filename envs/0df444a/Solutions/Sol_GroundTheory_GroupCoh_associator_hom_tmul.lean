-- Prove2me | solution 1 for GroundTheory.GroupCoh.associator_hom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:52.569796+00:00
-- url     : https://prove2.me/submissions/53a200f8-84ef-4fca-9074-8559450fed92

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (X Y Z : Rep k G) (a : X) (b : Y) (c : Z) :
    (α_ X Y Z).hom.hom (((a ⊗ₜ[k] b : (X ⊗ Y : Rep k G)) ⊗ₜ[k] c : ((X ⊗ Y) ⊗ Z : Rep k G))) =
      a ⊗ₜ[k] (b ⊗ₜ[k] c) :=
  rfl
end GroundTheory.GroupCoh
