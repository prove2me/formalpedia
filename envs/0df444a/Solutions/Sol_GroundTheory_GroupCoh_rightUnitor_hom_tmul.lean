-- Prove2me | solution 1 for GroundTheory.GroupCoh.rightUnitor_hom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:42.516111+00:00
-- url     : https://prove2.me/submissions/36c5958f-8612-4138-87b4-fd51322d2b7c

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
theorem _root_.solution (X : Rep k G) (a : X) (c : k) :
    (ρ_ X).hom.hom ((a ⊗ₜ[k] c : (X ⊗ 𝟙_ (Rep k G) : Rep k G))) = c • a :=
  rfl
end GroundTheory.GroupCoh
