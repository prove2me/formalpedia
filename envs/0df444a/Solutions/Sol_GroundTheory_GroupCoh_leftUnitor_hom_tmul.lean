-- Prove2me | solution 1 for GroundTheory.GroupCoh.leftUnitor_hom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:47:30.376064+00:00
-- url     : https://prove2.me/submissions/559e8fd8-1b4a-4f76-bcba-f7b07329bbd3

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
theorem _root_.solution (X : Rep k G) (c : k) (a : X) :
    (λ_ X).hom.hom ((c ⊗ₜ[k] a : (𝟙_ (Rep k G) ⊗ X : Rep k G))) = c • a :=
  rfl
end GroundTheory.GroupCoh
