-- Prove2me | solution 1 for GroundTheory.GroupCoh.whiskerRight_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:04.85014+00:00
-- url     : https://prove2.me/submissions/3b2a20ac-4c2c-43c7-ba35-e5acd8df31f9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting

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
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A A' B B' : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (φ : A ⟶ A') (a : A) (b : B) :
    (φ ▷ B).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = φ.hom a ⊗ₜ[k] b :=
  rfl
end GroundTheory.GroupCoh
