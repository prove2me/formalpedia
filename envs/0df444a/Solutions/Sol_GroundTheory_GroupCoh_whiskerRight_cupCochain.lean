-- Prove2me | solution 1 for GroundTheory.GroupCoh.whiskerRight_cupCochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:00.833707+00:00
-- url     : https://prove2.me/submissions/ae58e509-d9cc-4e38-8c0d-bcce5b75f02f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Theorems.Thm_GroundTheory_GroupCoh_whiskerRight_tmul

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
theorem _root_.solution (φ : A ⟶ A') (h : p + q = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    (φ ▷ B).hom (cupCochain h f g x) = cupCochain h (fun v => φ.hom (f v)) g x := by
  rw [cupCochain_apply, whiskerRight_tmul, cupCochain_apply]
end GroundTheory.GroupCoh
