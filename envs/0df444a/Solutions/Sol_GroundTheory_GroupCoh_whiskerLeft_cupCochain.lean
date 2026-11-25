-- Prove2me | solution 1 for GroundTheory.GroupCoh.whiskerLeft_cupCochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:43:59.339433+00:00
-- url     : https://prove2.me/submissions/379dda07-a08d-415c-a65d-4b331664a14e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Theorems.Thm_GroundTheory_GroupCoh_whiskerLeft_tmul

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
theorem _root_.solution (ψ : B ⟶ B') (h : p + q = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    (A ◁ ψ).hom (cupCochain h f g x) = cupCochain h f (fun v => ψ.hom (g v)) x := by
  rw [cupCochain_apply, whiskerLeft_tmul, cupCochain_apply, Rep.hom_comm_apply]
end GroundTheory.GroupCoh
