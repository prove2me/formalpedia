-- Prove2me | solution 2 for GroundTheory.GroupCoh.rightUnitor_cupCochain_oneCochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:19.679816+00:00
-- url     : https://prove2.me/submissions/f9b155ce-40bc-4f13-a8de-99df3ca66c6a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Theorems.Thm_GroundTheory_GroupCoh_rightUnitor_hom_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupₗ_apply
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : (Fin p → G) → A) (x : Fin p → G) :
    (ρ_ A).hom.hom (cupCochain (add_zero p) f oneCochain x) = f x := by
  simp only [cupCochain_apply, oneCochain]
  rw [rightUnitor_hom_tmul]
  exact one_smul k _
end GroundTheory.GroupCoh
