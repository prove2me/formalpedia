-- Prove2me | solution 2 for GroundTheory.GroupCoh.leftUnitor_oneCochain_cupCochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:10.268338+00:00
-- url     : https://prove2.me/submissions/be0ab61f-a3c2-4843-915d-f328a3930be6

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Theorems.Thm_GroundTheory_GroupCoh_partialProd_mk_zero
import Theorems.Thm_GroundTheory_GroupCoh_leftUnitor_hom_tmul
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
theorem _root_.solution (f : (Fin q → G) → A) (x : Fin q → G) :
    (λ_ A).hom.hom (cupCochain (zero_add q) oneCochain f x) = f x := by
  simp only [cupCochain_apply, oneCochain, partialProd_mk_zero, map_one, Module.End.one_apply]
  rw [leftUnitor_hom_tmul, one_smul]
  exact congrArg f (funext fun j => congrArg x (Fin.ext (zero_add _)))
end GroundTheory.GroupCoh
