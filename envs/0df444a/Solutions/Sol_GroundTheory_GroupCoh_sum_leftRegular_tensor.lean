-- Prove2me | solution 1 for GroundTheory.GroupCoh.sum_leftRegular_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:47.717827+00:00
-- url     : https://prove2.me/submissions/241eec18-6235-4468-8052-6f38647c1329

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Theorems.Thm_GroundTheory_GroupCoh_coeffOneProj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep MonoidalCategory
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (B : Rep.{u} k G)
namespace GroundTheory.GroupCoh
theorem _root_.solution (t : (leftRegular k G ⊗ B : Rep k G)) :
    ∑ g : G, (leftRegular k G ⊗ B).ρ g
      (TensorProduct.map coeffOneProj LinearMap.id ((leftRegular k G ⊗ B).ρ g⁻¹ t)) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | tmul x b =>
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib, hx, hy]
    | single h c =>
      rw [Fintype.sum_eq_single h]
      · simp [Rep.tensor_ρ, coeffOneProj_apply]
      · intro g hg
        have : g⁻¹ * h ≠ 1 := fun e => hg (inv_mul_eq_one.mp e)
        simp [Rep.tensor_ρ, coeffOneProj_apply, this]
end GroundTheory.GroupCoh
