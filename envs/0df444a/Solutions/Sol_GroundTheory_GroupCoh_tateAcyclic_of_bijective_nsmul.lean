-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_of_bijective_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:54.630125+00:00
-- url     : https://prove2.me/submissions/d9ef5198-a636-4a98-8dc7-a1cc7a3f4469

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_of_sum_eq


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
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) : TateAcyclic M := by
  let f : M.V →ₗ[k] M.V := Fintype.card G • LinearMap.id
  have hf : ∀ m : M, f m = Fintype.card G • m := fun m => rfl
  have hb : Function.Bijective f := by
    have : (f : M → M) = fun m : M => Fintype.card G • m := funext hf
    rw [this]; exact h
  let e := LinearEquiv.ofBijective f hb
  have he : ∀ m : M, Fintype.card G • e.symm m = m := fun m => by
    rw [← hf]; exact e.apply_symm_apply m
  have hc : ∀ (g : G) (x : M), M.ρ g (e.symm x) = e.symm (M.ρ g x) := by
    intro g x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change f (M.ρ g (e.symm x)) = M.ρ g x
    rw [hf, ← map_nsmul, he]
  refine tateAcyclic_of_sum_eq M e.symm.toLinearMap fun m => ?_
  have hg : ∀ g : G, M.ρ g (e.symm.toLinearMap (M.ρ g⁻¹ m)) = e.symm m := fun g => by
    rw [LinearEquiv.coe_coe, hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  rw [Finset.sum_congr rfl fun g _ => hg g, Finset.sum_const, Finset.card_univ, he]
end GroundTheory.GroupCoh
