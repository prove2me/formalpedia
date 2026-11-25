-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_res_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:08.6324+00:00
-- url     : https://prove2.me/submissions/dbcb604b-033a-4893-b8f2-515cba442401

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_res_iff
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {A : Rep.{u} k G} (U V : Subgroup G) [Fintype U] [Fintype V] (g : G)
    (hUV : ∀ x, x ∈ U ↔ g⁻¹ * x * g ∈ V) (hV : TateAcyclic (res V.subtype A)) :
    TateAcyclic (res U.subtype A) := by
  let c : U →* V :=
    { toFun := fun u => ⟨g⁻¹ * u * g, (hUV u).1 u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hinj : Function.Injective c := fun a b hab => by
    have h := congrArg (fun x : V => (x : G)) hab
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  have hsurj : Function.Surjective c := fun v =>
    ⟨⟨g * v * g⁻¹, (hUV _).2 (by simp [mul_assoc])⟩, Subtype.ext (by simp [c, mul_assoc])⟩
  have hc := (tateAcyclic_res_iff c ⟨hinj, hsurj⟩ (res V.subtype A)).2 hV
  let e : A.V ≃ₗ[k] A.V := LinearEquiv.ofLinearMap (A.ρ g⁻¹) (A.ρ g)
    (LinearMap.ext fun a => by simp) (LinearMap.ext fun a => by simp)
  let eqv : (res U.subtype A).ρ.Equiv (res c (res V.subtype A)).ρ :=
    Representation.Equiv.mk e fun u => LinearMap.ext fun a => by
      change A.ρ g⁻¹ (A.ρ u a) = A.ρ (g⁻¹ * u * g) (A.ρ g⁻¹ a)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc,
        mul_inv_cancel, mul_one]
  exact hc.of_iso (Rep.mkIso eqv)
end GroundTheory.GroupCoh
