-- Prove2me | solution 1 for GroundTheory.Global.sub_mem_range_cycSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:35.65826+00:00
-- url     : https://prove2.me/submissions/6c52122b-7b00-487f-96fa-042ad1cd0899

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply


attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {G M : Type*} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) {σ : G}
namespace GroundTheory.Global
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (g : G) (x : M) :
    ρ g x - x ∈ (cycSub ρ σ).range := by
  let S : Subgroup G :=
    { carrier := {g | ∀ x, ρ g x - x ∈ (cycSub ρ σ).range}
      one_mem' := fun x => by simp
      mul_mem' := fun {a b} ha hb x => by
        have : ρ (a * b) x - x = (ρ a (ρ b x) - ρ b x) + (ρ b x - x) := by
          rw [map_mul, Module.End.mul_apply]; abel
        rw [this]
        exact add_mem (ha _) (hb _)
      inv_mem' := fun {a} ha x => by
        have : ρ a⁻¹ x - x = -(ρ a (ρ a⁻¹ x) - ρ a⁻¹ x) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
          abel
        rw [this]
        exact neg_mem (ha _) }
  have hσS : σ ∈ S := fun x => ⟨x, rfl⟩
  have : Subgroup.zpowers σ ≤ S := (Subgroup.zpowers_le).2 hσS
  exact this (hσ g) x
end GroundTheory.Global
