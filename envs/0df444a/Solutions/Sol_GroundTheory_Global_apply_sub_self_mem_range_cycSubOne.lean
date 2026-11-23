-- Prove2me | solution 1 for GroundTheory.Global.apply_sub_self_mem_range_cycSubOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:22.774155+00:00
-- url     : https://prove2.me/submissions/e7028d8c-d4bd-47da-9e8e-bee46e3220f5

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
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



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
namespace GroundTheory.Global
theorem _root_.solution (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (g : G) (x : V) :
    ρ g x - x ∈ (cycSubOne ρ σ).range := by
  have := hσ g
  rw [Subgroup.zpowers_eq_closure] at this
  induction this using Subgroup.closure_induction generalizing x with
  | mem y hy =>
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨x, rfl⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have : ρ (a * b) x - x = (ρ a (ρ b x) - ρ b x) + (ρ b x - x) := by
      rw [map_mul, Module.End.mul_apply]; abel
    rw [this]
    exact add_mem (ha _) (hb _)
  | inv a _ ha =>
    have : ρ a⁻¹ x - x = -(ρ a (ρ a⁻¹ x) - ρ a⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      abel
    rw [this]
    exact neg_mem (ha _)
end GroundTheory.Global
