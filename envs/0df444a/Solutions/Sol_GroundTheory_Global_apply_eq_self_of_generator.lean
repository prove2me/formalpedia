-- Prove2me | solution 1 for GroundTheory.Global.apply_eq_self_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:08.468807+00:00
-- url     : https://prove2.me/submissions/fa6e19ec-0526-4aed-9447-b20bd1dda3f7

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
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : V} (hx : ρ σ x = x) (g : G) : ρ g x = x := by
  have := hσ g
  rw [Subgroup.zpowers_eq_closure] at this
  induction this using Subgroup.closure_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy, hx]
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul, Module.End.mul_apply, hb, ha]
  | inv a _ ha =>
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
end GroundTheory.Global
