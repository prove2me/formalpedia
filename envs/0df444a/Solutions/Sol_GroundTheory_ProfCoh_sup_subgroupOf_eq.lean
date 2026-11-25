-- Prove2me | solution 1 for GroundTheory.ProfCoh.sup_subgroupOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:38.195126+00:00
-- url     : https://prove2.me/submissions/890cc702-5913-4d7c-b5ae-05a527bd95f9

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
variable {G : Type*} [Group G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {K H U : Subgroup G} [U.Normal] (hKH : K ≤ H) :
    (K ⊔ U).subgroupOf H = K.subgroupOf H ⊔ U.subgroupOf H := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (fun x hx => Subgroup.mem_subgroupOf.mpr ((le_sup_left : K ≤ K ⊔ U) (Subgroup.mem_subgroupOf.mp hx)))
      (fun x hx => Subgroup.mem_subgroupOf.mpr ((le_sup_right : U ≤ K ⊔ U) (Subgroup.mem_subgroupOf.mp hx))))
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨k, hk, u, hu, hku⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hkH : k ∈ H := hKH hk
  have huH : u ∈ H := by
    have := H.mul_mem (H.inv_mem hkH) x.2
    rwa [← hku, inv_mul_cancel_left] at this
  have hx' : x = ⟨k, hkH⟩ * ⟨u, huH⟩ := Subtype.ext hku.symm
  rw [hx']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hk) (Subgroup.mem_subgroupOf.mpr hu)
end GroundTheory.ProfCoh
