-- Prove2me | solution 1 for GroundTheory.ProfCoh.inf_sup_normal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:53.781619+00:00
-- url     : https://prove2.me/submissions/8a3c3206-63a5-40c0-937c-7c8c71cee038

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
theorem _root_.solution {X H U : Subgroup G} [U.Normal] (hUX : U ≤ X) :
    X ⊓ (H ⊔ U) = (X ⊓ H) ⊔ U := by
  refine le_antisymm (fun x hx => ?_) (sup_le (inf_le_inf_left _ le_sup_left) (le_inf hUX le_sup_right))
  obtain ⟨hxX, hxHU⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨h, hh, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxHU
  have hhX : h ∈ X := by
    have := X.mul_mem hxX (X.inv_mem (hUX hu))
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hhX, hh⟩) hu
end GroundTheory.ProfCoh
