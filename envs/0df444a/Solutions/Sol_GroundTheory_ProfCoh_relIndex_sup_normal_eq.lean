-- Prove2me | solution 1 for GroundTheory.ProfCoh.relIndex_sup_normal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:17.660667+00:00
-- url     : https://prove2.me/submissions/2c80488f-f2c8-4db0-b1ef-5feb47821274

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Theorems.Thm_GroundTheory_ProfCoh_inf_sup_normal_eq

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
theorem _root_.solution {X H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hUX : U ≤ X) :
    X.relIndex (H ⊔ U) = X.relIndex H := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex U X (H ⊔ U)
  have h2 := Subgroup.relIndex_inf_mul_relIndex U X H
  rw [inf_eq_left.mpr hUX, Subgroup.relIndex_sup_right, inf_sup_normal_eq hUX,
    Subgroup.relIndex_sup_right] at h1
  rw [inf_eq_left.mpr hUX] at h2
  have hne : U.relIndex (X ⊓ H) ≠ 0 := fun h0 =>
    Subgroup.FiniteIndex.index_ne_zero (H := U)
      (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_index_of_normal U (X ⊓ H)))
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (h1.trans h2.symm)
end GroundTheory.ProfCoh
