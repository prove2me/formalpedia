-- Prove2me | solution 1 for GroundTheory.ProfCoh.index_sup_normal_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:16.799159+00:00
-- url     : https://prove2.me/submissions/f3a00c1c-9f13-4f18-b4f5-9347300e1a53

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Theorems.Thm_GroundTheory_ProfCoh_relIndex_sup_normal_eq

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
theorem _root_.solution {K H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hKH : K ≤ H) :
    (K ⊔ U).index = (H ⊔ U).index * (K ⊔ U).relIndex H := by
  rw [← Subgroup.relIndex_mul_index (sup_le_sup_right hKH U),
    relIndex_sup_normal_eq (le_sup_right : U ≤ K ⊔ U), mul_comm]
end GroundTheory.ProfCoh
