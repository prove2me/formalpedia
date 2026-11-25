-- Prove2me | solution 1 for GroundTheory.ProfCoh.ofNat_relIndex_sup_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:43.649297+00:00
-- url     : https://prove2.me/submissions/db38f1e2-c3c6-48a1-bac9-ee97e9e69042

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Theorems.Thm_GroundTheory_ProfCoh_relIndex_sup_ne_zero
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_dvd_iff_le
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_dvd_ofNat


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
variable [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (K H : Subgroup G) {U V : OpenNormalSubgroup G}
    (h : U ≤ V) :
    Supernatural.ofNat ((K ⊔ (V : Subgroup G)).relIndex H) ≤
      Supernatural.ofNat ((K ⊔ (U : Subgroup G)).relIndex H) := by
  rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (relIndex_sup_ne_zero K H V)
    (relIndex_sup_ne_zero K H U)]
  exact Subgroup.relIndex_dvd_of_le_left H (sup_le_sup_left (fun x hx => h hx) K)
end GroundTheory.ProfCoh
