-- Prove2me | solution 1 for GroundTheory.ProfCoh.ofNat_index_sup_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:42.874718+00:00
-- url     : https://prove2.me/submissions/fd1c24fc-1bec-41c0-81b7-ab33612683fb

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Theorems.Thm_GroundTheory_ProfCoh_index_sup_ne_zero
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
theorem _root_.solution (H : Subgroup G) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Supernatural.ofNat (H ⊔ (V : Subgroup G)).index ≤
      Supernatural.ofNat (H ⊔ (U : Subgroup G)).index := by
  rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (index_sup_ne_zero H V)
    (index_sup_ne_zero H U)]
  exact Subgroup.index_dvd_of_le (sup_le_sup_left (fun x hx => h hx) H)
end GroundTheory.ProfCoh
