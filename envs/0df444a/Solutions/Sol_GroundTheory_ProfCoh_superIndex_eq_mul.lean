-- Prove2me | solution 1 for GroundTheory.ProfCoh.superIndex_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:41.011851+00:00
-- url     : https://prove2.me/submissions/6885beb4-b259-4e54-9bc4-7a24e3b202be

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Theorems.Thm_GroundTheory_ProfCoh_index_sup_normal_eq_mul
import Theorems.Thm_GroundTheory_ProfCoh_index_sup_ne_zero
import Theorems.Thm_GroundTheory_ProfCoh_relIndex_sup_ne_zero
import Theorems.Thm_GroundTheory_ProfCoh_ofNat_index_sup_antitone
import Theorems.Thm_GroundTheory_ProfCoh_ofNat_relIndex_sup_antitone
import Theorems.Thm_GroundTheory_ProfCoh_superRelIndex_eq_iSup
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_iSup_mul_iSup
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_mul


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
theorem _root_.solution [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superIndex K = superIndex H * superRelIndex K H := by
  rw [superRelIndex_eq_iSup hKH, superIndex, superIndex,
    Supernatural.iSup_mul_iSup fun U V =>
      ⟨U ⊓ V, ofNat_index_sup_antitone H inf_le_left, ofNat_relIndex_sup_antitone K H inf_le_right⟩]
  refine iSup_congr fun U => ?_
  rw [index_sup_normal_eq_mul hKH, Supernatural.ofNat_mul (index_sup_ne_zero H U)
    (relIndex_sup_ne_zero K H U)]
end GroundTheory.ProfCoh
