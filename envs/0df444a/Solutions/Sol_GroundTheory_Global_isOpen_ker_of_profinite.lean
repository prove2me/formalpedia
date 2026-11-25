-- Prove2me | solution 1 for GroundTheory.Global.isOpen_ker_of_profinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:35.992893+00:00
-- url     : https://prove2.me/submissions/2df81c4a-868a-47c0-ba3d-f9252252f66f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Theorems.Thm_GroundTheory_Global_isOpen_ker_of_noSmallSubgroups
import Theorems.Thm_GroundTheory_Global_exists_openSubgroup_subset_of_profinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Topology Filter
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Global
theorem _root_.solution (hH : NoSmallSubgroups H) (f : G →* H) (hf : Continuous f) :
    IsOpen (f.ker : Set G) :=
  isOpen_ker_of_noSmallSubgroups (fun _ hW ↦ exists_openSubgroup_subset_of_profinite hW) hH f hf
end GroundTheory.Global
