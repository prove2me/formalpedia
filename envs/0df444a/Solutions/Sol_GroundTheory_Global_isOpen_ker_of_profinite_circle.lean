-- Prove2me | solution 1 for GroundTheory.Global.isOpen_ker_of_profinite_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:37.276306+00:00
-- url     : https://prove2.me/submissions/ac976e1b-7ecf-4181-b61b-442ff9da779f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Theorems.Thm_GroundTheory_Global_Circle_noSmallSubgroups
import Theorems.Thm_GroundTheory_Global_isOpen_ker_of_profinite

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
theorem _root_.solution (f : G →* Circle) (hf : Continuous f) :
    IsOpen (f.ker : Set G) :=
  isOpen_ker_of_profinite Circle.noSmallSubgroups f hf
end GroundTheory.Global
