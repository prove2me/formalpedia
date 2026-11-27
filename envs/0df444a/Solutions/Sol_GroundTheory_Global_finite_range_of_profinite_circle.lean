-- Prove2me | solution 1 for GroundTheory.Global.finite_range_of_profinite_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:41.56589+00:00
-- url     : https://prove2.me/submissions/84abc2ed-9d10-42e5-95ed-3855388ccf30

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Theorems.Thm_GroundTheory_Global_Circle_noSmallSubgroups
import Theorems.Thm_GroundTheory_Global_finite_range_of_profinite

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
    Finite f.range :=
  finite_range_of_profinite Circle.noSmallSubgroups f hf
end GroundTheory.Global
