-- Prove2me | solution 2 for GroundTheory.Global.finite_range_of_profinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:26:32.5458+00:00
-- url     : https://prove2.me/submissions/d459cb06-b74a-4842-ad68-3153125fecc7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
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
theorem _root_.solution (hH : NoSmallSubgroups H) (f : G →* H) (hf : Continuous f) :
    Finite f.range :=
  have : Finite (G ⧸ f.ker) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_ker_of_profinite hH f hf)
  Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange f).toEquiv
end GroundTheory.Global
