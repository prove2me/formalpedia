-- Prove2me | solution 1 for GroundTheory.Automorphic.isCompact_inf_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:38.092954+00:00
-- url     : https://prove2.me/submissions/f3800976-049c-4be3-a73e-6dc225dca4ec

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution {K L : OpenSubgroup G} (hK : IsCompact (K : Set G)) :
    IsCompact ((K ⊓ L : OpenSubgroup G) : Set G) := by
  rw [OpenSubgroup.coe_inf]
  exact hK.inter_right L.isClosed
end GroundTheory.Automorphic
