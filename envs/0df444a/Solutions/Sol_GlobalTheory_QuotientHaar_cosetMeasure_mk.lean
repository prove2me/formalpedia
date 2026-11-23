-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.cosetMeasure_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:29.744103+00:00
-- url     : https://prove2.me/submissions/8ac71902-7a8d-45f7-805c-68f33030b4be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.QuotientHaar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
namespace GlobalTheory.QuotientHaar
theorem _root_.solution (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) :
    cosetMeasure H ν (g : G ⧸ H) = ν.map (fun h : H => g * (h : G)) := rfl
end GlobalTheory.QuotientHaar
