-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.cosetMeasure_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:57.090781+00:00
-- url     : https://prove2.me/submissions/bcdc4e66-fc41-466c-9177-2d8ca2c1a2ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Theorems.Thm_GlobalTheory_QuotientHaar_cosetMeasure_mk

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
theorem _root_.solution (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) {s : Set G}
    (hs : MeasurableSet s) :
    cosetMeasure H ν (g : G ⧸ H) s = ν ((fun h : H => g * (h : G)) ⁻¹' s) := by
  rw [cosetMeasure_mk, Measure.map_apply (measurable_translate H g) hs]
end GlobalTheory.QuotientHaar
