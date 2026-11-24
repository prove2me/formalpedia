-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.continuous_invCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:40:10.846973+00:00
-- url     : https://prove2.me/submissions/d9faa0c8-1803-45d2-b6a0-b3ae2a89d4bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
omit [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
theorem _root_.solution : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H) := by
  refine continuous_quot_lift _ ?_
  exact continuous_quot_mk.comp continuous_inv
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
end GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
