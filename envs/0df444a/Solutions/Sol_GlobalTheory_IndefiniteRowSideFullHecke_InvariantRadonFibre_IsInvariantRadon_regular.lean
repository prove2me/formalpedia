-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon.regular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:17.824988+00:00
-- url     : https://prove2.me/submissions/0da8b37f-eeb6-4fa5-8630-e96d0de21682

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
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon
theorem _root_.solution [LocallyCompactSpace G]
    [SecondCountableTopology G] [IsClosed (H : Set G)] [MeasurableSpace (G ⧸ H)]
    [BorelSpace (G ⧸ H)] {μ : Measure (G ⧸ H)} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon H μ) :
    μ.Regular := by
  haveI := h.finiteOnCompacts
  infer_instance
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon
end GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
