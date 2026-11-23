-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:06.434602+00:00
-- url     : https://prove2.me/submissions/bca051f7-a438-435c-859f-2323273085aa

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
theorem _root_.solution (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    fibreIntegral H ν f (g : G ⧸ H) = ∫⁻ h : H, f (g * h) ∂ν := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
