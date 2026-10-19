-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_edgeWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/1b4ae470-6987-4b5b-863d-d6e533302fd1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_tendsto_flooredCoordinates_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_signature_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_actualEdgeWeight_of_ratios

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) (v : Vertex r m) (i : Fin (r + 1)) :
    Tendsto (fun n : ℕ => edgeWeight a b n v i)
      atTop (𝓝 (lagrangeWeight a b i * spectralAtom (a i))) := by
  apply tendsto_actualEdgeWeight_of_ratios a b h
    (fun n => signature a n v) (flooredCoordinates b)
  · intro j
    exact tendsto_signature_ratio a (fun _ => v) j
      (h.ambient_nonneg j)
  · intro j
    exact tendsto_flooredCoordinates_ratio b j
      (h.stabilizer_pos j).le
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
