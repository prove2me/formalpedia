-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_log_dimensionSum_div_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/18f43693-d4b7-40b3-a989-220b1a859b49

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_log_vertexDimension_div_log_two
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_vertexDimension_pos_all
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_log_finset_sum_div_log_two_of_eventually_pos

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
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hanti : StrictAnti a) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (dimensionSum (m := m) a n) / (n : ℝ)) / Real.log 2)
      atTop
      (𝓝 (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i))) := by
  apply tendsto_log_finset_sum_div_log_two_of_eventually_pos
    (fun v n => vertexDimension a n v)
    (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i))
    (eventually_vertexDimension_pos_all a ha hanti)
  intro v
  exact tendsto_log_vertexDimension_div_log_two a ha hanti (fun _ => v)
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
