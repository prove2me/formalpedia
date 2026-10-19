-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_log_vertexDimension_div_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/8de59539-55c1-47ab-b25a-e713a20b7c95

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_log_dimension_div_log_two
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_correctedSignature_antitone
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_correctedSignature_eq
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_correctedSignature_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_correctedSignature_atTop

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
    (ha : ∀ i, 0 < a i) (hanti : StrictAnti a)
    (v : ℕ → Vertex r m) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (Weyl.dimension n (signature a n (v n))) /
          (n : ℝ)) / Real.log 2)
      atTop
      (𝓝 (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i))) := by
  have hcorrected := Weyl.tendsto_log_dimension_div_log_two
    (correctedSignature a v) a ha hanti
    (correctedSignature_antitone a hanti.antitone v)
    (tendsto_correctedSignature_atTop a ha hanti v)
    (tendsto_correctedSignature_ratio a (fun i => (ha i).le) hanti v)
  apply hcorrected.congr'
  filter_upwards [eventually_correctedSignature_eq a
    (fun i => (ha i).le) hanti v] with n hn
  rw [hn]
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
