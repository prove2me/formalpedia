-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_entropy_prepend_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/a904e1a0-665a-4d5c-86c2-4468ecb4d1e2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_sphericalEntropy_sub_of_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_scaleCoordinate_sq_div_atTop
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_scaleCoordinate_sq_atTop

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ =>
      MetricCodes.sphericalEntropy u -
        MetricCodes.sphericalEntropy (scaleCoordinate (c ^ 2) u))
      atTop (𝓝 (-Real.logb 2 c)) :=
  CompactificationEntropy.tendsto_sphericalEntropy_sub_of_ratio hc
    (tendsto_scaleCoordinate_sq_atTop hc)
    (tendsto_scaleCoordinate_sq_div_atTop hc)
end MetricCodes.Spherical.HigherHierarchy
