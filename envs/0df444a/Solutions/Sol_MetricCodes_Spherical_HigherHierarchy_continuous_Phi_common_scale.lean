-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.continuous_Phi_common_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/2f870e84-b54d-44db-bf02-a46b1c72aa23

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_continuous_scaleCoordinate_factor

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
theorem _root_.solution {j : ℕ}
    (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ) :
    Continuous
      (fun t : ℝ => Phi (scaleAmbient t a) (scaleStabilizer t b)) := by
  unfold Phi scaleAmbient scaleStabilizer
  apply Continuous.sub
  · exact continuous_finsetSum _ fun i _ =>
      MetricCodes.Spherical.sphericalEntropy_continuous.comp
        (continuous_scaleCoordinate_factor (a i))
  · exact continuous_finsetSum _ fun i _ =>
      MetricCodes.Spherical.sphericalEntropy_continuous.comp
        (continuous_scaleCoordinate_factor (b i))
end MetricCodes.Spherical.HigherHierarchy
