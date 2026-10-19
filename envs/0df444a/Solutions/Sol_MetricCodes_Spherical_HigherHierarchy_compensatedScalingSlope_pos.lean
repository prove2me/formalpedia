-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compensatedScalingSlope_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/9225a5d2-ffad-4897-8f59-906eeef80dae

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_scalingGainCoefficient_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_appendSpectralLossUpper_pos

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
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    0 < compensatedScalingSlope a b := by
  unfold compensatedScalingSlope
  exact div_pos (by linarith [appendSpectralLossUpper_pos h hlast])
    (scalingGainCoefficient_pos h hlast)
end MetricCodes.Spherical.HigherHierarchy
