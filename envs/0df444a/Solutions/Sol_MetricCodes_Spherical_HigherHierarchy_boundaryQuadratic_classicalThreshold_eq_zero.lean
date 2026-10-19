-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.boundaryQuadratic_classicalThreshold_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/4522dcc4-f636-424c-ac86-1ea871572d36

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_classicalThreshold_spectral
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.Spherical.boundaryQuadratic s
      (MetricCodes.classicalThreshold s) = 0 := by
  let a : ℝ := MetricCodes.classicalThreshold s
  have ha : 0 < a := MetricCodes.classicalThreshold_pos hs hs'
  have hden : 0 < 1 + 2 * a := by positivity
  have hroot_sq := Real.sq_sqrt
    (show 0 ≤ a * (1 + a) by positivity)
  have hspectral := MetricCodes.Spherical.classicalThreshold_spectral hs hs'
  change 2 * MetricCodes.Gamma a 0 = s at hspectral
  rw [MetricCodes.Spherical.Gamma_zero ha,
    ← mul_div_assoc, div_eq_iff hden.ne'] at hspectral
  have hmult := congrArg
    (fun x : ℝ => x * Real.sqrt (a * (1 + a))) hspectral
  change MetricCodes.Spherical.boundaryQuadratic s a = 0
  unfold MetricCodes.Spherical.boundaryQuadratic
  nlinarith
end MetricCodes.Spherical.HigherHierarchy
