-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.boundaryDegree_spectral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/a45b68ac-945f-4daa-b9ba-c678c883e2f3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Gamma_eq_sub
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_mul_one_add

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
    {s a : ℝ} (ha : 0 < a)
    (hquadratic : 0 ≤ MetricCodes.Spherical.boundaryQuadratic s a) :
    2 * MetricCodes.Gamma a
      (MetricCodes.Spherical.boundaryDegree s a) = s := by
  have hden : 0 <
      (1 + 2 * a) * Real.sqrt (a * (1 + a)) := by positivity
  have hroot := MetricCodes.Spherical.boundaryDegree_mul_one_add hquadratic
  rw [MetricCodes.Gamma_eq_sub, ← mul_div_assoc,
    div_eq_iff hden.ne']
  unfold MetricCodes.Spherical.boundaryQuadratic at hroot
  nlinarith
end MetricCodes.Spherical.HigherHierarchy
