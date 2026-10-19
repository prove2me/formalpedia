-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.spectralAtom_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/ae4e1647-bddf-4180-b0a2-8cce9a68fdcc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) :
    spectralAtom u < (1 / 2 : ℝ) := by
  have hrad : 0 ≤ u * (1 + u) := by positivity
  have hroot : 0 ≤ Real.sqrt (u * (1 + u)) := Real.sqrt_nonneg _
  have hlinear : 0 < 1 + 2 * u := by positivity
  have hsquare := Real.sq_sqrt hrad
  have hgap :
      (2 * Real.sqrt (u * (1 + u))) ^ 2 < (1 + 2 * u) ^ 2 := by
    nlinarith
  unfold spectralAtom quadraticCoordinate
  apply (div_lt_iff₀ hlinear).mpr
  nlinarith
end MetricCodes.Spherical.HigherHierarchy
