-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.spectralAtom_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/bbe28dfd-73c2-455d-ad85-74ea0f55a77d

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
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) :
    spectralAtom u ^ 2 =
      quadraticCoordinate u / (1 + 4 * quadraticCoordinate u) := by
  have hrad : 0 ≤ quadraticCoordinate u := by
    unfold quadraticCoordinate
    positivity
  have hlin : 0 < 1 + 2 * u := by positivity
  have hsquare := Real.sq_sqrt hrad
  unfold spectralAtom
  rw [div_pow, hsquare]
  unfold quadraticCoordinate at *
  field_simp [hlin.ne']
  ring
end MetricCodes.Spherical.HigherHierarchy
