-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.constantVector_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/58906937-72a2-48a9-9924-11f457b4a23e

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
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxPerron
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
namespace MetricCodes.Spherical.HigherHierarchyBoxPerron
theorem _root_.solution (r m : ℕ) :
    constantVector r m ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun x : HigherHierarchyFinitePerron.Space (BoxVertex r m) =>
    x (fun _ => 0)) hzero
  simpa [constantVector] using h
end MetricCodes.Spherical.HigherHierarchyBoxPerron
