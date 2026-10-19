-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.operator_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/5b683cd2-0264-4ba7-858f-70849712807d

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
open Metric
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherHierarchyFinitePerron
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
namespace MetricCodes.Spherical.HigherHierarchyFinitePerron
theorem _root_.solution (A : Matrix I I ℝ)
    (hA : Aᵀ = A) : (operator A).IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrArg (fun B : Matrix I I ℝ => B i j) hA
  simpa using h
end MetricCodes.Spherical.HigherHierarchyFinitePerron
