-- Prove2me | solution 1 for MetricCodes.ProjectionFamily.sum_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/3a3325c6-5a7f-4d7e-8f75-71b4454404fe

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open MetricCodes.ProjectionFamily
variable {X : Type*} {D d : ℕ}
namespace MetricCodes.ProjectionFamily
theorem _root_.solution (P : ProjectionFamily X D d)
    (C : Finset X) :
    (∑ x ∈ C, P.projection x)ᵀ =
      ∑ x ∈ C, P.projection x := by
  classical
  ext i j
  simp only [Matrix.transpose_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  have h := congrFun (congrFun (P.symmetric x) i) j
  simpa [Matrix.transpose_apply] using h
end MetricCodes.ProjectionFamily
