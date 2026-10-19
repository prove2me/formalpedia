-- Prove2me | solution 1 for MetricCodes.ProjectionFamily.sum_overlap_eq_trace_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/c5109f6d-99ff-4176-9039-9f9b3b4f2a86

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
    (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) =
      Matrix.trace
        ((∑ x ∈ C, P.projection x) *
          (∑ y ∈ C, P.projection y)) := by
  classical
  simp only [overlap, Matrix.trace_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
end MetricCodes.ProjectionFamily
