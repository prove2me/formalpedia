-- Prove2me | solution 1 for MetricCodes.ProjectionFamily.overlap_eq_trace_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/ff47f9bb-42e5-41fd-b064-50e10a3dcf25

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
theorem _root_.solution (P : ProjectionFamily X D d) (x y : X) :
    P.overlap x y =
      Matrix.trace
        ((P.projection x * P.projection y)ᴴ *
          (P.projection x * P.projection y)) := by
  unfold overlap
  rw [Matrix.conjTranspose_mul,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    P.symmetric x, P.symmetric y]
  symm
  calc
    Matrix.trace
        ((P.projection y * P.projection x) *
          (P.projection x * P.projection y)) =
        Matrix.trace
          ((P.projection y * (P.projection x * P.projection x)) *
            P.projection y) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace
          ((P.projection y * P.projection x) * P.projection y) := by
          rw [P.idempotent x]
    _ = Matrix.trace
          (P.projection y * (P.projection x * P.projection y)) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.trace
          ((P.projection x * P.projection y) * P.projection y) := by
          exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (P.projection x * (P.projection y * P.projection y)) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.trace (P.projection x * P.projection y) := by
          rw [P.idempotent y]
end MetricCodes.ProjectionFamily
