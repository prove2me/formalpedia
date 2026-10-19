-- Prove2me | solution 1 for MetricCodes.ProjectionFamily.card_mul_rank_sq_le_dimension_mul_sum_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/e8c864e6-3291-4a6a-8e0b-66f0e47fcabc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_ProjectionFamily_sq_trace_le_dimension_mul_trace_sq
import Theorems.Thm_MetricCodes_ProjectionFamily_sum_symmetric
import Theorems.Thm_MetricCodes_ProjectionFamily_sum_overlap_eq_trace_mul_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open MetricCodes.ProjectionFamily
variable {X : Type*} {D d : ℕ}
namespace MetricCodes.ProjectionFamily
theorem _root_.solution
    (P : ProjectionFamily X D d) (C : Finset X) :
    ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
      (D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) := by
  classical
  let A : Matrix (Fin D) (Fin D) ℝ :=
    ∑ x ∈ C, P.projection x
  have htrace : Matrix.trace A = (C.card : ℝ) * (d : ℝ) := by
    dsimp [A]
    simp [Matrix.trace_sum, P.trace_eq]
  have hsym : Aᵀ = A := P.sum_symmetric C
  have hcs := sq_trace_le_dimension_mul_trace_sq A
  rw [htrace, hsym, ← P.sum_overlap_eq_trace_mul_sum C] at hcs
  exact hcs
end MetricCodes.ProjectionFamily
