-- Prove2me | solution 1 for MetricCodes.ProjectionFamily.sq_trace_le_dimension_mul_trace_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/b0ce75c4-eafd-493d-98ea-ad0de7648949

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
theorem _root_.solution
    (A : Matrix (Fin D) (Fin D) ℝ) :
    (Matrix.trace A) ^ 2 ≤
      (D : ℝ) * Matrix.trace (Aᵀ * A) := by
  classical
  have hdiag :
      (Matrix.trace A) ^ 2 ≤
        (D : ℝ) * ∑ i : Fin D, (A i i) ^ 2 := by
    simpa [Matrix.trace] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin D)))
        (f := fun i : Fin D => A i i))
  have hterm (i : Fin D) :
      (A i i) ^ 2 ≤ ∑ j : Fin D, (A i j) ^ 2 :=
    Finset.single_le_sum
      (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)
  have hsum :
      (∑ i : Fin D, (A i i) ^ 2) ≤
        ∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2 :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have htrace :
      Matrix.trace (Aᵀ * A) =
        ∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.transpose_apply, pow_two]
    rw [Finset.sum_comm]
  calc
    (Matrix.trace A) ^ 2 ≤
        (D : ℝ) * ∑ i : Fin D, (A i i) ^ 2 := hdiag
    _ ≤ (D : ℝ) *
        (∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg D)
    _ = (D : ℝ) * Matrix.trace (Aᵀ * A) := by rw [htrace]
end MetricCodes.ProjectionFamily
