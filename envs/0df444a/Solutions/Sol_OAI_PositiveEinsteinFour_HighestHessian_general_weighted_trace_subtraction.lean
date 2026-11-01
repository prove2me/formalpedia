-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:43:15.011513+00:00
-- url     : https://prove2.me/submissions/23760a78-671a-48f3-9442-11c0dc8836dc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C016
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_add_left
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_add_right
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_comm
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_smul_left
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_smul_right
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_totalMinus_traceLift
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_0_0
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_0_1
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_0_2
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_0_3
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_1_0
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_1_1
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_1_2
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_1_3
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_2_0
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_2_1
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_2_2
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_2_3

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceAdjoint
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit trace lift is the actual adjoint on the Bianchi subspace. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

private theorem traceLift_adjoint_parameters_0
    (a b c d e : ℝ) (p k l : Vec) :
    liftSlicePairing (ofCoordinates a b c d e) 0 (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) 0 (parameters referenceShape p k l) := by
  simp [liftSlicePairing, derivativePairing, traceLift,
    quaternionMatrix, parameters, Tensor.matrix,
    referenceShape, difference, next, previous, quaternion, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem traceLift_adjoint_parameters_1
    (a b c d e : ℝ) (p k l : Vec) :
    liftSlicePairing (ofCoordinates a b c d e) 1 (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) 1 (parameters referenceShape p k l) := by
  simp [liftSlicePairing, derivativePairing, traceLift,
    quaternionMatrix, parameters, Tensor.matrix,
    referenceShape, difference, next, previous, quaternion, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem traceLift_adjoint_parameters_2
    (a b c d e : ℝ) (p k l : Vec) :
    liftSlicePairing (ofCoordinates a b c d e) 2 (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) 2 (parameters referenceShape p k l) := by
  simp [liftSlicePairing, derivativePairing, traceLift,
    quaternionMatrix, parameters, Tensor.matrix,
    referenceShape, difference, next, previous, quaternion, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem traceLift_adjoint_parameters_3
    (a b c d e : ℝ) (p k l : Vec) :
    liftSlicePairing (ofCoordinates a b c d e) 3 (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) 3 (parameters referenceShape p k l) := by
  simp [liftSlicePairing, derivativePairing, traceLift,
    quaternionMatrix, parameters, Tensor.matrix,
    referenceShape, difference, next, previous, quaternion, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem traceLift_adjoint_parameters
    (a b c d e : ℝ) (p k l : Vec) (i : Fin 4) :
    liftSlicePairing (ofCoordinates a b c d e) i (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) i (parameters referenceShape p k l) := by
  fin_cases i
  · exact traceLift_adjoint_parameters_0 _ _ _ _ _ _ _ _
  · exact traceLift_adjoint_parameters_1 _ _ _ _ _ _ _ _
  · exact traceLift_adjoint_parameters_2 _ _ _ _ _ _ _ _
  · exact traceLift_adjoint_parameters_3 _ _ _ _ _ _ _ _

/-- The adjoint identity holds for every actual symmetric trace-free Bianchi
gradient; no projection identity is a premise. -/
theorem traceLift_adjoint_slice (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) (i : Fin 4) :
    liftSlicePairing M i Z = derivativePairing M i Z := by
  rw [← coordinates_eq M hs ht, ← parameters_reconstruction referenceShape Z hz hb]
  exact traceLift_adjoint_parameters _ _ _ _ _ _ _ _ i

/-- The global finite-dimensional adjoint identity for the restricted trace. -/
theorem traceLift_adjoint (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (Z : Fin 4 → Tensor) (hz : ∀ i, (Z i).traceFree) (hb : ∀ i, (Z i).bianchi) :
    (∑ i, liftSlicePairing M i (Z i)) = ∑ a, ∑ b, M a b * slicesTrace Z a b := by
  have h (i : Fin 4) := traceLift_adjoint_slice M hs ht (Z i) (hz i) (hb i) i
  simp_rw [h]
  unfold derivativePairing slicesTrace
  simp only [Fin.sum_univ_succ]
  ring

/-- The trace component pairs with an arbitrary constrained Hessian only
through its trace. This includes the prescribed skew part of the Hessian. -/
theorem traceComponent_pairing (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (Z : Fin 4 → Tensor) (hz : ∀ i, (Z i).traceFree) (hb : ∀ i, (Z i).bianchi) :
    hessianPairing (traceComponent M) (slicesHessian Z) =
      (5 / 12 : ℝ) * ∑ a, ∑ b, M a b * slicesTrace Z a b := by
  have h := traceLift_adjoint M hs ht Z hz hb
  change (∑ a, ∑ b, ∑ i, ∑ j,
    ((5 / 12 : ℝ) * traceLift M i j a b) * (Z i).matrix a b j) = _
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [← h]
  congr 1
  unfold liftSlicePairing
  simp only [Fin.sum_univ_succ]
  ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TensorPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skew matrix actions on the actual four tensor slots. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

/-- The usual reindexing proof for a real skew-adjoint matrix. -/
theorem skew_matrix_pairing {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = -A j i) (x y : ι → ℝ) :
    (∑ i, (∑ j, A i j * x j) * y i) =
      -(∑ i, x i * (∑ j, A i j * y j)) := by
  calc
    _ = ∑ i, ∑ j, A i j * x j * y i := by simp_rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, A i j * x j * y i := Finset.sum_comm
    _ = ∑ j, -(∑ i, x j * (A j i * y i)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hA i j]
      ring
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [Finset.sum_neg_distrib]

theorem plusKernel_skew (s : Fin 3) (p q : TensorIndex) :
    plusKernel s p q = -plusKernel s q p := by
  unfold plusKernel
  rw [quaternionMatrix_skew s p.1 q.1,
    quaternionMatrix_skew s p.2.1 q.2.1,
    rotation_skew s p.2.2.1 q.2.2.1,
    rotation_skew s p.2.2.2 q.2.2.2]
  simp only [eq_comm (a := q.1) (b := p.1),
    eq_comm (a := q.2.1) (b := p.2.1),
    eq_comm (a := q.2.2.1) (b := p.2.2.1),
    eq_comm (a := q.2.2.2) (b := p.2.2.2)]
  split_ifs <;> ring

theorem matrixAction_row_sum (s : Fin 3) (M : Mat) (a b : Fin 3) :
    matrixAction s M a b = (∑ c, rotation s a c * M c b) +
      ∑ c, rotation s b c * M a c := by
  unfold matrixAction
  simp only [Finset.sum_sub_distrib]
  have h (c : Fin 3) : M a c * rotation s c b = -(rotation s b c * M a c) := by
    rw [rotation_skew s c b]
    ring
  simp_rw [h]
  rw [Finset.sum_neg_distrib]
  ring

theorem hessianPairing_add_left (X Y Z : Hessian) :
    hessianPairing (X + Y) Z = hessianPairing X Z + hessianPairing Y Z := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b + Y i j a b) * Z i j a b) = _
  simp only [add_mul, hessianPairing, Finset.sum_add_distrib]

theorem hessianPairing_smul_left (r : ℝ) (X Y : Hessian) :
    hessianPairing (r • X) Y = r * hessianPairing X Y := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (r * X i j a b) * Y i j a b) = _
  simp only [mul_assoc, hessianPairing, ← Finset.mul_sum]

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestAction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates _root_.OAI.PositiveEinsteinFour.HighestHessian.vectorHessian_hessianVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The plus Casimir energy and curvature bound on actual highest Hessians. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Entrywise identification with the four-slot Kronecker-sum matrix. -/
theorem totalPlus_coordinates (s : Fin 3) (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (totalPlus s X) p =
      ∑ q : TensorIndex, plusKernel s p q * tensorCoordinates X q := by
  rcases p with ⟨i, j, a, b⟩
  simp [tensorCoordinates, totalPlus, matrixAction_row_sum, plusKernel,
    Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib, ite_mul, ite_and]
  ring

/-- The actual total generator is skew-adjoint for the Frobenius pairing. -/
theorem totalPlus_skew (s : Fin 3) (X Y : Hessian) :
    hessianPairing (totalPlus s X) Y = -hessianPairing X (totalPlus s Y) := by
  have h := skew_matrix_pairing (plusKernel s) (plusKernel_skew s)
    (tensorCoordinates X) (tensorCoordinates Y)
  simp_rw [← totalPlus_coordinates] at h
  rw [tensorCoordinates_pairing, tensorCoordinates_pairing] at h
  exact h

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiSlices
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual gradient slices of a four-slot Hessian. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem innerSlice_traceFree (X : Hessian) (i : Fin 4)
    (ht : ∀ j, traceFree (X i j)) : (innerSlice X i).traceFree := by
  ext j
  simpa [Tensor.traceFree, innerSlice, traceFree, Fin.sum_univ_three] using ht j

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compressed derivative generator in the actual quaternion model. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The normalization of the spin-two curvature operator is a direct
five-coordinate identity. -/
theorem weighted_matrixAction_square (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (M : Mat) (hs : symmetric M) (hm : traceFree M) :
    (∑ s, t s • matrixAction s (matrixAction s M)) =
      (24 : ℝ) • diagonalCurvatureAction t M := by
  have ht2 : t 2 = -t 0 - t 1 := by
    have h := ht
    simp only [Fin.sum_univ_three] at h
    linarith
  ext a b
  change (∑ s, t s * matrixAction s (matrixAction s M) a b) =
    24 * diagonalCurvatureAction t M a b
  rw [← coordinates_eq M hs hm]
  simp only [Fin.sum_univ_three, matrixAction_coordinates_zero,
    matrixAction_coordinates_one, matrixAction_coordinates_two]
  fin_cases a <;> fin_cases b <;>
    simp [diagonalCurvatureAction, ofCoordinates, Fin.sum_univ_succ, ht2]
  all_goals ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixSlotOperator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying matrix-slot curvature coefficient as an actual bounded
operator. The extension to all matrix arrays is self-adjoint; on trace-free
arrays it is the trace-free anticommutator used in the Weyl equation. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedSpaceRealMat
theorem matrixSlotAction_diagonal (t : Fin 3 → ℝ) (M : Mat) :
    matrixSlotAction (Matrix.diagonal t) M = diagonalCurvatureAction t M := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [matrixSlotAction, diagonalCurvatureAction, Matrix.diagonal,
      Fin.sum_univ_three]
  all_goals ring

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceActionIntertwining
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trace lift intertwines the actual tensor rotation actions. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open HighestHessian
set_option maxHeartbeats 1000000

/-- The plus tensor action on the explicit restricted trace adjoint. -/
theorem totalPlus_traceLift (s : Fin 3) (M : Mat) :
    totalPlus s (traceLift M) = traceLift (matrixAction s M) := by
  funext i j a b
  fin_cases s <;> fin_cases i
  · exact traceLift_plus_0_0 M j a b
  · exact traceLift_plus_0_1 M j a b
  · exact traceLift_plus_0_2 M j a b
  · exact traceLift_plus_0_3 M j a b
  · exact traceLift_plus_1_0 M j a b
  · exact traceLift_plus_1_1 M j a b
  · exact traceLift_plus_1_2 M j a b
  · exact traceLift_plus_1_3 M j a b
  · exact traceLift_plus_2_0 M j a b
  · exact traceLift_plus_2_1 M j a b
  · exact traceLift_plus_2_2 M j a b
  · exact traceLift_plus_2_3 M j a b

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceAction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates _root_.OAI.PositiveEinsteinFour.HighestHessian.vectorHessian_hessianVector _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise curvature action on the prescribed trace component. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi HighestHessian

theorem traceLift_add (M N : Mat) : traceLift (M + N) = traceLift M + traceLift N := by
  funext i j a b
  by_cases hij : i = j <;>
    simp [traceLift, matrixAction, hij, mul_add, add_mul, Finset.sum_add_distrib]
  all_goals simp only [Fin.sum_univ_three]
  all_goals ring

theorem traceLift_smul (r : ℝ) (M : Mat) : traceLift (r • M) = r • traceLift M := by
  funext i j a b
  by_cases hij : i = j <;>
    simp [traceLift, matrixAction, hij, Fin.sum_univ_three]
  all_goals ring

theorem traceLift_sub (M N : Mat) : traceLift (M - N) = traceLift M - traceLift N := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ N, traceLift_add, traceLift_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceDecomposition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local tensor identities imply the highest-Hessian constraints. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem matrixAction_traceFree (s : Fin 3) (M : Mat)
    (hs : symmetric M) (ht : traceFree M) : traceFree (matrixAction s M) := by
  rw [← coordinates_eq M hs ht]
  fin_cases s <;> simp [traceFree, matrixAction, TraceHessian.rotation, ofCoordinates, Fin.sum_univ_succ]

theorem traceComponent_traceFree (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (i j : Fin 4) : traceFree (traceComponent M i j) := by
  have h (s : Fin 3) : (∑ a, matrixAction s M a a) = 0 :=
    matrixAction_traceFree s M hs ht
  have hdiag : (∑ a : Fin 3, if i = j then (3 / 5 : ℝ) * M a a else 0) = 0 := by
    by_cases hij : i = j
    · simp only [hij, ite_true, if_true, ← Finset.mul_sum]
      rw [show (∑ a, M a a) = 0 from ht, mul_zero]
    · simp [hij]
  change (∑ a, (5 / 12 : ℝ) * traceLift M i j a a) = 0
  simp only [← Finset.mul_sum, traceLift, Finset.sum_add_distrib]
  rw [hdiag, zero_add]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, h, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceSubtraction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact subtraction of the prescribed trace from the weighted square. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The restricted trace adjoint pairs with any actual inner-Bianchi array,
including an unsymmetrized weight derivative. -/
theorem traceComponent_pairing_hessian (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (X : Hessian) (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) :
    hessianPairing (traceComponent M) X =
      (5 / 12 : ℝ) * matrixPairing M (hessianTrace X) := by
  have hx : slicesHessian (innerSlice X) = X := by
    funext i j a b
    change (innerSlice X i).matrix a b j = X i j a b
    rw [innerSlice_matrix X i (fun j => (hmatrix i j).1)]
  have htr : slicesTrace (innerSlice X) = hessianTrace X := by
    ext a b
    change (∑ i, (innerSlice X i).matrix a b i) = ∑ i, X i i a b
    apply Finset.sum_congr rfl
    intro i _
    rw [innerSlice_matrix X i (fun j => (hmatrix i j).1)]
  calc
    _ = hessianPairing (traceComponent M) (slicesHessian (innerSlice X)) := by rw [hx]
    _ = _ := by
      rw [traceComponent_pairing M hs ht (innerSlice X)
        (fun i => innerSlice_traceFree X i (fun j => (hmatrix i j).2))
        (fun i => innerSlice_bianchi X i (fun j => (hmatrix i j).1) (hbianchi i)), htr]
      rfl

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The original weighted-Hessian curvature form with complete Weyl matrices.
The contractions retain the full symmetric Weyl matrices. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

theorem symmetricMatrix_expansion (A : Mat) (hA : symmetric A) :
    A = Matrix.diagonal (fun r => A r r) + A 0 1 • symmetricUnit 0 1 +
      A 0 2 • symmetricUnit 0 2 + A 1 2 • symmetricUnit 1 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricUnit, hA 1 0, hA 2 0, hA 2 1]


end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The exact prescribed trace in arbitrary matrix coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

private theorem generalMatrixActionSquare_add (A B M : Mat) :
    generalMatrixActionSquare (A + B) M =
      generalMatrixActionSquare A M + generalMatrixActionSquare B M := by
  simp only [generalMatrixActionSquare, Matrix.add_apply, add_smul,
    Finset.sum_add_distrib]

private theorem generalMatrixActionSquare_smul (c : ℝ) (A M : Mat) :
    generalMatrixActionSquare (c • A) M = c • generalMatrixActionSquare A M := by
  simp only [generalMatrixActionSquare, Matrix.smul_apply, smul_eq_mul,
    mul_smul, Finset.smul_sum]

private theorem matrixSlotAction_coeff_add (A B M : Mat) :
    matrixSlotAction (A + B) M = matrixSlotAction A M + matrixSlotAction B M := by
  ext i j
  simp only [matrixSlotAction, Matrix.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  split_ifs <;> ring

private theorem matrixSlotAction_coeff_smul (c : ℝ) (A M : Mat) :
    matrixSlotAction (c • A) M = c • matrixSlotAction A M := by
  ext i j
  simp only [matrixSlotAction, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  split_ifs <;> ring

private theorem generalMatrixActionSquare_diagonal (t : Fin 3 → ℝ) (M : Mat)
    (ht : ∑ r, t r = 0) (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare (Matrix.diagonal t) M =
      (24 : ℝ) • matrixSlotAction (Matrix.diagonal t) M := by
  simp only [generalMatrixActionSquare, Matrix.diagonal_apply,
    ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [matrixSlotAction_diagonal]
  exact weighted_matrixAction_square t ht M hM htM

private theorem generalMatrixActionSquare_symmetricUnit (r s : Fin 3) (M : Mat) :
    generalMatrixActionSquare (symmetricUnit r s) M =
      matrixAction r (matrixAction s M) + matrixAction s (matrixAction r M) := by
  fin_cases r <;> fin_cases s <;>
    simp [generalMatrixActionSquare, symmetricUnit, Fin.sum_univ_three, add_smul, add_comm]
  all_goals exact add_comm _ _

private theorem matrixAction_cross_01 (M : Mat)
    (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare (symmetricUnit 0 1) M =
      (24 : ℝ) • matrixSlotAction (symmetricUnit 0 1) M := by
  rw [generalMatrixActionSquare_symmetricUnit]
  ext i j
  change matrixAction 0 (matrixAction 1 M) i j +
    matrixAction 1 (matrixAction 0 M) i j =
      24 * matrixSlotAction (symmetricUnit 0 1) M i j
  rw [← coordinates_eq M hM htM]
  simp only [matrixAction_coordinates_zero, matrixAction_coordinates_one]
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricUnit, matrixSlotAction, ofCoordinates, Fin.sum_univ_three]
  all_goals ring

private theorem matrixAction_cross_02 (M : Mat)
    (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare (symmetricUnit 0 2) M =
      (24 : ℝ) • matrixSlotAction (symmetricUnit 0 2) M := by
  rw [generalMatrixActionSquare_symmetricUnit]
  ext i j
  change matrixAction 0 (matrixAction 2 M) i j +
    matrixAction 2 (matrixAction 0 M) i j =
      24 * matrixSlotAction (symmetricUnit 0 2) M i j
  rw [← coordinates_eq M hM htM]
  simp only [matrixAction_coordinates_zero, matrixAction_coordinates_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricUnit, matrixSlotAction, ofCoordinates, Fin.sum_univ_three]
  all_goals ring

private theorem matrixAction_cross_12 (M : Mat)
    (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare (symmetricUnit 1 2) M =
      (24 : ℝ) • matrixSlotAction (symmetricUnit 1 2) M := by
  rw [generalMatrixActionSquare_symmetricUnit]
  ext i j
  change matrixAction 1 (matrixAction 2 M) i j +
    matrixAction 2 (matrixAction 1 M) i j =
      24 * matrixSlotAction (symmetricUnit 1 2) M i j
  rw [← coordinates_eq M hM htM]
  simp only [matrixAction_coordinates_one, matrixAction_coordinates_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricUnit, matrixSlotAction, ofCoordinates, Fin.sum_univ_three]
  all_goals ring

/-- The diagonal spin-two identity extends to the full symmetric
trace-free coefficient by its three off-diagonal entries. -/
theorem general_matrixAction_square (A M : Mat)
    (hA : symmetric A) (htA : traceFree A) (hM : symmetric M) (htM : traceFree M) :
    generalMatrixActionSquare A M = (24 : ℝ) • matrixSlotAction A M := by
  rw [symmetricMatrix_expansion A hA]
  simp only [generalMatrixActionSquare_add, generalMatrixActionSquare_smul,
    matrixSlotAction_coeff_add, matrixSlotAction_coeff_smul]
  rw [generalMatrixActionSquare_diagonal _ M htA hM htM,
    matrixAction_cross_01 M hM htM, matrixAction_cross_02 M hM htM,
    matrixAction_cross_12 M hM htM]
  module


private theorem traceLift_pairing_double_sum (A : Mat) (F : Fin 3 → Fin 3 → Mat)
    (Y : Hessian) :
    (∑ r, ∑ s, A r s * hessianPairing (traceLift (F r s)) Y) =
      hessianPairing (traceLift (∑ r, ∑ s, A r s • F r s)) Y := by
  simp only [Fin.sum_univ_three, traceLift_add, traceLift_smul,
    hessianPairing_add_left, hessianPairing_smul_left]

/-- The exact trace-component action is invariant under an arbitrary
symmetric trace-free Weyl coefficient. -/
theorem general_traceLift_curvatureAction (A U M : Mat)
    (hA : symmetric A) (htA : traceFree A) (hM : symmetric M) (htM : traceFree M)
    (Y : Hessian) :
    generalCurvaturePairing A U (traceLift M) Y =
      hessianPairing (traceLift ((4 : ℝ) • M - matrixSlotAction A M)) Y := by
  have hp (r s : Fin 3) :
      hessianPairing (totalPlus r (traceLift M)) (totalPlus s Y) =
        -hessianPairing (traceLift (matrixAction s (matrixAction r M))) Y := by
    rw [totalPlus_traceLift]
    have h := totalPlus_skew s (traceLift (matrixAction r M)) Y
    rw [totalPlus_traceLift] at h
    linarith
  have hw : (∑ r, ∑ s, A r s *
      hessianPairing (traceLift (matrixAction s (matrixAction r M))) Y) =
        24 * hessianPairing (traceLift (matrixSlotAction A M)) Y := by
    have he : (∑ r, ∑ s, A r s *
        hessianPairing (traceLift (matrixAction s (matrixAction r M))) Y) =
        ∑ r, ∑ s, A r s * hessianPairing (traceLift (matrixAction r (matrixAction s M))) Y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [hA s r]
    rw [he, traceLift_pairing_double_sum]
    change hessianPairing (traceLift (generalMatrixActionSquare A M)) Y = _
    rw [general_matrixAction_square A M hA htA hM htM,
      traceLift_smul, hessianPairing_smul_left]
  have hz (V : Hessian) : hessianPairing (0 : Hessian) V = 0 := by
    simp [hessianPairing]
  rw [traceLift_sub, traceLift_smul]
  simp only [generalCurvaturePairing, hp, totalMinus_traceLift, hz,
    mul_neg, Finset.sum_neg_distrib, mul_zero, Finset.sum_const_zero,
    zero_div, add_zero]
  rw [hw]
  rw [sub_eq_add_neg, ← neg_one_smul ℝ (traceLift (matrixSlotAction A M)),
    hessianPairing_add_left, hessianPairing_smul_left, hessianPairing_smul_left]
  ring

theorem general_traceComponent_curvatureAction (A U M : Mat)
    (hA : symmetric A) (htA : traceFree A) (hM : symmetric M) (htM : traceFree M)
    (Y : Hessian) :
    generalCurvaturePairing A U (traceComponent M) Y =
      hessianPairing (traceComponent (generalTraceCurvatureBlock A M)) Y := by
  change generalCurvaturePairing A U ((5 / 12 : ℝ) • traceLift M) Y =
    hessianPairing ((5 / 12 : ℝ) • traceLift (generalTraceCurvatureBlock A M)) Y
  rw [generalCurvaturePairing_smul_left, hessianPairing_smul_left,
    general_traceLift_curvatureAction A U M hA htA hM htM Y]
  rfl


theorem generalTraceCurvatureBlock_symmetric (A M : Mat)
    (hA : symmetric A) (hM : symmetric M) :
    symmetric (generalTraceCurvatureBlock A M) := by
  intro a b
  have hrow (c : Fin 3) :
      A a c * M c b + M a c * A c b = A b c * M c a + M b c * A c a := by
    rw [hA b c, hM c a, hM b c, hA c a]
    ring
  change 4 * M a b - matrixSlotAction A M a b =
    4 * M b a - matrixSlotAction A M b a
  rw [hM a b]
  unfold matrixSlotAction
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp_rw [hrow]
  by_cases hab : a = b
  · subst b
    rfl
  · simp only [hab, Ne.symm hab, ite_false, if_false]

theorem generalTraceCurvatureBlock_traceFree (A M : Mat) (hM : traceFree M) :
    traceFree (generalTraceCurvatureBlock A M) := by
  have hs : Matrix.trace (matrixSlotAction A M) = 0 := by
    rw [matrixSlotAction_eq, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_mul_comm M A]
    norm_num
    ring
  change Matrix.trace (generalTraceCurvatureBlock A M) = 0
  rw [generalTraceCurvatureBlock, Matrix.trace_sub, Matrix.trace_smul,
    show Matrix.trace M = 0 from hM, hs]
  ring

/-- The full trace curvature term pairs through the actual tensor trace. -/
theorem general_traceComponent_curvaturePairing (A U M : Mat)
    (hA : symmetric A) (htA : traceFree A) (hM : symmetric M) (htM : traceFree M)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    generalCurvaturePairing A U (traceComponent M) X =
      (5 / 12 : ℝ) * matrixPairing (generalTraceCurvatureBlock A M) (hessianTrace X) := by
  rw [general_traceComponent_curvatureAction A U M hA htA hM htM X]
  exact traceComponent_pairing_hessian _ (generalTraceCurvatureBlock_symmetric A M hA hM)
    (generalTraceCurvatureBlock_traceFree A M htM) X hm hb

theorem general_prescribed_trace_curvaturePairing (A U M : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A)
    (hM : symmetric M) (htM : traceFree M)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) :
    generalCurvaturePairing A U X (traceComponent M) =
      generalCurvaturePairing A U (traceComponent M) (traceComponent M) := by
  rw [generalCurvaturePairing_comm A U hA hU X,
    general_traceComponent_curvaturePairing A U M hA htA hM htM X hm hb,
    general_traceComponent_curvaturePairing A U M hA htA hM htM (traceComponent M)
      (fun i j => ⟨traceComponent_symmetric M hM htM i j,
        traceComponent_traceFree M hM htM i j⟩)
      (traceComponent_divergence M hM htM), htrace, trace_traceComponent]

/-- Exact trace subtraction includes the unsymmetrized weight derivative. -/
theorem general_weighted_trace_subtraction_oai (A U M : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A)
    (hM : symmetric M) (htM : traceFree M)
    (X L : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) (m : ℝ) :
    m * generalCurvaturePairing A U (X - traceComponent M) (X - traceComponent M) +
        generalCurvaturePairing A U (X - traceComponent M) L =
      m * generalCurvaturePairing A U X X + generalCurvaturePairing A U X L -
        m * generalCurvaturePairing A U (traceComponent M) (traceComponent M) -
          generalCurvaturePairing A U (traceComponent M) L := by
  have hx := general_prescribed_trace_curvaturePairing A U M hA hU htA hM htM
    X hm hb htrace
  have hsub : X - traceComponent M = X + (-1 : ℝ) • traceComponent M := by module
  rw [hsub]
  simp only [generalCurvaturePairing_add_left, generalCurvaturePairing_add_right,
    generalCurvaturePairing_smul_left, generalCurvaturePairing_smul_right]
  rw [generalCurvaturePairing_comm A U hA hU (traceComponent M) X, hx]
  ring


end
end PositiveEinsteinFour.HighestHessian
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction_oai := @OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction_oai
