-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.MetricGreenData.traceGreen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:43:39.398373+00:00
-- url     : https://prove2.me/submissions/356c67e7-3dbe-4f5e-8c85-58ad5a9185e8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C016
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_smul_left
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
-- module Solutions.OAIQ091_EF.EinsteinFour_Bianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete four-vector coordinates for a Bianchi gradient

The three quaternion actions are left multiplication by `i,j,k` on the real
four-dimensional Euclidean space. A symmetric matrix of four-vectors is
encoded by its three diagonal and three off-diagonal entries. Its divergence
constraint is the actual quaternionic Bianchi constraint of Section 2.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

theorem Tensor.matrix_symmetric (T : Tensor) (i j : Fin 3) :
    T.matrix i j = T.matrix j i := by
  fin_cases i <;> fin_cases j <;> rfl

end
end PositiveEinsteinFour.Bianchi

end OAI
end

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
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration of the full prescribed trace term, including its weight derivative. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Integrate the trace block against the rough Laplacian. The gradient of
its coefficient is retained on the right-hand side. -/
theorem weighted_trace_green
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ i, Continuous (fun p : ℝ × Ω => φ i p.1 p.2))
    (hμ : ∀ i t, MeasurePreserving (φ i t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (B : C(Ω, E)) (dB Z dZ : Fin 4 → C(Ω, E))
    (hm : ∀ i t x, HasDerivAt (fun s => m (φ i s x)) (dm i (φ i t x)) t)
    (hB : ∀ i t x, HasDerivAt (fun s => B (φ i s x)) (dB i (φ i t x)) t)
    (hZ : ∀ i t x, HasDerivAt (fun s => Z i (φ i s x)) (dZ i (φ i t x)) t) :
    (∫ x, m x * inner ℝ (B x) (∑ i, dZ i x) +
      ∑ i, dm i x * inner ℝ (B x) (Z i x) ∂μ) =
      -(∫ x, m x * (∑ i, inner ℝ (dB i x) (Z i x)) ∂μ) := by
  have hL (i : Fin 4) : Integrable (fun x =>
      m x * inner ℝ (dB i x) (Z i x) + dm i x * inner ℝ (B x) (Z i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR (i : Fin 4) : Integrable (fun x => m x * inner ℝ (B x) (dZ i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : (∫ x, ∑ i,
      (m x * inner ℝ (dB i x) (Z i x) + dm i x * inner ℝ (B x) (Z i x)) ∂μ) =
      -(∫ x, ∑ i, m x * inner ℝ (B x) (dZ i x) ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => hL i),
      integral_finsetSum _ (fun i _ => hR i)]
    simp_rw [weighted_flow_green μ _ (hφ _) (hμ _) m (dm _) B (dB _) (Z _) (dZ _)
      (hm _) (hB _) (hZ _), Finset.sum_neg_distrib]
  have hJ : Integrable (fun x => m x * (∑ i, inner ℝ (dB i x) (Z i x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (fun x => ∑ i, dm i x * inner ℝ (B x) (Z i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hQ : Integrable (fun x => m x * inner ℝ (B x) (∑ i, dZ i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← inner_sum] at hs
  rw [integral_add hJ hK] at hs
  rw [integral_add hQ hK]
  linarith

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceSubtraction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
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

/-- The weight derivative keeps the genuine inner Bianchi constraints. -/
theorem weightTensor_matrix_bianchi (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∀ i j, symmetric (weightTensor a Z i j) ∧ traceFree (weightTensor a Z i j)) ∧
      (∀ i r, divergence (weightTensor a Z) i r = 0) := by
  constructor
  · intro i j
    constructor
    · intro b c
      change a i * Z.matrix b c j = a i * Z.matrix c b j
      rw [Z.matrix_symmetric b c]
    · have h := congrArg (fun z : Vec => z j) hz
      simp [Fin.sum_univ_three] at h
      change (∑ b, a i * Z.matrix b b j) = 0
      simp only [Fin.sum_univ_three]
      change a i * Z.diagonal 0 j + a i * Z.diagonal 1 j +
        a i * Z.diagonal 2 j = 0
      linear_combination a i * h
  · intro i r
    have h (s : Fin 3) :
        (WithLp.toLp 2 (fun j => weightTensor a Z i j s r) : Vec) =
          a i • Z.matrix s r := by
      ext j
      rfl
    simp only [divergence, h, quaternion_smul, ← Finset.smul_sum,
      ← Tensor.divergence_eq_sum, hb r, smul_zero]

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Differentiate the invariant matrix Weyl equation before choosing a
diagonal frame. The derivative of its quadratic term is exactly twice
the concrete matrix-slot operator. -/

namespace PositiveEinsteinFour.TraceHessian

open Matrix PositiveEinsteinFour.Geometry
open scoped BigOperators

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.TraceHessian.instNormedRingMat
attribute [local instance] OAI.PositiveEinsteinFour.TraceHessian.instNormedSpaceRealMat
attribute [local instance] OAI.PositiveEinsteinFour.TraceHessian.instNormedAlgebraRealMat
theorem matrixSlotAction_derivative (M Z : Mat) :
    Z * M + M * Z - (Matrix.trace (Z * M + M * Z) / 3) • (1 : Mat) =
      (2 : ℝ) • matrixSlotAction M Z := by
  rw [matrixSlotAction_eq, Matrix.trace_add, Matrix.trace_mul_comm Z M]
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem hasDerivAt_traceFreeSquare {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) :
    HasDerivAt (fun r => traceFreeSquare (T r))
      ((2 : ℝ) • matrixSlotAction (T t) Z) t := by
  have hP := hT.mul hT
  have htr := hasDerivAt_matrixTrace hP
  have h := hP.sub ((htr.div_const 3).smul_const (1 : Mat))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  exact (matrixSlotAction_derivative (T t) Z).symm

end
end PositiveEinsteinFour.TraceHessian
end


section

/-! The prescribed-trace coefficient and its ordinary derivative in an
arbitrary frame. No derivative of a matrix eigenframe is used. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian HighestHessian Bianchi
open scoped BigOperators

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.traceCoefficientNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.traceCoefficientNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.traceCoefficientNormedAlgebra
private theorem trace_coefficient_coordinates (a b c d e : ℝ) :
    (4 : ℝ) • weylLaplacian (ofCoordinates a b c d e) -
      matrixSlotAction (ofCoordinates a b c d e)
        (weylLaplacian (ofCoordinates a b c d e)) =
    (6 : ℝ) • traceCoefficient (ofCoordinates a b c d e) := by
  ext i j
  simp only [weylLaplacian, traceCoefficient, traceFreeSquare, matrixSlotAction,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.trace, Matrix.diag, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [ofCoordinates, Matrix.one_apply, Fin.sum_univ_three] <;> ring

/-- The trace operator applied to the derived Weyl Laplacian is six
times the coefficient used in the trace Green identity. -/
theorem trace_coefficient_eq (A : Mat) (hs : symmetric A) (ht : traceFree A) :
    (4 : ℝ) • weylLaplacian A - matrixSlotAction A (weylLaplacian A) =
      (6 : ℝ) • traceCoefficient A := by
  simpa only [coordinates_eq A hs ht] using
    trace_coefficient_coordinates (A 0 0) (A 1 1) (A 0 1) (A 0 2) (A 1 2)

/-- Differentiate the invariant polynomial coefficient, retaining its
radial derivative term. -/
theorem hasDerivAt_traceCoefficient {A : ℝ → Mat} {Z : Mat} {r : ℝ}
    (hA : HasDerivAt A Z r) :
    HasDerivAt (fun t => traceCoefficient (A t))
      (traceCoefficientDerivative (A r) Z) r := by
  have hp := hasDerivAt_matrixTrace (hA.mul hA)
  have h := (((hasDerivAt_const r (4 : ℝ)).add (hp.div_const 6)).smul hA).sub
    ((hasDerivAt_traceFreeSquare hA).const_smul (5 : ℝ))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [traceCoefficientDerivative, Matrix.trace_add,
    Matrix.trace_mul_comm Z (A r), zero_add, Pi.add_apply, Pi.mul_apply]
  have hscalar : (Matrix.trace (A r * Z) + Matrix.trace (A r * Z)) / 6 =
      Matrix.trace (A r * Z) / 3 := by ring
  rw [hscalar]
  module

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Ricci-commuted gradient equation for the actual metric. The two
classical slot identities remain explicit, while the differentiated trace
and curvature-divergence equations are derived. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricRicciNormedRing_r507c68_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricRicciNormedSpace_r507c68_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricRicciNormedAlgebra_r507c68_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem rawMatrixSlice_gradientTensor (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (j : Fin 4) :
    rawMatrixSlice (gradientTensor Z).matrix j = Z j := by
  ext a b
  simp only [rawMatrixSlice, gradientTensor_matrix Z hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full prescribed-trace Green identity for the actual metric,
derived by differentiating its invariant polynomial coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.metricTraceNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.metricTraceNormedSpace
local instance metricTraceNormedAlgebra_r507c68_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- Before any scalar contraction, both trace subtractions give this
identity on the actual frame bundle. The coefficient is a polynomial in
the actual Weyl matrix and its derivative is derived above. -/
theorem weighted_metric_trace_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hDT : ∀ i, Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i))
    (hX : ∀ i, Continuous (frameHessianSlice g i i))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((φ i).map s e))
      (dm i ((φ i).map t e)) t)
    (hTd : ∀ i t e, HasDerivAt
      (fun s => plusWeyl g ((φ i).map s e).base ((φ i).map s e).frame)
      (plusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t)
    (hZd : ∀ i t e, HasDerivAt (fun s => frameGradientSlice g i ((φ i).map s e))
      (frameHessianSlice g i i ((φ i).map t e)) t) :
    -(5 / 12 : ℝ) * (∫ e, m e *
      matrixPairing (traceCoefficient (plusWeyl g e.base e.frame))
        (hessianTrace (plusWeylHessian g e.base e.frame)) +
      ∑ i, dm i e * matrixPairing (traceCoefficient (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame i) ∂μ) =
      (5 / 12 : ℝ) * (∫ e, m e * ∑ i,
        matrixPairing (traceCoefficientDerivative (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i))
          (plusWeylGradient g e.base e.frame i) ∂μ) := by
  let T : C(FrameBundle g, Mat) := ⟨fun e => plusWeyl g e.base e.frame, hT⟩
  let DT (i : Fin 4) : C(FrameBundle g, Mat) :=
    ⟨fun e => plusWeylGradient g e.base e.frame i, hDT i⟩
  let B : C(FrameBundle g, MatrixVector) := traceCoefficientVectorMap.comp T
  let dB (i : Fin 4) : C(FrameBundle g, MatrixVector) :=
    traceCoefficientDerivativeVectorMap.comp (T.prodMk (DT i))
  let Z (i : Fin 4) : C(FrameBundle g, MatrixVector) :=
    ⟨frameGradientSlice g i, matrixVectorMap.continuous.comp (hDT i)⟩
  let X (i : Fin 4) : C(FrameBundle g, MatrixVector) := ⟨frameHessianSlice g i i, hX i⟩
  have h := Averages.weighted_trace_green μ
    (fun i => (φ i).map) (fun i => (φ i).continuous) (fun i => (φ i).preserves)
    m dm B dB Z X hm
    (fun i t e => hasDerivAt_matrixVector (hasDerivAt_traceCoefficient (hTd i t e))) hZd
  have hsum (e : FrameBundle g) :
      (∑ i, frameHessianSlice g i i e) =
        matrixVector (hessianTrace (plusWeylHessian g e.base e.frame)) := by
    ext p
    simp only [frameHessianSlice, hessianTrace, matrixVector, WithLp.ofLp_sum,
      Finset.sum_apply, Matrix.sum_apply]
  simp only [B, dB, T, DT, Z, X, traceCoefficientVectorMap,
    traceCoefficientDerivativeVectorMap, ContinuousMap.comp_apply, ContinuousMap.prod_eval,
    ContinuousMap.coe_mk, hsum] at h
  change (∫ e, m e * inner ℝ
      (matrixVector (traceCoefficient (plusWeyl g e.base e.frame)))
      (matrixVector (hessianTrace (plusWeylHessian g e.base e.frame))) +
      ∑ i, dm i e * inner ℝ
        (matrixVector (traceCoefficient (plusWeyl g e.base e.frame)))
        (matrixVector (plusWeylGradient g e.base e.frame i)) ∂μ) =
    -(∫ e, m e * ∑ i, inner ℝ
      (matrixVector (traceCoefficientDerivative (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i)))
      (matrixVector (plusWeylGradient g e.base e.frame i)) ∂μ) at h
  simp only [inner_matrixVector] at h
  rw [h]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full trace Green term as invariant polynomial contractions.
This expression has no division by a Weyl norm and is valid at its zeros. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance traceScalarNormedRing_r507c68_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance traceScalarNormedSpace_r507c68_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance traceScalarNormedAlgebra_r507c68_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem traceCoefficientDerivative_pairing (A Z : Mat) (hZ : symmetric Z) :
    matrixPairing (traceCoefficientDerivative A Z) Z =
      (4 + Matrix.trace (A * A) / 6) * matrixPairing Z Z -
        10 * matrixPairing (matrixSlotAction A Z) Z + Matrix.trace (A * Z) ^ 2 / 3 := by
  have hzt : Zᵀ = Z := by ext i j; exact hZ j i
  have hp : matrixPairing A Z = Matrix.trace (A * Z) := by
    rw [matrixPairing_eq_trace, hzt]
  change CurvatureContraction.matrixPairingLinear Z _ = _
  rw [traceCoefficientDerivative, map_sub, map_add, map_smul, map_smul, map_smul]
  change (4 + Matrix.trace (A * A) / 6) * matrixPairing Z Z +
    (Matrix.trace (A * Z) / 3) * matrixPairing A Z -
      10 * matrixPairing (matrixSlotAction A Z) Z = _
  rw [hp]
  ring

theorem traceCoefficientDerivative_sum (A : Mat) (hA : symmetric A)
    (Z : Fin 4 → Mat) (hZ : ∀ i, symmetric (Z i)) :
    (5 / 12 : ℝ) * (∑ i, matrixPairing (traceCoefficientDerivative A (Z i)) (Z i)) =
      (10 + (5 / 2 : ℝ) * normalizedBlockNorm A ^ 2) * weylGradientEnergy Z -
        25 * weylMatrixEnergy A Z + 5 * weylRadialSquare A Z := by
  simp_rw [traceCoefficientDerivative_pairing A _ (hZ _)]
  rw [trace_square_eq_six_norm_sq A hA]
  simp only [weylGradientEnergy, weylMatrixEnergy, weylRadialSquare,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_div]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The actual trace subtraction gives the scalar term of the weighted
Hessian estimate in every frame, including at Weyl zeros. -/
theorem weighted_metric_trace_scalar
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hDT : ∀ i, Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i))
    (hX : ∀ i, Continuous (frameHessianSlice g i i))
    (hsT : ∀ e : FrameBundle g, symmetric (plusWeyl g e.base e.frame))
    (hsZ : ∀ e : FrameBundle g, ∀ i, symmetric (plusWeylGradient g e.base e.frame i))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((φ i).map s e))
      (dm i ((φ i).map t e)) t)
    (hTd : ∀ i t e, HasDerivAt
      (fun s => plusWeyl g ((φ i).map s e).base ((φ i).map s e).frame)
      (plusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t)
    (hZd : ∀ i t e, HasDerivAt (fun s => frameGradientSlice g i ((φ i).map s e))
      (frameHessianSlice g i i ((φ i).map t e)) t) :
    -(5 / 12 : ℝ) * (∫ e, m e *
      matrixPairing (traceCoefficient (plusWeyl g e.base e.frame))
        (hessianTrace (plusWeylHessian g e.base e.frame)) +
      ∑ i, dm i e * matrixPairing (traceCoefficient (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame i) ∂μ) =
      ∫ e, m e *
        ((10 + (5 / 2 : ℝ) * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) *
          weylGradientEnergy (plusWeylGradient g e.base e.frame) -
        25 * weylMatrixEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) +
        5 * weylRadialSquare (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame)) ∂μ := by
  rw [weighted_metric_trace_green g φ m dm hT hDT hX hm hTd hZd,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with e
  calc
    _ = m e * ((5 / 12 : ℝ) * ∑ i,
        matrixPairing (traceCoefficientDerivative (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i))
          (plusWeylGradient g e.base e.frame i)) := by ring
    _ = _ := by rw [traceCoefficientDerivative_sum _ (hsT e) _ (hsZ e)]

end
end PositiveEinsteinFour.Geometry
end


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

/-! Evaluate the derivative-slot Green integral on actual metric tensors,
using the published raw curvature decomposition and Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedSpace
local instance curvatureIntegralNormedAlgebra_r507c68_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuousHessianSlice (d : MetricGreenData g μ) (i j : Fin 4) :
    Continuous (frameHessianSlice g i j) :=
  matrixVectorMap.continuous.comp (d.continuousHessian i j)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
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


/-- The prescribed trace is exactly the invariant polynomial coefficient
already differentiated in the geometric trace Green identity. -/
theorem generalTraceCurvatureBlock_weylLaplacian (A : Mat)
    (hA : symmetric A) (htA : traceFree A) :
    generalTraceCurvatureBlock A (weylLaplacian A) = (6 : ℝ) • traceCoefficient A :=
  trace_coefficient_eq A hA htA

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Identify the complete trace correction in the invariant local square
with the already proved metric trace Green integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem matrixPairing_weightTensor_trace (A : Mat) (a : Vec) (Z : Tensor) :
    matrixPairing A (hessianTrace (weightTensor a Z)) =
      ∑ i, a i * matrixPairing A (rawMatrixSlice Z.matrix i) := by
  simp only [matrixPairing, hessianTrace, weightTensor, Matrix.sum_apply,
    Finset.mul_sum, rawMatrixSlice]
  calc
    _ = ∑ b, ∑ i, ∑ c, A b c * (a i * Z.matrix b c i) := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ i, ∑ b, ∑ c, A b c * (a i * Z.matrix b c i) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem general_traceCorrection_weyl (A U : Mat)
    (hA : symmetric A) (htA : traceFree A) (m : ℝ) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    generalTraceCorrection A U (weylLaplacian A) m (weightTensor a Z) =
      -(5 / 12 : ℝ) * (m * matrixPairing (traceCoefficient A) (weylLaplacian A) +
        ∑ i, a i * matrixPairing (traceCoefficient A) (rawMatrixSlice Z.matrix i)) := by
  have hs := weylLaplacian_symmetric A hA
  have ht := weylLaplacian_traceFree A htA
  have hL := weightTensor_matrix_bianchi a Z hz hb
  unfold generalTraceCorrection
  rw [general_traceComponent_curvaturePairing A U _ hA htA hs ht _
      (fun i j => ⟨traceComponent_symmetric _ hs ht i j,
        traceComponent_traceFree _ hs ht i j⟩) (traceComponent_divergence _ hs ht),
    general_traceComponent_curvaturePairing A U _ hA htA hs ht _ hL.1 hL.2,
    trace_traceComponent, generalTraceCurvatureBlock_weylLaplacian A hA htA]
  have hp (B : Mat) : matrixPairing ((6 : ℝ) • traceCoefficient A) B =
      6 * matrixPairing (traceCoefficient A) B := by
    simp only [matrixPairing, Matrix.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum]
  rw [hp, hp, matrixPairing_weightTensor_trace]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem traceGreen_oai (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, generalTraceCorrection (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (weylLaplacian (plusWeyl g e.base e.frame)) (m e)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * ((10 + (5 / 2 : ℝ) * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) *
        weylGradientEnergy (plusWeylGradient g e.base e.frame) -
      25 * weylMatrixEnergy (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
      5 * weylRadialSquare (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)) ∂μ := by
  have h := weighted_metric_trace_scalar g d.flow m dm d.continuousWeyl
    d.continuousGradient (fun i => d.continuousHessianSlice i i)
    d.weyl.symmetric (fun e => (d.gradientConstraints e).1) hm d.derivativeWeyl
    (fun i t e => hasDerivAt_matrixVector (d.derivativeGradient i i t e))
  rw [← integral_const_mul] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with e
  simp only [plusGradientTensor]
  rw [general_traceCorrection_weyl _ _ (d.weyl.symmetric e) (d.weyl.traceFree e) _ _ _
    (gradientTensor_traceFree _ (d.gradientConstraints e).2)
    (gradientTensor_bianchi _ (d.gradientConstraints e).1 (d.gradientBianchi e)),
    metric_weyl_trace g d.weyl e]
  simp only [rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.traceGreen_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.traceGreen_oai.{u_1}
