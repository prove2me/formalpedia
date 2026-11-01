-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.MetricGreenData.preVarianceGreen_oriented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:41:49.132439+00:00
-- url     : https://prove2.me/submissions/74874552-2e4d-4335-b35b-68700b7ae2d2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C016
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_FrameReflectionData_jointEnergyCancellation
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_regularizedHessianGreen
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_add_left
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_add_right
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_smul_left
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_smul_right

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed trace component of the Bianchi Hessian

The arrays are real tensors. The lift is the explicit formula for the
restricted trace adjoint in Section 5; its Bianchi constraint, trace and
squared norm follow by direct calculation in the fixed quaternion frame. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

/-- The spin-two Casimir, computed on the actual symmetric trace-free matrix. -/
theorem matrixAction_casimir (M : Mat) (hs : symmetric M) (ht : traceFree M) :
    (∑ a, ∑ b, ∑ s, matrixAction s M a b ^ 2) = 24 * matrixNormSq M := by
  rw [← coordinates_eq M hs ht]
  simp [matrixAction, rotation, ofCoordinates, matrixNormSq,
    Fin.sum_univ_succ]
  ring

private theorem quaternion_square_sum (x : ℝ) (a : Fin 3 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      ((if i = j then (3 / 5 : ℝ) * x else 0) +
        (1 / 10 : ℝ) * ∑ s, quaternionMatrix s i j * a s) ^ 2) =
      (36 / 25) * x ^ 2 + (1 / 25) * ∑ s, a s ^ 2 := by
  simp [quaternionMatrix, Fin.sum_univ_succ]
  ring

/-- The norm of the explicit restricted trace lift. -/
theorem traceLift_norm (M : Mat) (hs : symmetric M) (ht : traceFree M) :
    hessianNormSq (traceLift M) = (12 / 5) * matrixNormSq M := by
  have hentry (a b : Fin 3) :
      (∑ i : Fin 4, ∑ j : Fin 4, traceLift M i j a b ^ 2) =
        (36 / 25) * M a b ^ 2 + (1 / 25) * ∑ s, matrixAction s M a b ^ 2 := by
    simpa only [traceLift] using
      quaternion_square_sum (M a b) (fun s => matrixAction s M a b)
  unfold hessianNormSq
  simp_rw [hentry]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [matrixAction_casimir M hs ht]
  unfold matrixNormSq
  ring

/-- The exact coefficient subtracted in the weighted Hessian identity. -/
theorem traceComponent_norm (M : Mat) (hs : symmetric M) (ht : traceFree M) :
    hessianNormSq (traceComponent M) = (5 / 12) * matrixNormSq M := by
  have hscale : hessianNormSq (traceComponent M) =
      (5 / 12 : ℝ) ^ 2 * hessianNormSq (traceLift M) := by
    simp [hessianNormSq, traceComponent, mul_pow, Finset.mul_sum]
  rw [hscale, traceLift_norm M hs ht]
  ring

end
end PositiveEinsteinFour.TraceHessian

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

theorem hessianPairing_comm (X Y : Hessian) :
    hessianPairing X Y = hessianPairing Y X := by
  simp only [hessianPairing, mul_comm]

theorem hessianNormSq_sub (X Y : Hessian) :
    hessianNormSq (X - Y) = hessianNormSq X - 2 * hessianPairing X Y +
      hessianNormSq Y := by
  have h (i j : Fin 4) (a b : Fin 3) :
      (X i j a b - Y i j a b) ^ 2 = X i j a b ^ 2 -
        2 * (X i j a b * Y i j a b) + Y i j a b ^ 2 := by ring
  change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b - Y i j a b) ^ 2) = _
  simp only [hessianNormSq, hessianPairing, h, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]

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
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Smooth norm regularization for the actual squared Weyl weight.
The positive regularization parameter allows the Green identities to be
used at Weyl zeros as well as on the positive-norm set. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian Filter
open scoped _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedRing
local instance smoothWeylNormedSpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedAlgebra
theorem regularizedBlockNorm_le (ε : ℝ) (hε : 0 ≤ ε) (A : Mat) :
    regularizedBlockNorm ε A ≤ normalizedBlockNorm A + ε := by
  rw [regularizedBlockNorm, Real.sqrt_le_left (add_nonneg (normalizedBlockNorm_nonneg A) hε)]
  nlinarith [normalizedBlockNorm_nonneg A]

theorem tendsto_regularizedBlockNorm (A : Mat) :
    Tendsto (fun ε => regularizedBlockNorm ε A) (𝓝 0) (𝓝 (normalizedBlockNorm A)) := by
  have hc : Continuous (fun ε => regularizedBlockNorm ε A) := by
    unfold regularizedBlockNorm
    fun_prop
  simpa only [regularizedBlockNorm_zero] using hc.tendsto 0

theorem tendsto_regularizedRadialDerivative (A Z : Mat) :
    Tendsto (fun ε => regularizedRadialDerivative ε A Z) (𝓝 0)
      (𝓝 (Matrix.trace (A * Z) / (6 * normalizedBlockNorm A))) := by
  by_cases ha : normalizedBlockNorm A = 0
  · have hA : A = 0 := (normalizedBlockNorm_eq_zero_iff A).mp ha
    subst A
    simp [regularizedRadialDerivative]
  · exact tendsto_const_nhds.div
      (tendsto_const_nhds.mul (tendsto_regularizedBlockNorm A))
      (mul_ne_zero (by norm_num) ha)

theorem tendsto_regularizedWeylWeight (A B : Mat) :
    Tendsto (fun ε => regularizedWeylWeight ε A B) (𝓝 0)
      (𝓝 ((1 - (3 / 8 : ℝ) * (normalizedBlockNorm A - normalizedBlockNorm B)) ^ 2)) := by
  exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul
    ((tendsto_regularizedBlockNorm A).sub (tendsto_regularizedBlockNorm B)))).pow 2

theorem tendsto_regularizedWeylWeightDerivative (A B Z V : Mat) :
    Tendsto (fun ε => regularizedWeylWeightDerivative ε A B Z V) (𝓝 0)
      (𝓝 (-(3 / 4 : ℝ) *
        (1 - (3 / 8 : ℝ) * (normalizedBlockNorm A - normalizedBlockNorm B)) *
        (Matrix.trace (A * Z) / (6 * normalizedBlockNorm A) -
          Matrix.trace (B * V) / (6 * normalizedBlockNorm B)))) := by
  exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_const_nhds.mul
    ((tendsto_regularizedBlockNorm A).sub (tendsto_regularizedBlockNorm B))))).mul
      ((tendsto_regularizedRadialDerivative A Z).sub
        (tendsto_regularizedRadialDerivative B V))

theorem regularized_weight_factor_lower (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    1 / 8 < 1 - (3 / 8 : ℝ) * (regularizedBlockNorm ε A - regularizedBlockNorm ε B) := by
  have ha := regularizedBlockNorm_le ε hε A
  have hb := Real.sqrt_nonneg (normalizedBlockNorm B ^ 2 + ε ^ 2)
  have hnb := normalizedBlockNorm_nonneg B
  change 0 ≤ regularizedBlockNorm ε B at hb
  nlinarith

theorem regularizedWeylWeight_pos (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    0 < regularizedWeylWeight ε A B := by
  have h := regularized_weight_factor_lower ε hε he A B hpinch
  unfold regularizedWeylWeight
  exact sq_pos_of_pos (by linarith)

theorem abs_trace_mul_le_norm (A Z : Mat) (hZ : symmetric Z) :
    |Matrix.trace (A * Z)| ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := by
  have hzt : Zᵀ = Z := by ext i j; exact hZ j i
  have hp : matrixPairing A Z = Matrix.trace (A * Z) := by
    rw [matrixPairing_eq_trace, hzt]
  have h := real_inner_mul_inner_self_le (matrixVector A) (matrixVector Z)
  simp only [inner_matrixVector, matrixPairing_self_norm, hp] at h
  apply abs_le_of_sq_le_sq _
    (mul_nonneg (mul_nonneg (by norm_num) (normalizedBlockNorm_nonneg A))
      (normalizedBlockNorm_nonneg Z))
  nlinarith only [h]

/-- The regularized derivative has a bound independent of the smoothing
parameter. This is the domination needed at Weyl zeros. -/
theorem abs_regularizedRadialDerivative_le (ε : ℝ) (hε : 0 < ε)
    (A Z : Mat) (hZ : symmetric Z) :
    |regularizedRadialDerivative ε A Z| ≤ normalizedBlockNorm Z := by
  have hn := regularizedBlockNorm_pos ε hε A
  rw [regularizedRadialDerivative, abs_div, abs_of_pos (mul_pos (by norm_num) hn),
    div_le_iff₀ (mul_pos (by norm_num) hn)]
  calc
    _ ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := abs_trace_mul_le_norm A Z hZ
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (norm_le_regularizedBlockNorm ε A)
        (normalizedBlockNorm_nonneg Z)
      nlinarith only [h]

theorem regularized_weight_factor_upper (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    1 - (3 / 8 : ℝ) * (regularizedBlockNorm ε A - regularizedBlockNorm ε B) < 2 := by
  have hb := regularizedBlockNorm_le ε hε B
  have ha := Real.sqrt_nonneg (normalizedBlockNorm A ^ 2 + ε ^ 2)
  have hna := normalizedBlockNorm_nonneg A
  change 0 ≤ regularizedBlockNorm ε A at ha
  nlinarith

theorem regularizedWeylWeight_bounds (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    1 / 64 ≤ regularizedWeylWeight ε A B ∧ regularizedWeylWeight ε A B ≤ 4 := by
  have hlo := regularized_weight_factor_lower ε hε he A B hpinch
  have hhi := regularized_weight_factor_upper ε hε he A B hpinch
  unfold regularizedWeylWeight
  constructor <;> nlinarith

theorem abs_regularizedWeylWeightDerivative_le (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3)
    (A B Z V : Mat) (hZ : symmetric Z) (hV : symmetric V)
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedWeylWeightDerivative ε A B Z V| ≤
      (3 / 2 : ℝ) * (normalizedBlockNorm Z + normalizedBlockNorm V) := by
  have hlo := regularized_weight_factor_lower ε hε.le he A B hpinch
  have hhi := regularized_weight_factor_upper ε hε.le he A B hpinch
  have habs : |1 - (3 / 8 : ℝ) *
      (regularizedBlockNorm ε A - regularizedBlockNorm ε B)| ≤ 2 := by
    rw [abs_of_pos (by linarith)]
    exact hhi.le
  have hrad : |regularizedRadialDerivative ε A Z - regularizedRadialDerivative ε B V| ≤
      normalizedBlockNorm Z + normalizedBlockNorm V :=
    (abs_sub _ _).trans (add_le_add (abs_regularizedRadialDerivative_le ε hε A Z hZ)
      (abs_regularizedRadialDerivative_le ε hε B V hV))
  unfold regularizedWeylWeightDerivative
  rw [abs_mul, abs_mul]
  norm_num only [abs_neg, abs_div]
  calc
    _ ≤ (3 / 4 : ℝ) * 2 * (normalizedBlockNorm Z + normalizedBlockNorm V) := by
      gcongr
    _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ordinary differentiation and compact bounds for the specific polynomial
multiplier of equation (15), with both Weyl norms varying. -/

namespace PositiveEinsteinFour.Geometry

open Potential Quadratic TraceHessian Filter
open scoped _root_.Topology

noncomputable section

theorem hasDerivAt_kappa_comp {v b : ℝ → ℝ} {p q t : ℝ}
    (hv : HasDerivAt v p t) (hb : HasDerivAt b q t) :
    HasDerivAt (fun s => kappa (v s) (b s))
      (kappaV (v t) (b t) * p + kappaB (v t) (b t) * q) t := by
  have ha := hv.sub_const 1
  have hs := hb.sub_const 1
  have h0 := (ha.sub hs).const_mul (-(158 / 6 : ℝ))
  have h1 := h0.add ((ha.pow 2).const_mul (-(43 / 4 : ℝ)))
  have h2 := h1.add ((ha.mul hs).const_mul (61 / 18 : ℝ))
  have h3 := h2.add ((hs.pow 2).const_mul (-(45 / 4 : ℝ)))
  have h4 := h3.add ((hs.pow 3).const_mul (-(63 / 4 : ℝ)))
  have h5 := h4.add ((ha.mul (hs.pow 2)).const_mul (21 / 4 : ℝ))
  have h6 := h5.add (((ha.pow 2).mul hs).const_mul (183 / 4 : ℝ))
  have h7 := h6.add ((ha.pow 3).const_mul (208 / 4 : ℝ))
  have h8 := h7.add ((hs.pow 4).const_mul (61 / 4 : ℝ))
  have h9 := h8.add ((ha.mul (hs.pow 3)).const_mul (46 / 4 : ℝ))
  have h10 := h9.add (((ha.pow 2).mul (hs.pow 2)).const_mul (101 / 4 : ℝ))
  have h11 := h10.add (((ha.pow 3).mul hs).const_mul (79 / 4 : ℝ))
  have h12 := h11.add ((ha.pow 4).const_mul (-(41 / 4 : ℝ)))
  convert! h12 using 1
  · funext s
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    unfold kappa
    ring
  · unfold kappaV kappaB
    simp only [Pi.pow_apply]
    ring

theorem continuous_kappa : Continuous (fun x : ℝ × ℝ => kappa x.1 x.2) := by
  unfold kappa
  fun_prop

theorem continuous_kappaV : Continuous (fun x : ℝ × ℝ => kappaV x.1 x.2) := by
  unfold kappaV
  fun_prop

theorem continuous_kappaB : Continuous (fun x : ℝ × ℝ => kappaB x.1 x.2) := by
  unfold kappaB
  fun_prop

theorem kappa_rectangle_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ v b : ℝ, 0 ≤ v → v ≤ 3 → 0 ≤ b → b ≤ 3 →
      |kappa v b| ≤ C ∧ |kappaV v b| ≤ C ∧ |kappaB v b| ≤ C := by
  let K : Set (ℝ × ℝ) := Set.Icc 0 3 ×ˢ Set.Icc 0 3
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, h₀⟩ := hK.exists_bound_of_continuousOn continuous_kappa.continuousOn
  obtain ⟨C₁, h₁⟩ := hK.exists_bound_of_continuousOn continuous_kappaV.continuousOn
  obtain ⟨C₂, h₂⟩ := hK.exists_bound_of_continuousOn continuous_kappaB.continuousOn
  refine ⟨|C₀| + |C₁| + |C₂|, by positivity, ?_⟩
  intro v b hv hv3 hb hb3
  have hx : (v, b) ∈ K := ⟨⟨hv, hv3⟩, ⟨hb, hb3⟩⟩
  have h0 := h₀ (v, b) hx
  have h1 := h₁ (v, b) hx
  have h2 := h₂ (v, b) hx
  simp only [Real.norm_eq_abs] at h0 h1 h2
  exact ⟨h0.trans (by linarith [le_abs_self C₀, abs_nonneg C₁, abs_nonneg C₂]),
    h1.trans (by linarith [le_abs_self C₁, abs_nonneg C₀, abs_nonneg C₂]),
    h2.trans (by linarith [le_abs_self C₂, abs_nonneg C₀, abs_nonneg C₁])⟩

local instance kappaNormedRing_rdf0d04_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance kappaNormedSpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance kappaNormedAlgebra_rdf0d04_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuous_regularizedKappa {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (A B : Ω → Mat) (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun e => regularizedKappa ε (A e) (B e)) := by
  simpa only [regularizedKappa, Function.comp_def] using
    continuous_kappa.comp (((continuous_regularizedBlockNorm ε).comp hA).prodMk
      ((continuous_regularizedBlockNorm ε).comp hB))

theorem continuous_regularizedKappaDerivative {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A B Z V : Ω → Mat)
    (hA : Continuous A) (hB : Continuous B) (hZ : Continuous Z) (hV : Continuous V) :
    Continuous (fun e => regularizedKappaDerivative ε (A e) (B e) (Z e) (V e)) := by
  have hAB := ((continuous_regularizedBlockNorm ε).comp hA).prodMk
    ((continuous_regularizedBlockNorm ε).comp hB)
  convert! ((continuous_kappaV.comp hAB).mul
    (continuous_regularizedRadialDerivative ε hε A Z hA hZ)).add
      ((continuous_kappaB.comp hAB).mul
        (continuous_regularizedRadialDerivative ε hε B V hB hV)) using 1
  all_goals try with_reducible_and_instances rfl

theorem hasDerivAt_regularizedKappa {A B : ℝ → Mat} {Z V : Mat} {t ε : ℝ}
    (hA : HasDerivAt A Z t) (hB : HasDerivAt B V t)
    (hsA : ∀ t, symmetric (A t)) (hsB : ∀ t, symmetric (B t)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedKappa ε (A s) (B s))
      (regularizedKappaDerivative ε (A t) (B t) Z V) t :=
  hasDerivAt_kappa_comp (hasDerivAt_regularizedBlockNorm hA hsA hε)
    (hasDerivAt_regularizedBlockNorm hB hsB hε)

theorem regularizedNorm_rectangle {ε : ℝ} (hε : 0 ≤ ε) (he : ε ≤ 1)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    0 ≤ regularizedBlockNorm ε A ∧ regularizedBlockNorm ε A ≤ 3 ∧
    0 ≤ regularizedBlockNorm ε B ∧ regularizedBlockNorm ε B ≤ 3 := by
  have hA := regularizedBlockNorm_le ε hε A
  have hB := regularizedBlockNorm_le ε hε B
  refine ⟨Real.sqrt_nonneg _, ?_, Real.sqrt_nonneg _, ?_⟩
  · linarith [normalizedBlockNorm_nonneg B]
  · linarith [normalizedBlockNorm_nonneg A]

theorem regularizedKappa_bounds (C : ℝ)
    (hC : ∀ v b : ℝ, 0 ≤ v → v ≤ 3 → 0 ≤ b → b ≤ 3 →
      |kappa v b| ≤ C ∧ |kappaV v b| ≤ C ∧ |kappaB v b| ≤ C)
    {ε : ℝ} (hε : 0 < ε) (he : ε ≤ 1)
    (A B Z V : Mat) (hZ : symmetric Z) (hV : symmetric V)
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedKappa ε A B| ≤ C ∧ |regularizedKappaDerivative ε A B Z V| ≤
      C * (normalizedBlockNorm Z + normalizedBlockNorm V) := by
  obtain ⟨hA0, hA3, hB0, hB3⟩ := regularizedNorm_rectangle hε.le he A B hpinch
  obtain ⟨hk, hkV, hkB⟩ := hC _ _ hA0 hA3 hB0 hB3
  refine ⟨hk, ?_⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hk
  unfold regularizedKappaDerivative
  calc
    _ ≤ |kappaV (regularizedBlockNorm ε A) (regularizedBlockNorm ε B) *
        regularizedRadialDerivative ε A Z| +
        |kappaB (regularizedBlockNorm ε A) (regularizedBlockNorm ε B) *
        regularizedRadialDerivative ε B V| := abs_add_le _ _
    _ ≤ C * normalizedBlockNorm Z + C * normalizedBlockNorm V := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul hkV (abs_regularizedRadialDerivative_le ε hε A Z hZ) (abs_nonneg _) hC0)
        (mul_le_mul hkB (abs_regularizedRadialDerivative_le ε hε B V hV) (abs_nonneg _) hC0)
    _ = _ := by ring

theorem tendsto_regularizedKappa (A B : Mat) :
    Tendsto (fun ε => regularizedKappa ε A B) (𝓝 0) (𝓝 (regularizedKappa 0 A B)) := by
  simpa only [regularizedKappa, regularizedBlockNorm_zero, Function.comp_def] using
    continuous_kappa.continuousAt.tendsto.comp
      ((tendsto_regularizedBlockNorm A).prodMk_nhds (tendsto_regularizedBlockNorm B))

theorem tendsto_regularizedKappaDerivative (A B Z V : Mat) :
    Tendsto (fun ε => regularizedKappaDerivative ε A B Z V) (𝓝 0)
      (𝓝 (regularizedKappaDerivative 0 A B Z V)) := by
  have hp := (tendsto_regularizedBlockNorm A).prodMk_nhds (tendsto_regularizedBlockNorm B)
  have hz : Tendsto (fun ε => regularizedRadialDerivative ε A Z) (𝓝 0)
      (𝓝 (regularizedRadialDerivative 0 A Z)) := by
    simpa only [regularizedRadialDerivative, regularizedBlockNorm_zero] using
      tendsto_regularizedRadialDerivative A Z
  have hv : Tendsto (fun ε => regularizedRadialDerivative ε B V) (𝓝 0)
      (𝓝 (regularizedRadialDerivative 0 B V)) := by
    simpa only [regularizedRadialDerivative, regularizedBlockNorm_zero] using
      tendsto_regularizedRadialDerivative B V
  simpa only [regularizedKappaDerivative, regularizedBlockNorm_zero, Function.comp_def] using
    ((continuous_kappaV.continuousAt.tendsto.comp hp).mul hz).add
      ((continuous_kappaB.continuousAt.tendsto.comp hp).mul hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Mixed entries of the regularized weight cost. These are the finite
matrix entries needed by the actual orthogonal-projection quadratic form. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped _root_.Topology

noncomputable section

local instance mixedWeightNormedRing_rdf0d04_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance mixedWeightNormedSpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance mixedWeightNormedAlgebra_rdf0d04_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem regularized_weight_mixed_cost_le
    (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3) (A B Z₁ Z₂ V₁ V₂ : Mat)
    (hsZ₁ : symmetric Z₁) (hsZ₂ : symmetric Z₂)
    (hsV₁ : symmetric V₁) (hsV₂ : symmetric V₂)
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedWeylWeightDerivative ε A B Z₁ V₁ *
      regularizedWeylWeightDerivative ε A B Z₂ V₂ / regularizedWeylWeight ε A B| ≤
      144 * (normalizedBlockNorm Z₁ + normalizedBlockNorm V₁) *
        (normalizedBlockNorm Z₂ + normalizedBlockNorm V₂) := by
  have hp := regularizedWeylWeight_pos ε hε.le he A B hpinch
  have hm := (regularizedWeylWeight_bounds ε hε.le he A B hpinch).1
  have h₁ := abs_regularizedWeylWeightDerivative_le ε hε he A B Z₁ V₁ hsZ₁ hsV₁ hpinch
  have h₂ := abs_regularizedWeylWeightDerivative_le ε hε he A B Z₂ V₂ hsZ₂ hsV₂ hpinch
  have hn₁ : 0 ≤ normalizedBlockNorm Z₁ + normalizedBlockNorm V₁ :=
    add_nonneg (normalizedBlockNorm_nonneg _) (normalizedBlockNorm_nonneg _)
  have hn₂ : 0 ≤ normalizedBlockNorm Z₂ + normalizedBlockNorm V₂ :=
    add_nonneg (normalizedBlockNorm_nonneg _) (normalizedBlockNorm_nonneg _)
  rw [abs_div, abs_mul, abs_of_pos hp, div_le_iff₀ hp]
  calc
    _ ≤ ((3 / 2 : ℝ) * (normalizedBlockNorm Z₁ + normalizedBlockNorm V₁)) *
        ((3 / 2 : ℝ) * (normalizedBlockNorm Z₂ + normalizedBlockNorm V₂)) :=
      mul_le_mul h₁ h₂ (abs_nonneg _) (mul_nonneg (by norm_num) hn₁)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hm (mul_nonneg hn₁ hn₂)
      nlinarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Derivatives vanish almost everywhere on a level set. Countability of
the isolated points gives the one-dimensional statement; Fubini and
preservation of frame measure transfer it to the actual Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open Filter Set MeasureTheory EinsteinFour TraceHessian
open scoped _root_.Topology Manifold ContDiff

noncomputable section

/-- At a non-isolated point of a level set, the ordinary derivative is zero. -/
theorem derivative_zero_at_level_accPt {f : ℝ → ℝ} {x c v : ℝ}
    (hd : HasDerivAt f v x) (hx : f x = c)
    (ha : AccPt x (𝓟 {y | f y = c})) : v = 0 := by
  have hc : HasDerivWithinAt f 0 {y | f y = c} x :=
    (hasDerivWithinAt_const x {y | f y = c} c).congr
      (fun y hy => hy) hx
  exact ha.uniqueDiffWithinAt.eq_deriv _ hd.hasDerivWithinAt hc

/-- Nonzero derivatives on any one level form a countable set. -/
theorem countable_nonzero_derivative_on_level (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (c : ℝ) :
    {x | f x = c ∧ df x ≠ 0}.Countable := by
  let s : Set ℝ := {x | f x = c}
  apply (countable_setOfPred_isolated_right_within (s := s)).mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  have ha : ¬AccPt x (𝓟 s) := fun ha =>
    hx.2 (derivative_zero_at_level_accPt (hd x) hx.1 ha)
  have hb : 𝓝[s \ {x}] x = ⊥ := by
    simpa only [accPt_principal_iff_clusterPt, ClusterPt, nhdsWithin, not_neBot] using ha
  apply le_bot_iff.mp
  rw [← hb]
  apply nhdsWithin_mono
  intro y hy
  exact ⟨hy.1, by simp only [mem_singleton_iff]; exact ne_of_gt hy.2⟩

/-- Lebesgue almost everywhere, an ordinary derivative vanishes whenever
its function lies on a specified level. -/
theorem ae_derivative_zero_on_level (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (c : ℝ) :
    ∀ᵐ x, f x = c → df x = 0 := by
  rw [ae_iff]
  simpa only [_root_.not_imp, not_not] using
    (countable_nonzero_derivative_on_level f df hd c).measure_zero volume

/-- A measure-preserving flow transfers the one-dimensional level-set
statement to its base measure; no measure-zero assertion is a premise. -/
theorem ae_flow_derivative_zero_on_level
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) [SFinite μ]
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hp : ∀ t, MeasurePreserving (φ t) μ μ)
    (f df : Ω → ℝ) (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (c : ℝ) : ∀ᵐ x ∂μ, f x = c → df x = 0 := by
  have hfc : Continuous (fun p : Ω × ℝ => f (φ p.2 p.1)) :=
    hf.comp (hφ.comp continuous_swap)
  have hdc : Continuous (fun p : Ω × ℝ => df (φ p.2 p.1)) :=
    hdf.comp (hφ.comp continuous_swap)
  have hP : MeasurableSet {p : Ω × ℝ | f (φ p.2 p.1) = c → df (φ p.2 p.1) = 0} := by
    simp only [imp_iff_not_or]
    exact (measurableSet_eq_fun hfc.measurable measurable_const).compl.union
      (measurableSet_eq_fun hdc.measurable measurable_const)
  have hline : ∀ᵐ x ∂μ, ∀ᵐ t : ℝ, f (φ t x) = c → df (φ t x) = 0 :=
    Filter.Eventually.of_forall (fun x => ae_derivative_zero_on_level
      (fun t => f (φ t x)) (fun t => df (φ t x)) (fun t => hd t x) c)
  obtain ⟨t, ht⟩ := ((Measure.ae_ae_comm hP).mp hline).exists
  rw [ae_iff] at ht ⊢
  calc
    μ {x | ¬(f x = c → df x = 0)} =
        μ ((φ t) ⁻¹' {x | ¬(f x = c → df x = 0)}) :=
      ((hp t).measure_preimage_equiv _).symm
    _ = 0 := ht

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance zeroLevelNormedRing_rdf0d04_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance zeroLevelNormedSpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance zeroLevelNormedAlgebra_rdf0d04_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- The actual covariant Weyl gradient vanishes almost everywhere on the
zero set of its block. This justifies the zero-set case in the norm-weight
limit without assuming either Weyl block is everywhere nonzero. -/
theorem MetricGreenData.gradient_zero_ae_on_zero
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)} [SFinite μ]
    (d : MetricGreenData g μ) :
    ∀ᵐ e ∂μ, plusWeyl g e.base e.frame = 0 →
      ∀ i, plusWeylGradient g e.base e.frame i = 0 := by
  have hc (i : Fin 4) (a b : Fin 3) :
      ∀ᵐ e ∂μ, plusWeyl g e.base e.frame a b = 0 →
        plusWeylGradient g e.base e.frame i a b = 0 :=
    ae_flow_derivative_zero_on_level μ (fun t => (d.flow i).map t)
      (d.flow i).continuous (d.flow i).preserves
      (fun e => plusWeyl g e.base e.frame a b)
      (fun e => plusWeylGradient g e.base e.frame i a b)
      ((matrixEntryMap a b).continuous.comp d.continuousWeyl)
      ((matrixEntryMap a b).continuous.comp (d.continuousGradient i))
      (fun t e => hasDerivAt_matrixEntry (d.derivativeWeyl i t e) a b) 0
  have hall : ∀ᵐ e ∂μ, ∀ i a b, plusWeyl g e.base e.frame a b = 0 →
      plusWeylGradient g e.base e.frame i a b = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => hc i a b)))
  filter_upwards [hall] with e he
  intro hz i
  ext a b
  apply he i a b
  exact congrArg (fun A : Mat => A a b) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite four-by-four projection-cost kernel passes through the
smooth norm regularization, without any nonvanishing Weyl hypothesis. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology

noncomputable section

local instance matrixWeightNormedRing_rdf0d04_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance matrixWeightNormedSpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance matrixWeightNormedAlgebra_rdf0d04_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem abs_regularizedMatrixWeight_le (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (Z V : Fin 4 → Mat) (K : Fin 4 → Fin 4 → ℝ)
    (hZ : ∀ i, symmetric (Z i)) (hV : ∀ i, symmetric (V i))
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedMatrixWeight ε A B Z V K| ≤
      ∑ i, ∑ j, 144 * (normalizedBlockNorm (Z i) + normalizedBlockNorm (V i)) *
        (normalizedBlockNorm (Z j) + normalizedBlockNorm (V j)) * |K i j| := by
  unfold regularizedMatrixWeight
  calc
    _ ≤ ∑ i, |∑ j, (regularizedWeylWeightDerivative ε A B (Z i) (V i) *
        regularizedWeylWeightDerivative ε A B (Z j) (V j) / regularizedWeylWeight ε A B) * K i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (regularized_weight_mixed_cost_le ε hε he
        A B (Z i) (Z j) (V i) (V j) (hZ i) (hZ j) (hV i) (hV j) hpinch) (abs_nonneg _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Simultaneous dominated convergence for the scalar, cubic, and projection
terms of the weighted Hessian estimate. All derivative indices are the
four actual frame directions. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology

noncomputable section

local instance hessianWeightNormedRing_rdf0d04_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianWeightNormedSpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianWeightNormedAlgebra_rdf0d04_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem regularizedHessianWeight_bound (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (Z V : Fin 4 → Mat) (F : ℝ) (G : Fin 4 → ℝ)
    (K : Fin 4 → Fin 4 → ℝ) (hZ : ∀ i, symmetric (Z i)) (hV : ∀ i, symmetric (V i))
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedHessianWeight ε A B Z V F G K| ≤
      4 * |F| + (∑ i, (3 / 2 : ℝ) *
        (normalizedBlockNorm (Z i) + normalizedBlockNorm (V i)) * |G i|) +
      ∑ i, ∑ j, 144 * (normalizedBlockNorm (Z i) + normalizedBlockNorm (V i)) *
        (normalizedBlockNorm (Z j) + normalizedBlockNorm (V j)) * |K i j| := by
  have hscalar : |regularizedWeylWeight ε A B * F| ≤ 4 * |F| := by
    rw [abs_mul, abs_of_pos (regularizedWeylWeight_pos ε hε.le he A B hpinch)]
    exact mul_le_mul_of_nonneg_right
      (regularizedWeylWeight_bounds ε hε.le he A B hpinch).2 (abs_nonneg _)
  have hlinear : |∑ i, regularizedWeylWeightDerivative ε A B (Z i) (V i) * G i| ≤
      ∑ i, (3 / 2 : ℝ) * (normalizedBlockNorm (Z i) + normalizedBlockNorm (V i)) * |G i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_regularizedWeylWeightDerivative_le
      ε hε he A B (Z i) (V i) (hZ i) (hV i) hpinch) (abs_nonneg _)
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add hscalar hlinear))
    (abs_regularizedMatrixWeight_le ε hε he A B Z V K hZ hV hpinch))

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integral_regularizedHessianWeight_tendsto
    (A B : Ω → Mat) (Z V : Fin 4 → Ω → Mat) (F : Ω → ℝ)
    (G : Fin 4 → Ω → ℝ) (K : Fin 4 → Fin 4 → Ω → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hZ : ∀ i, Continuous (Z i))
    (hV : ∀ i, Continuous (V i)) (hF : Continuous F)
    (hG : ∀ i, Continuous (G i)) (hK : ∀ i j, Continuous (K i j))
    (hsZ : ∀ i x, symmetric (Z i x)) (hsV : ∀ i x, symmetric (V i x))
    (hpinch : ∀ x, normalizedBlockNorm (A x) + normalizedBlockNorm (B x) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, regularizedHessianWeight (ε n) (A x) (B x)
      (fun i => Z i x) (fun i => V i x) (F x) (fun i => G i x)
        (fun i j => K i j x) ∂μ) atTop
      (𝓝 (∫ x, regularizedHessianWeight 0 (A x) (B x)
        (fun i => Z i x) (fun i => V i x) (F x) (fun i => G i x)
          (fun i j => K i j x) ∂μ)) := by
  let N : Fin 4 → Ω → ℝ := fun i x => normalizedBlockNorm (Z i x) + normalizedBlockNorm (V i x)
  have hN (i) : Continuous (N i) :=
    (continuous_normalizedBlockNorm.comp (hZ i)).add
      (continuous_normalizedBlockNorm.comp (hV i))
  apply tendsto_integral_of_dominated_convergence
    (fun x => 4 * |F x| + (∑ i, (3 / 2 : ℝ) * N i x * |G i x|) +
      ∑ i, ∑ j, 144 * N i x * N j x * |K i j x|)
  · intro n
    have hd (i : Fin 4) := continuous_regularizedWeylWeightDerivative (ε n) (hε n)
      A B (Z i) (V i) hA hB (hZ i) (hV i)
    have hw := continuous_regularizedWeylWeight (ε n) A B hA hB
    have hp x := ne_of_gt (regularizedWeylWeight_pos (ε n) (hε n).le (he n) _ _ (hpinch x))
    apply Continuous.aestronglyMeasurable
    unfold regularizedHessianWeight regularizedMatrixWeight
    exact ((hw.mul hF).add (continuous_finsetSum _ (fun i _ => (hd i).mul (hG i)))).add
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        (((hd i).mul (hd j)).div hw hp).mul (hK i j))))
  · have hc : Continuous (fun x => 4 * |F x| + (∑ i, (3 / 2 : ℝ) * N i x * |G i x|) +
        ∑ i, ∑ j, 144 * N i x * N j x * |K i j x|) :=
      ((continuous_const.mul hF.abs).add (continuous_finsetSum _ (fun i _ =>
        (continuous_const.mul (hN i)).mul (hG i).abs))).add
        (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
          ((continuous_const.mul (hN i)).mul (hN j)).mul (hK i j).abs)))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact regularizedHessianWeight_bound (ε n) (hε n) (he n) _ _ _ _ _ _ _
      (fun i => hsZ i x) (fun i => hsV i x) (hpinch x)
  · filter_upwards [] with x
    have hd (i : Fin 4) : Tendsto
        (fun n => regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z i x) (V i x)) atTop
        (𝓝 (regularizedWeylWeightDerivative 0 (A x) (B x) (Z i x) (V i x))) := by
      simpa only [Function.comp_def, regularizedWeylWeightDerivative,
        regularizedRadialDerivative, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeightDerivative (A x) (B x) (Z i x) (V i x)).comp hlim
    have hw : Tendsto (fun n => regularizedWeylWeight (ε n) (A x) (B x)) atTop
        (𝓝 (regularizedWeylWeight 0 (A x) (B x))) := by
      simpa only [Function.comp_def, regularizedWeylWeight, regularizedBlockNorm_zero] using
        (tendsto_regularizedWeylWeight (A x) (B x)).comp hlim
    have hl : Tendsto (fun n => ∑ i,
        regularizedWeylWeightDerivative (ε n) (A x) (B x) (Z i x) (V i x) * G i x) atTop
        (𝓝 (∑ i, regularizedWeylWeightDerivative 0 (A x) (B x) (Z i x) (V i x) * G i x)) :=
      tendsto_finsetSum _ (fun i _ => (hd i).mul tendsto_const_nhds)
    have hk : Tendsto (fun n => regularizedMatrixWeight (ε n) (A x) (B x)
        (fun i => Z i x) (fun i => V i x) (fun i j => K i j x)) atTop
        (𝓝 (regularizedMatrixWeight 0 (A x) (B x)
          (fun i => Z i x) (fun i => V i x) (fun i j => K i j x))) := by
      unfold regularizedMatrixWeight
      apply tendsto_finsetSum
      intro i _
      apply tendsto_finsetSum
      intro j _
      exact (((hd i).mul (hd j)).div hw (ne_of_gt
        (regularizedWeylWeight_pos 0 (by norm_num) (by norm_num) _ _ (hpinch x)))).mul
          tendsto_const_nhds
    exact ((hw.mul tendsto_const_nhds).add hl).add hk

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quadratic and radial scalar contractions are unchanged by the
pointwise spectral frame. These are identities on finite arrays. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem matrixSlotAction_sum_smul {ι : Type*} [Fintype ι]
    (A : Mat) (c : ι → ℝ) (B : ι → Mat) :
    matrixSlotAction A (∑ j, c j • B j) = ∑ j, c j • matrixSlotAction A (B j) := by
  change (slotLinear A) (∑ j, c j • B j) = _
  rw [map_sum]
  simp only [map_smul]
  rfl

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The opposite Weyl block has the same derived gradient constraints and
zero-set calculus, using its actual parallel-frame derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem OppositeWeylData.gradientConstraints {d : MetricGreenData g μ}
    (o : OppositeWeylData d) (e : FrameBundle g) :
    (∀ i, TraceHessian.symmetric (minusWeylGradient g e.base e.frame i)) ∧
    (∀ i, TraceHessian.traceFree (minusWeylGradient g e.base e.frame i)) := by
  have hi (i : Fin 4) : TraceHessian.symmetric (minusWeylGradient g e.base e.frame i) ∧
      TraceHessian.traceFree (minusWeylGradient g e.base e.frame i) := by
    obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
    change (d.flow i).map 0 e₀ = e at he
    have hs := symmetric_of_hasDerivAt (o.derivativeWeyl i 0 e₀)
      (fun t => o.symmetric ((d.flow i).map t e₀))
    have ht := traceFree_of_hasDerivAt (o.derivativeWeyl i 0 e₀)
      (fun t => o.traceFree ((d.flow i).map t e₀))
    rw [he] at hs ht
    exact ⟨hs, ht⟩
  exact ⟨fun i => (hi i).1, fun i => (hi i).2⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projection cost is a four-by-four quadratic form in the
weight derivative. This finite expansion is used for its integral limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem highestProjectionMap_apply (X : Hessian) : highestProjectionMap X = highestProjection X := rfl

theorem weightTensor_basis_sum (a : Vec) (Z : Tensor) :
    weightTensor a Z = ∑ i, a i • weightTensor (derivativeBasis i) Z := by
  ext j k b c
  simp [Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply,
    weightTensor, derivativeBasis]

theorem projection_weight_cost_expansion (A U : Mat) (Z : Tensor) (a : Vec) (m : ℝ) :
    generalCurvaturePairing A U (highestProjection (weightTensor a Z))
      (highestProjection (weightTensor a Z)) / (24 * m) =
        ∑ i, ∑ j, (a i * a j / m) * projectedWeightKernel A U Z i j := by
  have hP : highestProjection (weightTensor a Z) =
      ∑ i, a i • highestProjection (weightTensor (derivativeBasis i) Z) := by
    change highestProjectionMap (weightTensor a Z) = _
    rw [weightTensor_basis_sum, map_sum]
    simp only [map_smul, highestProjectionMap_apply]
  rw [hP]
  simp only [Fin.sum_univ_four, generalCurvaturePairing_add_left,
    generalCurvaturePairing_add_right, generalCurvaturePairing_smul_left,
    generalCurvaturePairing_smul_right, projectedWeightKernel]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem MetricGreenData.continuousProjectedWeightKernel
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (o : OppositeWeylData d) (i j : Fin 4) :
    Continuous (fun e : FrameBundle g => projectedWeightKernel
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusGradientTensor g e.base e.frame) i j) := by
  have h (k : Fin 4) : Continuous (fun e : FrameBundle g =>
      highestProjection (weightTensor (derivativeBasis k) (plusGradientTensor g e.base e.frame))) := by
    exact continuous_highestProjection.comp
      (d.continuousWeightTensor (fun l => ContinuousMap.const _ (if l = k then 1 else 0)))
  exact (continuous_generalCurvaturePairing d.continuousWeyl o.continuousWeyl (h i) (h j)).div_const 24

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projection term in the metric Hessian estimate converges
under norm regularization, including at zeros of either Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem regularizedProjectionCost_eq_matrixWeight (g : SmoothMetric M) (ε : ℝ)
    (e : FrameBundle g) :
    regularizedProjectionCost g ε e =
      regularizedMatrixWeight ε (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame)
        (projectedWeightKernel (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusGradientTensor g e.base e.frame)) :=
  projection_weight_cost_expansion _ _ _ _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual global Hessian inequality for the nonsmooth norm weight.
The limit is proved on the original Weyl tensors, including their zeros. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem regularizedHessianIntegrand_eq_weight (g : SmoothMetric M) (ε : ℝ)
    (e : FrameBundle g) :
    regularizedHessianIntegrand g ε e =
      regularizedHessianWeight ε (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame)
        (invariantHessianForm (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame))
        (fun i => -(5 / 36 : ℝ) * Matrix.trace (plusWeylGradient g e.base e.frame i *
          (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j)))
        (projectedWeightKernel (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusGradientTensor g e.base e.frame)) := by
  have hc := regularizedProjectionCost_eq_matrixWeight g ε e
  change regularizedWeylWeight ε _ _ * _ - (5 / 36 : ℝ) * _ +
    regularizedProjectionCost g ε e = _
  rw [hc]
  unfold regularizedHessianWeight
  congr 1
  rw [Finset.mul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem integral_regularizedHessian_tendsto (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (he : ∀ n, ε n ≤ 1 / 3)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e, regularizedHessianIntegrand g (ε n) e ∂μ) atTop
      (𝓝 (∫ e, regularizedHessianIntegrand g 0 e ∂μ)) := by
  simp_rw [regularizedHessianIntegrand_eq_weight]
  exact integral_regularizedHessianWeight_tendsto μ _ _ _ _ _ _ _
    d.continuousWeyl o.continuousWeyl d.continuousGradient o.continuousGradient
    (d.invariantHessianField o).continuous (fun i => (d.cubicEntryField i).continuous)
    (d.continuousProjectedWeightKernel o)
    (fun i e => (d.gradientConstraints e).1 i)
    (fun i e => (o.gradientConstraints e).1 i) hpinch ε hε he hlim

/-- The nonsmooth norm weight satisfies the actual integrated Hessian
inequality. No positivity of either Weyl norm is required. -/
theorem unregularizedHessianGreen (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    0 ≤ ∫ e, regularizedHessianIntegrand g 0 e ∂μ := by
  let ε : ℕ → ℝ := fun n => (1 / 3 : ℝ) * (1 / ((n : ℝ) + 1))
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have he (n) : ε n ≤ 1 / 3 := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hi : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) := by
      exact (div_le_one (by positivity)).mpr hn
    dsimp [ε]
    nlinarith
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 3 : ℝ)
  exact ge_of_tendsto' (d.integral_regularizedHessian_tendsto o hpinch ε hε he hlim)
    (fun n => d.regularizedHessianGreen o hp hdecomp hpinch (ε n) (hε n) (he n))

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Bianchi triple becomes the positive triple after
reflecting only the derivative index. This gives the same invariant Kato
bound for the actual opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem reflectedGradient_energy (Z : Angular.Gradient) :
    weylGradientEnergy (reflectedGradient Z) = weylGradientEnergy Z := by
  unfold weylGradientEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold matrixPairing
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [reflectedGradient, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = orientationSign i ^ 2 * (Z i a b * Z i a b) := by ring
    _ = _ := by rw [orientationSign_sq, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regularized scalar Weyl equation follows from ordinary derivatives
of the actual block and its proved matrix Laplacian. Test functions are
arbitrary smooth flow weights, ready for the polynomial coupling test. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem regularizedRadialField_derivative (d : MetricGreenData g μ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => d.regularizedRadialField ε hε i ((d.flow i).map s e))
      (d.regularizedSecondField ε hε i ((d.flow i).map t e)) t :=
  hasDerivAt_regularizedRadialDerivative (d.derivativeWeyl i t e)
    (d.derivativeGradient i i t e) (fun s => d.weyl.symmetric ((d.flow i).map s e)) hε

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normEquationNormedRing
local instance normEquationNormedSpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normEquationNormedAlgebra
/-- The weak scalar norm equation at positive regularization. Its matrix
Laplacian term is fixed by the proved Bianchi commutator equation. -/
theorem testedRegularizedNormEquation (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 < ε) (k : C(FrameBundle g, ℝ))
    (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    (∫ e, k e * ((weylGradientEnergy (plusWeylGradient g e.base e.frame) +
        Matrix.trace (plusWeyl g e.base e.frame * weylLaplacian (plusWeyl g e.base e.frame)) / 6 -
        ∑ i, (d.regularizedRadialField ε hε i e) ^ 2) / d.regularizedNormField ε e) +
      ∑ i, dk i e * d.regularizedRadialField ε hε i e ∂μ) = 0 := by
  let P := d.regularizedRadialField ε hε
  let Q := d.regularizedSecondField ε hε
  let F : Fin 4 → C(FrameBundle g, ℝ) := fun i => k * P i
  let D : Fin 4 → C(FrameBundle g, ℝ) := fun i => dk i * P i + k * Q i
  have hd (i) : (∫ e, D i e ∂μ) = 0 := by
    apply Averages.integral_flow_derivative_zero μ (d.flow i).map
      (d.flow i).continuous (d.flow i).preserves (F i) (D i)
    intro t e
    exact (hk i t e).mul (d.regularizedRadialField_derivative ε hε i t e)
  have hi (i : Fin 4) : Integrable (fun e => D i e) μ :=
    (D i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : (∫ e, ∑ i, D i e ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun i _ => hi i)]
    simp only [hd, Finset.sum_const_zero]
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with e
  have heq := regularizedRadialSecond_sum ε (plusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame) (plusWeylHessian g e.base e.frame)
    (d.gradientConstraints e).1 (metric_weyl_trace g d.weyl e)
  change k e * _ + (∑ i, dk i e * P i e) =
    ∑ i, (dk i e * P i e + k e * Q i e)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change (∑ i, Q i e) = _ at heq
  rw [heq]
  dsimp only [regularizedNormField, regularizedRadialField, ContinuousMap.coe_mk]
  ring

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability at a zero Weyl norm is obtained from uniformly bounded
regularized energies and Fatou's lemma. No integrability of the singular
quotient is assumed in the limiting argument. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology

noncomputable section

theorem integrable_of_ae_limit_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, ‖F n x‖ ∂μ) ≤ C) : Integrable f μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hF n).aestronglyMeasurable) hlim, ?_⟩
  have hf : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤
      liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ‖F n x‖ₑ) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono (fun x hx => hx.enorm.liminf_eq.symm))
      _ ≤ _ := lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.enorm)
  have hb : liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    apply iSup_le
    intro n
    refine (iInf₂_le n le_rfl).trans ?_
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact lt_of_le_of_lt (hf.trans hb) ENNReal.ofReal_lt_top

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Integrability of the actual nonsmooth Hessian integrand, obtained from
its smooth approximants and their existing common domination. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

local instance hessianIntegrabilityRing_rdf0d04_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianIntegrabilitySpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianIntegrabilityAlgebra_rdf0d04_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem tendsto_regularizedHessianWeight_zero
    (A B : Mat) (Z V : Fin 4 → Mat) (F : ℝ) (G : Fin 4 → ℝ)
    (K : Fin 4 → Fin 4 → ℝ)
    (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => regularizedHessianWeight (ε n) A B Z V F G K) atTop
      (𝓝 (regularizedHessianWeight 0 A B Z V F G K)) := by
  have hd (i : Fin 4) : Tendsto
      (fun n => regularizedWeylWeightDerivative (ε n) A B (Z i) (V i)) atTop
      (𝓝 (regularizedWeylWeightDerivative 0 A B (Z i) (V i))) := by
    simpa only [Function.comp_def, regularizedWeylWeightDerivative,
      regularizedRadialDerivative, regularizedBlockNorm_zero] using
      (tendsto_regularizedWeylWeightDerivative A B (Z i) (V i)).comp hlim
  have hw : Tendsto (fun n => regularizedWeylWeight (ε n) A B) atTop
      (𝓝 (regularizedWeylWeight 0 A B)) := by
    simpa only [Function.comp_def, regularizedWeylWeight, regularizedBlockNorm_zero] using
      (tendsto_regularizedWeylWeight A B).comp hlim
  have hl := tendsto_finsetSum Finset.univ (fun i _ => (hd i).mul
    (tendsto_const_nhds (x := G i)))
  have hk : Tendsto (fun n => regularizedMatrixWeight (ε n) A B Z V K) atTop
      (𝓝 (regularizedMatrixWeight 0 A B Z V K)) := by
    unfold regularizedMatrixWeight
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (((hd i).mul (hd j)).div hw (ne_of_gt
      (regularizedWeylWeight_pos 0 (by norm_num) (by norm_num) A B hpinch))).mul
        tendsto_const_nhds
  exact ((hw.mul tendsto_const_nhds).add hl).add hk

section Integral

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

local instance hessianIntegrabilityRing_rdf0d04_2 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianIntegrabilitySpace_rdf0d04_2 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianIntegrabilityAlgebra_rdf0d04_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem integrable_regularizedHessianWeight_zero
    (A B : Ω → Mat) (Z V : Fin 4 → Ω → Mat) (F : Ω → ℝ)
    (G : Fin 4 → Ω → ℝ) (K : Fin 4 → Fin 4 → Ω → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hZ : ∀ i, Continuous (Z i))
    (hV : ∀ i, Continuous (V i)) (hF : Continuous F)
    (hG : ∀ i, Continuous (G i)) (hK : ∀ i j, Continuous (K i j))
    (hsZ : ∀ i x, symmetric (Z i x)) (hsV : ∀ i x, symmetric (V i x))
    (hpinch : ∀ x, normalizedBlockNorm (A x) + normalizedBlockNorm (B x) < 2) :
    Integrable (fun x => regularizedHessianWeight 0 (A x) (B x)
      (fun i => Z i x) (fun i => V i x) (F x) (fun i => G i x)
        (fun i j => K i j x)) μ := by
  let ε : ℕ → ℝ := fun n => (1 / 3 : ℝ) * (1 / ((n : ℝ) + 1))
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have he (n) : ε n ≤ 1 / 3 := by
    have hi : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [ε]
    linarith
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 3 : ℝ)
  let N : Fin 4 → Ω → ℝ := fun i x => normalizedBlockNorm (Z i x) + normalizedBlockNorm (V i x)
  let bound : Ω → ℝ := fun x => 4 * |F x| +
    (∑ i, (3 / 2 : ℝ) * N i x * |G i x|) +
    ∑ i, ∑ j, 144 * N i x * N j x * |K i j x|
  have hN (i) : Continuous (N i) :=
    (continuous_normalizedBlockNorm.comp (hZ i)).add
      (continuous_normalizedBlockNorm.comp (hV i))
  have hb : Integrable bound μ := by
    have hc : Continuous bound :=
      ((continuous_const.mul hF.abs).add (continuous_finsetSum _ (fun i _ =>
        (continuous_const.mul (hN i)).mul (hG i).abs))).add
        (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
          ((continuous_const.mul (hN i)).mul (hN j)).mul (hK i j).abs)))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let f : ℕ → Ω → ℝ := fun n x => regularizedHessianWeight (ε n) (A x) (B x)
    (fun i => Z i x) (fun i => V i x) (F x) (fun i => G i x) (fun i j => K i j x)
  have hf (n) : Integrable (f n) μ := by
    have hd (i : Fin 4) := continuous_regularizedWeylWeightDerivative (ε n) (hε n)
      A B (Z i) (V i) hA hB (hZ i) (hV i)
    have hw := continuous_regularizedWeylWeight (ε n) A B hA hB
    have hp x := ne_of_gt (regularizedWeylWeight_pos (ε n) (hε n).le (he n) _ _ (hpinch x))
    have hc : Continuous (f n) := by
      unfold f regularizedHessianWeight regularizedMatrixWeight
      exact ((hw.mul hF).add (continuous_finsetSum _ (fun i _ => (hd i).mul (hG i)))).add
        (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
          (((hd i).mul (hd j)).div hw hp).mul (hK i j))))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ f _ (∫ x, bound x ∂μ) hf
  · filter_upwards [] with x
    exact tendsto_regularizedHessianWeight_zero _ _ _ _ _ _ _ (hpinch x) ε hlim
  · intro n
    apply integral_mono_ae (hf n).norm hb
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact regularizedHessianWeight_bound (ε n) (hε n) (he n) _ _ _ _ _ _ _
      (fun i => hsZ i x) (fun i => hsV i x) (hpinch x)

end Integral

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.hessianIntegrand_integrable (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    Integrable (regularizedHessianIntegrand g 0) μ := by
  change Integrable (fun e => regularizedHessianIntegrand g 0 e) μ
  simp_rw [regularizedHessianIntegrand_eq_weight]
  exact integrable_regularizedHessianWeight_zero μ _ _ _ _ _ _ _
    d.continuousWeyl o.continuousWeyl d.continuousGradient o.continuousGradient
    (d.invariantHessianField o).continuous (fun i => (d.cubicEntryField i).continuous)
    (d.continuousProjectedWeightKernel o)
    (fun i e => (d.gradientConstraints e).1 i)
    (fun i e => (o.gradientConstraints e).1 i) hpinch

end
end PositiveEinsteinFour.Geometry
end


section

/-! The singular Weyl energy quotient is integrable. The refined Kato
inequality is kept as a local intermediate input, to be supplied by the
pointwise Bianchi parametrization; no weak norm equation is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

local instance normIntegrabilityNormedRing_rdf0d04_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance normIntegrabilityNormedSpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance normIntegrabilityNormedAlgebra_rdf0d04_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem regularized_norm_laplacian_split (ε : ℝ) (A : Mat) (e p : ℝ) :
    (e + Matrix.trace (A * weylLaplacian A) / 6 - p) / regularizedBlockNorm ε A =
      (e - p) / regularizedBlockNorm ε A +
        regularizedRadialDerivative ε A (weylLaplacian A) := by
  unfold regularizedRadialDerivative
  ring

theorem weylGradientEnergy_nonneg (Z : Fin 4 → Mat) : 0 ≤ weylGradientEnergy Z := by
  unfold weylGradientEnergy matrixPairing
  exact div_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ =>
    Finset.sum_nonneg (fun b _ => mul_self_nonneg _)))) (by norm_num)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

local instance normIntegrabilityNormedRing_rdf0d04_2 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance normIntegrabilityNormedSpace_rdf0d04_2 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance normIntegrabilityNormedAlgebra_rdf0d04_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem regularizedEnergyQuotient_bound (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (ε : ℝ) (hε : 0 < ε) :
    (∫ e, weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      regularizedBlockNorm ε (plusWeyl g e.base e.frame) ∂μ) ≤
      (5 / 2 : ℝ) * ∫ e, normalizedBlockNorm (weylLaplacian (plusWeyl g e.base e.frame)) ∂μ := by
  let E := d.gradientEnergyField
  let N := d.regularizedNormField ε
  let P : C(FrameBundle g, ℝ) := ⟨fun e => ∑ i, (d.regularizedRadialField ε hε i e) ^ 2,
    by fun_prop⟩
  let T : C(FrameBundle g, ℝ) :=
    ⟨fun e => regularizedRadialDerivative ε (plusWeyl g e.base e.frame)
      (weylLaplacian (plusWeyl g e.base e.frame)),
      continuous_regularizedRadialDerivative ε hε _ _ d.continuousWeyl
        (continuous_weylLaplacian.comp d.continuousWeyl)⟩
  let L := d.laplacianNormField
  have hN e : 0 < N e := regularizedBlockNorm_pos ε hε _
  let F : C(FrameBundle g, ℝ) := ⟨fun e => E e / N e,
    E.continuous.div N.continuous (fun e => (hN e).ne')⟩
  let Q : C(FrameBundle g, ℝ) := ⟨fun e => (E e - P e) / N e + T e,
    ((E.continuous.sub P.continuous).div N.continuous (fun e => (hN e).ne')).add T.continuous⟩
  have hQ : (∫ e, Q e ∂μ) = 0 := by
    have h := d.testedRegularizedNormEquation ε hε (ContinuousMap.const _ 1)
      (fun _ => ContinuousMap.const _ 0) (by intro i t e; exact hasDerivAt_const t 1)
    simpa only [Q, E, N, P, T, ContinuousMap.coe_const, Function.const_apply, one_mul, zero_mul,
      Finset.sum_const_zero, add_zero, regularizedNormField, regularizedRadialField,
      gradientEnergyField, gradientMap, ContinuousMap.coe_mk, regularized_norm_laplacian_split] using h
  have hpoint (e : FrameBundle g) : F e ≤ (5 / 2 : ℝ) * (Q e + L e) := by
    have hP := regularized_radial_energy_le ε hε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)
    have hK := hkato e
    change P e ≤ _ at hP
    change _ ≤ E e at hK
    have he : E e ≤ (5 / 2 : ℝ) * (E e - P e) := by linarith
    have hd := div_le_div_of_nonneg_right he (hN e).le
    have ht := (abs_le.mp (abs_regularizedRadialDerivative_le ε hε
      (plusWeyl g e.base e.frame) (weylLaplacian (plusWeyl g e.base e.frame))
      (weylLaplacian_symmetric _ (d.weyl.symmetric e)))).1
    change -L e ≤ T e at ht
    rw [mul_div_assoc] at hd
    change E e / N e ≤ (5 / 2 : ℝ) * ((E e - P e) / N e + T e + L e)
    nlinarith only [hd, ht]
  have hFi : Integrable F μ := F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQi : Integrable Q μ := Q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLi : Integrable L μ := L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ e, F e ∂μ) ≤ (5 / 2 : ℝ) * ∫ e, L e ∂μ
  calc
    _ ≤ ∫ e, (5 / 2 : ℝ) * (Q e + L e) ∂μ :=
      integral_mono hFi ((hQi.add hLi).const_mul _) hpoint
    _ = (5 / 2 : ℝ) * ∫ e, L e ∂μ := by
      rw [integral_const_mul, integral_add hQi hLi, hQ, zero_add]

theorem integrableEnergyQuotient (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame)) :
    Integrable (fun e => weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → FrameBundle g → ℝ := fun n e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      regularizedBlockNorm (ε n) (plusWeyl g e.base e.frame)
  apply integrable_of_ae_limit_norm_bound μ F _
    ((5 / 2 : ℝ) * ∫ e, d.laplacianNormField e ∂μ)
  · intro n
    exact (d.gradientEnergyField.continuous.div (d.regularizedNormField (ε n)).continuous
      (fun e => (regularizedBlockNorm_pos (ε n) (hε n) _).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · filter_upwards [d.gradient_zero_ae_on_zero] with e he
    by_cases hv : normalizedBlockNorm (plusWeyl g e.base e.frame) = 0
    · have hA := (normalizedBlockNorm_eq_zero_iff _).mp hv
      have hZ := he hA
      have hz : weylGradientEnergy (plusWeylGradient g e.base e.frame) = 0 := by
        simp only [weylGradientEnergy, hZ, matrixPairing, Matrix.zero_apply, mul_zero,
          Finset.sum_const_zero, zero_div]
      simp only [F, hz, zero_div]
      exact tendsto_const_nhds
    · exact tendsto_const_nhds.div ((tendsto_regularizedBlockNorm _).comp hεlim) hv
  · intro n
    have heq : (fun e => ‖F n e‖) = F n := by
      funext e
      apply Real.norm_of_nonneg
      exact div_nonneg (weylGradientEnergy_nonneg _) (regularizedBlockNorm_pos (ε n) (hε n) _).le
    rw [heq]
    exact d.regularizedEnergyQuotient_bound hkato (ε n) (hε n)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Weyl equation at zero regularization. Its singular energy
term is controlled by the proved integrable energy quotient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

theorem abs_scalarNormExpression_le (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (hA : symmetric A)
    (hz : normalizedBlockNorm A = 0 → Z = 0)
    (hk : ‖blockRadialGradient A Z‖ ^ 2 ≤ weylGradientEnergy Z) :
    |scalarNormExpression ε A Z| ≤ weylGradientEnergy Z / normalizedBlockNorm A +
      normalizedBlockNorm (weylLaplacian A) := by
  have he := weylGradientEnergy_nonneg Z
  have hn := regularizedBlockNorm_pos ε hε A
  have hp := regularized_radial_energy_le ε hε A Z
  have hpn : 0 ≤ ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hq : 0 ≤ (weylGradientEnergy Z -
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) / regularizedBlockNorm ε A :=
    div_nonneg (by linarith) hn.le
  have hb : (weylGradientEnergy Z -
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) / regularizedBlockNorm ε A ≤
      weylGradientEnergy Z / normalizedBlockNorm A := by
    by_cases hv : normalizedBlockNorm A = 0
    · have hZ := hz hv
      subst Z
      simp [weylGradientEnergy, matrixPairing, regularizedRadialDerivative]
    · exact (div_le_div_of_nonneg_right (sub_le_self _ hpn) hn.le).trans
        (div_le_div_of_nonneg_left he
          (lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv))
          (norm_le_regularizedBlockNorm ε A))
  exact (abs_add_le _ _).trans (add_le_add
    (by rwa [abs_of_nonneg hq])
    (abs_regularizedRadialDerivative_le ε hε A (weylLaplacian A)
      (weylLaplacian_symmetric A hA)))

theorem tendsto_scalarNormExpression (A : Mat) (Z : Fin 4 → Mat)
    (hz : normalizedBlockNorm A = 0 → Z = 0) :
    Tendsto (fun ε => scalarNormExpression ε A Z) (𝓝 0)
      (𝓝 (scalarNormExpression 0 A Z)) := by
  have ht := tendsto_regularizedRadialDerivative A (weylLaplacian A)
  have hp (i : Fin 4) : Tendsto (fun ε => regularizedRadialDerivative ε A (Z i))
      (𝓝 0) (𝓝 (regularizedRadialDerivative 0 A (Z i))) := by
    simpa [regularizedRadialDerivative, regularizedBlockNorm_zero] using
      tendsto_regularizedRadialDerivative A (Z i)
  have ht' : Tendsto (fun ε => regularizedRadialDerivative ε A (weylLaplacian A))
      (𝓝 0) (𝓝 (regularizedRadialDerivative 0 A (weylLaplacian A))) := by
    simpa [regularizedRadialDerivative, regularizedBlockNorm_zero] using ht
  by_cases hv : normalizedBlockNorm A = 0
  · have hZ := hz hv
    subst Z
    simpa [scalarNormExpression, weylGradientEnergy, matrixPairing,
      regularizedRadialDerivative] using ht'
  · exact ((tendsto_const_nhds.sub (tendsto_finsetSum _ (fun i _ => (hp i).pow 2))).div
      (by simpa only [regularizedBlockNorm_zero] using tendsto_regularizedBlockNorm A)
      (by simpa only [regularizedBlockNorm_zero] using hv)).add ht'

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pass the actual weak norm equation through bounded smooth test
approximations, including their first derivatives. This is the limit used
for the polynomial multiplier in the two-block coupling. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem testedNormEquation_of_limits (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (k : ℕ → C(FrameBundle g, ℝ)) (dk : ℕ → Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ n i t e, HasDerivAt (fun s => k n ((d.flow i).map s e))
      (dk n i ((d.flow i).map t e)) t)
    (k₀ : FrameBundle g → ℝ) (dk₀ : Fin 4 → FrameBundle g → ℝ)
    (hklim : ∀ e, Tendsto (fun n => k n e) atTop (𝓝 (k₀ e)))
    (hdlim : ∀ i e, Tendsto (fun n => dk n i e) atTop (𝓝 (dk₀ i e)))
    (C : ℝ) (hC : 0 ≤ C) (hkbound : ∀ n e, |k n e| ≤ C)
    (B : Fin 4 → C(FrameBundle g, ℝ)) (hdbound : ∀ n i e, |dk n i e| ≤ B i e) :
    (∫ e, k₀ e * scalarNormExpression 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
      ∑ i, dk₀ i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) ∂μ) = 0 := by
  let F : ℕ → FrameBundle g → ℝ := fun n e =>
    k n e * d.scalarNormField (ε n) (hε n) e +
      ∑ i, dk n i e * d.regularizedRadialField (ε n) (hε n) i e
  let H : FrameBundle g → ℝ := fun e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame) + d.laplacianNormField e
  let J : C(FrameBundle g, ℝ) := ⟨fun e =>
    ∑ i, B i e * normalizedBlockNorm (plusWeylGradient g e.base e.frame i), by
      apply continuous_finsetSum
      intro i _
      exact (B i).continuous.mul (continuous_normalizedBlockNorm.comp (d.continuousGradient i))⟩
  have hF (n) : Continuous (F n) := by
    exact ((k n).continuous.mul (d.scalarNormField (ε n) (hε n)).continuous).add
      (continuous_finsetSum _ (fun i _ => (dk n i).continuous.mul
        (d.regularizedRadialField (ε n) (hε n) i).continuous))
  have hH : Integrable H μ := (d.integrableEnergyQuotient hkato).add
    (d.laplacianNormField.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hconv : Tendsto (fun n => ∫ e, F n e ∂μ) atTop
      (𝓝 (∫ e, k₀ e * scalarNormExpression 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
        ∑ i, dk₀ i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun e => C * H e + J e)
    · exact fun n => (hF n).aestronglyMeasurable
    · exact (hH.const_mul C).add (J.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    · intro n
      filter_upwards [d.gradient_zero_ae_on_zero] with e he
      have hs := abs_scalarNormExpression_le (ε n) (hε n) _ _ (d.weyl.symmetric e)
        (fun hv => funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))
        (by
          have h := hkato e
          have hp := sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
            (plusWeylGradient g e.base e.frame)‖
          nlinarith)
      rw [Real.norm_eq_abs]
      change |k n e * d.scalarNormField (ε n) (hε n) e +
        ∑ i, dk n i e * d.regularizedRadialField (ε n) (hε n) i e| ≤ _
      calc
        _ ≤ |k n e * d.scalarNormField (ε n) (hε n) e| +
            ∑ i, |dk n i e * d.regularizedRadialField (ε n) (hε n) i e| :=
          (abs_add_le _ _).trans (add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _))
        _ ≤ C * H e + J e := by
          apply add_le_add
          · rw [abs_mul]
            exact mul_le_mul (hkbound n e) hs (abs_nonneg _) hC
          · change _ ≤ ∑ i, B i e * normalizedBlockNorm (plusWeylGradient g e.base e.frame i)
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul]
            exact mul_le_mul (hdbound n i e)
              (abs_regularizedRadialDerivative_le (ε n) (hε n) _ _ ((d.gradientConstraints e).1 i))
              (abs_nonneg _) ((abs_nonneg _).trans (hdbound n i e))
    · filter_upwards [d.gradient_zero_ae_on_zero] with e he
      apply Tendsto.add
      · exact (hklim e).mul ((tendsto_scalarNormExpression _ _
          (fun hv => funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))).comp hlim)
      · apply tendsto_finsetSum
        intro i _
        apply (hdlim i e).mul
        simpa only [regularizedRadialField, ContinuousMap.coe_mk, regularizedRadialDerivative,
          regularizedBlockNorm_zero, Function.comp_def] using
          (tendsto_regularizedRadialDerivative (plusWeyl g e.base e.frame)
            (plusWeylGradient g e.base e.frame i)).comp hlim
  have hz (n) : (∫ e, F n e ∂μ) = 0 := by
    have h := d.testedRegularizedNormEquation (ε n) (hε n) (k n) (dk n) (hk n)
    simpa only [F, scalarNormField, scalarNormExpression, regularizedNormField, regularizedRadialField,
      ContinuousMap.coe_mk, regularized_norm_laplacian_split] using h
  simp only [hz] at hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Weyl norm equation tested against the specific polynomial
κ(v,b). Its smooth approximation is constructed from the two tensor norms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.kappaNormEquation (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedKappa 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
      ∑ i, regularizedKappaDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) ∂μ) = 0 := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let k : ℕ → C(FrameBundle g, ℝ) := fun n =>
    ⟨fun e => regularizedKappa (ε n) (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame),
      continuous_regularizedKappa (ε n) _ _ d.continuousWeyl o.continuousWeyl⟩
  let dk : ℕ → Fin 4 → C(FrameBundle g, ℝ) := fun n i =>
    ⟨fun e => regularizedKappaDerivative (ε n) (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i),
      continuous_regularizedKappaDerivative (ε n) (hε n) _ _ _ _ d.continuousWeyl
        o.continuousWeyl (d.continuousGradient i) (o.continuousGradient i)⟩
  obtain ⟨C, hC0, hC⟩ := kappa_rectangle_bound
  let B : Fin 4 → C(FrameBundle g, ℝ) := fun i =>
    ⟨fun e => C * (normalizedBlockNorm (plusWeylGradient g e.base e.frame i) +
      normalizedBlockNorm (minusWeylGradient g e.base e.frame i)),
      continuous_const.mul ((continuous_normalizedBlockNorm.comp (d.continuousGradient i)).add
        (continuous_normalizedBlockNorm.comp (o.continuousGradient i)))⟩
  apply d.testedNormEquation_of_limits hkato ε hε tendsto_one_div_add_atTop_nhds_zero_nat k dk
    (C := C) (B := B)
  · intro n i t e
    exact hasDerivAt_regularizedKappa (d.derivativeWeyl i t e) (o.derivativeWeyl i t e)
      (fun s => d.weyl.symmetric ((d.flow i).map s e))
      (fun s => o.symmetric ((d.flow i).map s e)) (hε n)
  · intro e
    exact (tendsto_regularizedKappa _ _).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · intro i e
    exact (tendsto_regularizedKappaDerivative _ _ _ _).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · exact hC0
  · intro n e
    exact (regularizedKappa_bounds C hC (hε n) (hε1 n) _ _ _ _
      ((d.gradientConstraints e).1 0) ((o.gradientConstraints e).1 0) (hpinch e)).1
  · intro n i e
    exact (regularizedKappa_bounds C hC (hε n) (hε1 n) _ _ _ _
      ((d.gradientConstraints e).1 i) ((o.gradientConstraints e).1 i) (hpinch e)).2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The invariant Bianchi refined Kato inequality for the metric. The weak
norm equations and singular quotient integrability follow from parallel-frame
covariant calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem refinedKato (d : MetricGreenData g μ) (e : FrameBundle g) :
    (5 / 3 : ℝ) * ‖blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame) :=
  QuaternionFrame.blockRadialGradient_refined_kato _ _ (d.weyl.symmetric e)
    (d.weyl.traceFree e) (d.gradientConstraints e).1 (d.gradientConstraints e).2
    (d.gradientBianchi e)

theorem energyQuotient_integrable (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] :
    Integrable (fun e => weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame)) μ :=
  d.integrableEnergyQuotient d.refinedKato

theorem kappaTest (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedKappa 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
      ∑ i, regularizedKappaDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) ∂μ) = 0 :=
  d.kappaNormEquation o d.refinedKato hpinch

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive trace-free Hessian energy behind the integral addition
in equation (16). The entire prescribed trace component is subtracted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem prescribed_trace_norm_subtraction (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (X : Hessian) (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) :
    hessianNormSq (X - traceComponent M) = hessianNormSq X - (5 / 12) * matrixNormSq M := by
  rw [hessianNormSq_sub, hessianPairing_comm,
    traceComponent_pairing_hessian M hs ht X hmatrix hbianchi,
    htrace, traceComponent_norm M hs ht]
  have hM : matrixPairing M M = matrixNormSq M := by
    simp only [matrixPairing, matrixNormSq, pow_two]
  rw [hM]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem traceEnergy_remainder (d : MetricGreenData g μ) (e : FrameBundle g) :
    hessianNormSq (plusWeylHessian g e.base e.frame) / 3 -
      traceEnergy (plusWeyl g e.base e.frame) =
    hessianNormSq (plusWeylHessian g e.base e.frame -
      traceComponent (weylLaplacian (plusWeyl g e.base e.frame))) / 3 := by
  rw [prescribed_trace_norm_subtraction _
    (weylLaplacian_symmetric _ (d.weyl.symmetric e))
    (weylLaplacian_traceFree _ (d.weyl.traceFree e)) _
    (d.weyl.hessianMatrix e) (d.weyl.hessianBianchi e) (metric_weyl_trace g d.weyl e)]
  unfold traceEnergy
  ring

theorem traceEnergy_le_hessian (d : MetricGreenData g μ) (e : FrameBundle g) :
    traceEnergy (plusWeyl g e.base e.frame) ≤
      hessianNormSq (plusWeylHessian g e.base e.frame) / 3 := by
  have h : 0 ≤ hessianNormSq (plusWeylHessian g e.base e.frame -
      traceComponent (weylLaplacian (plusWeyl g e.base e.frame))) := by
    unfold hessianNormSq
    positivity
  have he := d.traceEnergy_remainder e
  linarith

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The raw orthogonal-frame invariance used from Brin--Karcher, §1:
the uniform frame measure is invariant under a fixed reflection, and
parallel transport intertwines reflection with reversal of the first
flow direction. This gives integral and tensor identities for reflected frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem regularizedRadialDerivative_smul (ε : ℝ) (A Z : Mat) (c : ℝ) :
    regularizedRadialDerivative ε A (c • Z) = c * regularizedRadialDerivative ε A Z := by
  simp only [regularizedRadialDerivative, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem reflectedGradient_radial_sum (ε : ℝ) (A : Mat) (Z : Angular.Gradient) :
    (∑ i, regularizedRadialDerivative ε A (reflectedGradient Z i) ^ 2) =
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedGradient, regularizedRadialDerivative_smul, mul_pow, orientationSign_sq, one_mul]

theorem scalarNormExpression_reflected (ε : ℝ) (A : Mat) (Z : Angular.Gradient) :
    scalarNormExpression ε A (reflectedGradient Z) = scalarNormExpression ε A Z := by
  unfold scalarNormExpression
  rw [reflectedGradient_energy, reflectedGradient_radial_sum]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)

include r in
theorem integral_reflection (F : FrameBundle g → ℝ) :
    (∫ e, F (frameReflection e) ∂μ) = ∫ e, F e ∂μ := by
  have h : MeasurePreserving (frameReflectionEquiv g) μ μ := r.preserves
  exact h.integral_comp' F

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the scalar weak equation and of its radial terms.
The estimates use the actual metric Kato bound, including the zero set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

theorem scalarNorm_integrable (d : MetricGreenData g μ) :
    Integrable (fun e => scalarNormExpression 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let H : FrameBundle g → ℝ := fun e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame) + d.laplacianNormField e
  have hH : Integrable H μ := d.energyQuotient_integrable.add
    (d.laplacianNormField.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hF (n) : Integrable (fun e => d.scalarNormField (ε n) (hε n) e) μ :=
    (d.scalarNormField (ε n) (hε n)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ
    (fun n e => d.scalarNormField (ε n) (hε n) e) _ (∫ e, H e ∂μ) hF
  · filter_upwards [d.gradient_zero_ae_on_zero] with e he
    exact (tendsto_scalarNormExpression _ _ (fun hv =>
      funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    apply integral_mono_ae (hF n).norm hH
    filter_upwards [d.gradient_zero_ae_on_zero] with e he
    rw [Real.norm_eq_abs]
    apply abs_scalarNormExpression_le (ε n) (hε n) _ _ (d.weyl.symmetric e)
    · intro hv
      exact funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv))
    · have hk := d.refinedKato e
      nlinarith [sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)‖]

theorem radial_integrable (d : MetricGreenData g μ) (i : Fin 4) :
    Integrable (fun e => regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let H : C(FrameBundle g, ℝ) := ⟨fun e => normalizedBlockNorm
    (plusWeylGradient g e.base e.frame i),
    continuous_normalizedBlockNorm.comp (d.continuousGradient i)⟩
  have hF (n) : Integrable (fun e => d.regularizedRadialField (ε n) (hε n) i e) μ :=
    (d.regularizedRadialField (ε n) (hε n) i).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ
    (fun n e => d.regularizedRadialField (ε n) (hε n) i e) _ (∫ e, H e ∂μ) hF
  · filter_upwards [] with e
    simpa only [ε, regularizedRadialField, ContinuousMap.coe_mk, Function.comp_def,
      regularizedRadialDerivative, regularizedBlockNorm_zero] using
      (tendsto_regularizedRadialDerivative (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i)).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    apply integral_mono_ae (hF n).norm
      (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    filter_upwards [] with e
    rw [Real.norm_eq_abs]
    exact abs_regularizedRadialDerivative_le (ε n) (hε n) _ _ ((d.gradientConstraints e).1 i)

end MetricGreenData

omit [IsFiniteMeasure μ] in
theorem integrable_continuous_weight {f : FrameBundle g → ℝ} (hf : Integrable f μ)
    (k : C(FrameBundle g, ℝ)) : Integrable (fun e => k e * f e) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn k.continuous.continuousOn
  exact hf.bdd_mul k.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hC e (Set.mem_univ e)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Symmetrize an oriented frame measure only for the reflection-invariant
Green integral. Scalar variance and Weyl gaps still use the original
oriented measure. Reflection invariance of that original measure is not
assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem reflection_preserves_symmetricFrameMeasure :
    MeasurePreserving (frameReflection : FrameBundle g → FrameBundle g)
      (symmetricFrameMeasure g μ) (symmetricFrameMeasure g μ) := by
  have hF : Measurable (frameReflection : FrameBundle g → FrameBundle g) :=
    (frameReflectionEquiv g).measurable
  have hinv : (μ.map frameReflection).map frameReflection = μ := by
    rw [Measure.map_map hF hF]
    have hf : (frameReflection : FrameBundle g → FrameBundle g) ∘ frameReflection = id :=
      funext (frameReflection_involutive g)
    rw [hf, Measure.map_id]
  refine ⟨hF, ?_⟩
  rw [symmetricFrameMeasure, Measure.map_add _ _ hF, hinv, add_comm]

theorem OppositeWeylData.onSymmetricMeasure {d : MetricGreenData g μ}
    (o : OppositeWeylData d) (hparallel : ParallelReflection d) :
    OppositeWeylData (d.onSymmetricMeasure hparallel) where
  symmetric := o.symmetric
  traceFree := o.traceFree
  continuousWeyl := o.continuousWeyl
  continuousGradient := o.continuousGradient
  derivativeWeyl := o.derivativeWeyl
  gradientBianchi := o.gradientBianchi

theorem MetricGreenData.symmetricReflection (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) : FrameReflectionData (d.onSymmetricMeasure hparallel) where
  preserves := reflection_preserves_symmetricFrameMeasure
  parallel := hparallel

/-- Transfer a symmetric integral back to the oriented frame measure. -/
theorem integral_symmetricFrameMeasure (f : FrameBundle g → ℝ)
    (hi : Integrable f (symmetricFrameMeasure g μ))
    (hs : ∀ e, f (frameReflection e) = f e) :
    (∫ e, f e ∂symmetricFrameMeasure g μ) = 2 * ∫ e, f e ∂μ := by
  have hi' : Integrable f μ ∧ Integrable f (μ.map frameReflection) :=
    integrable_add_measure.mp hi
  rw [symmetricFrameMeasure, integral_add_measure hi'.1 hi'.2]
  have hm : (∫ e, f e ∂μ.map frameReflection) = ∫ e, f (frameReflection e) ∂μ := by
    exact (frameReflectionEquiv g).measurableEmbedding.integral_map _
  rw [hm]
  simp_rw [hs]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Test both actual scalar Weyl equations against the total derivative
energy. This is the norm-equation half of the cancellation in (16). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalarNormExpression_frameReflection (ε : ℝ) (e : FrameBundle g) :
    scalarNormExpression ε (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (plusWeylGradient g (frameReflection e).base (frameReflection e).frame) =
    scalarNormExpression ε (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame) := by
  have hZ : plusWeylGradient g (frameReflection e).base (frameReflection e).frame =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change scalarNormExpression ε (plusWeyl g e.base e.frame.reflect) _ = _
  rw [plusWeyl_reflect, hZ, scalarNormExpression_reflected]

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem opposite_scalarNorm_integrable :
    Integrable (fun e => scalarNormExpression 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame)) μ := by
  have h := r.preserves.integrable_comp_of_integrable d.scalarNorm_integrable
  exact h.congr (Filter.Eventually.of_forall (scalarNormExpression_frameReflection 0))

theorem opposite_radial_integrable (i : Fin 4) :
    Integrable (fun e => regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame i)) μ := by
  have h := (r.preserves.integrable_comp_of_integrable (d.radial_integrable i)).const_mul
    (orientationSign i)
  apply h.congr
  filter_upwards [] with e
  change orientationSign i * regularizedRadialDerivative 0
    (plusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect i) = _
  rw [plusWeyl_reflect, plusWeylGradient_reflect, regularizedRadialDerivative_smul,
    ← mul_assoc, ← pow_two, orientationSign_sq, one_mul]

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite and summed deficit tests, obtained from the same
proved plus-block energy identity by reflection of the actual frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem minusWeylGradient_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i : Fin 4) :
    minusWeylGradient g c e.reflect i = orientationSign i • plusWeylGradient g c e i := by
  have h := plusWeylGradient_reflect g c e.reflect i
  rw [e.reflect_reflect] at h
  have h' := congrArg (fun A : Mat => orientationSign i • A) h
  rw [smul_smul, ← pow_two, orientationSign_sq, one_smul] at h'
  exact h'.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exchanged polynomial test in (18), obtained from the proved
plus-block test by the actual frame reflection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem regularizedKappaDerivative_smul (ε : ℝ) (A B Z V : Mat) (c : ℝ) :
    regularizedKappaDerivative ε A B (c • Z) (c • V) =
      c * regularizedKappaDerivative ε A B Z V := by
  unfold regularizedKappaDerivative
  rw [regularizedRadialDerivative_smul, regularizedRadialDerivative_smul]
  ring

theorem kappaNormIntegrand_reflected (A B : Mat) (Z V : Angular.Gradient) :
    kappaNormIntegrand A B (reflectedGradient Z) (reflectedGradient V) =
      kappaNormIntegrand A B Z V := by
  unfold kappaNormIntegrand
  rw [scalarNormExpression_reflected]
  apply congrArg (fun z : ℝ => regularizedKappa 0 A B * scalarNormExpression 0 A Z + z)
  apply Finset.sum_congr rfl
  intro i _
  simp only [reflectedGradient, regularizedKappaDerivative_smul, regularizedRadialDerivative_smul]
  calc
    _ = orientationSign i ^ 2 * (regularizedKappaDerivative 0 A B (Z i) (V i) *
        regularizedRadialDerivative 0 A (Z i)) := by ring
    _ = _ := by rw [orientationSign_sq, one_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem kappaNormIntegrand_frameReflection (e : FrameBundle g) :
    kappaNormIntegrand (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (minusWeyl g (frameReflection e).base (frameReflection e).frame)
      (plusWeylGradient g (frameReflection e).base (frameReflection e).frame)
      (minusWeylGradient g (frameReflection e).base (frameReflection e).frame) =
    kappaNormIntegrand (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame) := by
  have hp : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  have hm : minusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (plusWeylGradient g e.base e.frame) := by
    funext i
    exact minusWeylGradient_reflect g e.base e.frame i
  change kappaNormIntegrand (plusWeyl g e.base e.frame.reflect)
    (minusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect)
      (minusWeylGradient g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect, minusWeyl_reflect, hp, hm, kappaNormIntegrand_reflected]

theorem FrameReflectionData.opposite_kappaTest {d : MetricGreenData g μ}
    (r : FrameReflectionData d) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, kappaNormIntegrand (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame) ∂μ) = 0 := by
  let F : FrameBundle g → ℝ := fun e => kappaNormIntegrand (plusWeyl g e.base e.frame)
    (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame)
  have hF : (∫ e, F e ∂μ) = 0 := d.kappaTest o hpinch
  rw [← r.integral_reflection F] at hF
  refine Eq.trans (b := ∫ e, F (frameReflection e) ∂μ) ?_ hF
  apply integral_congr_ae
  filter_upwards [] with e
  exact (kappaNormIntegrand_frameReflection e).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact cancellation of the two weak norm equations with the
deficit-weighted energy equation. All fields are the actual Weyl fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem jointScalarNorm_integrable : Integrable d.jointScalarNorm μ :=
  d.scalarNorm_integrable.add r.opposite_scalarNorm_integrable

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equation (16), before its positive constant factor: the integrated
trace-subtracted energy is nonnegative. The proof combines the actual
weak equations and the full prescribed trace subtraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

theorem jointTraceEnergy_le_hessian (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.jointTraceEnergy e ≤ d.jointHessianEnergy e := by
  have hp := d.traceEnergy_le_hessian e
  have hm := d.traceEnergy_le_hessian (frameReflection e)
  change traceEnergy (plusWeyl g e.base e.frame) +
    traceEnergy (plusWeyl g (frameReflection e).base (frameReflection e).frame) ≤
    ((hessianNormSq (plusWeylHessian g e.base e.frame) / 3 +
        26 * weylGradientEnergy (plusWeylGradient g e.base e.frame) -
        40 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) +
      (hessianNormSq (plusWeylHessian g (frameReflection e).base (frameReflection e).frame) / 3 +
        26 * weylGradientEnergy (plusWeylGradient g (frameReflection e).base (frameReflection e).frame) -
        40 * weylMatrixEnergy (plusWeyl g (frameReflection e).base (frameReflection e).frame)
          (plusWeylGradient g (frameReflection e).base (frameReflection e).frame))) -
      26 * (weylGradientEnergy (plusWeylGradient g e.base e.frame) +
        weylGradientEnergy (plusWeylGradient g (frameReflection e).base (frameReflection e).frame)) +
      40 * (weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
        weylMatrixEnergy (plusWeyl g (frameReflection e).base (frameReflection e).frame)
          (plusWeylGradient g (frameReflection e).base (frameReflection e).frame))
  linarith only [hp, hm]

end MetricGreenData

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem traceDeficit_integral_nonneg (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    0 ≤ ∫ e, d.traceDeficitIntegrand o e ∂μ := by
  let F : C(FrameBundle g, ℝ) := d.deficitField o * (d.jointHessianEnergy - d.jointTraceEnergy)
  let K : FrameBundle g → ℝ := fun e => d.deficitField o e * d.jointEnergyLaplacian e +
    d.totalEnergyField e * d.jointScalarNorm e
  have hF : Integrable F μ := F.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hK : Integrable K μ :=
    (((d.deficitField o).continuous.mul d.jointEnergyLaplacian.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).add
        (integrable_continuous_weight r.jointScalarNorm_integrable d.totalEnergyField)
  have hz : (∫ e, K e ∂μ) = 0 := r.jointEnergyCancellation o hpinch
  have he (e : FrameBundle g) : d.traceDeficitIntegrand o e = F e - K e := by
    change -(d.totalEnergyField e * d.jointScalarNorm e) -
      26 * d.deficitField o e * d.totalEnergyField e +
      40 * d.deficitField o e * d.jointMatrixEnergy e - d.deficitField o e * d.jointTraceEnergy e =
      d.deficitField o e * ((d.jointEnergyLaplacian e - 26 * d.totalEnergyField e +
        40 * d.jointMatrixEnergy e) - d.jointTraceEnergy e) -
        (d.deficitField o e * d.jointEnergyLaplacian e + d.totalEnergyField e * d.jointScalarNorm e)
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_sub hF hK, hz, sub_zero]
  apply integral_nonneg
  intro e
  change 0 ≤ d.deficitField o e * (d.jointHessianEnergy e - d.jointTraceEnergy e)
  apply mul_nonneg
  · change 0 ≤ 2 - regularizedBlockNorm 0 (plusWeyl g e.base e.frame) -
      regularizedBlockNorm 0 (minusWeyl g e.base e.frame)
    rw [regularizedBlockNorm_zero, regularizedBlockNorm_zero]
    linarith [hpinch e]
  · exact sub_nonneg.mpr (d.jointTraceEnergy_le_hessian e)

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the products in the two polynomial norm tests.
The norm derivatives are obtained by their actual regularized limits. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

theorem continuous_kappaV_fields {Ω : Type*} [TopologicalSpace Ω]
    (v b : Ω → ℝ) (hv : Continuous v) (hb : Continuous b) :
    Continuous (fun x => Quadratic.kappaV (v x) (b x)) := by
  unfold Quadratic.kappaV
  fun_prop

theorem continuous_kappaB_fields {Ω : Type*} [TopologicalSpace Ω]
    (v b : Ω → ℝ) (hv : Continuous v) (hb : Continuous b) :
    Continuous (fun x => Quadratic.kappaB (v x) (b x)) := by
  unfold Quadratic.kappaB
  fun_prop

theorem abs_radialDerivative_zero_le (A Z : Mat) (hZ : symmetric Z) :
    |regularizedRadialDerivative 0 A Z| ≤ normalizedBlockNorm Z := by
  have ht : Tendsto (fun n : ℕ => regularizedRadialDerivative
      (1 / ((n : ℝ) + 1)) A Z) atTop (𝓝 (regularizedRadialDerivative 0 A Z)) := by
    simpa only [Function.comp_def, regularizedRadialDerivative,
      regularizedBlockNorm_zero] using
      (tendsto_regularizedRadialDerivative A Z).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto ht.abs (Eventually.of_forall (fun n =>
    abs_regularizedRadialDerivative_le _ (by positivity) A Z hZ))

section Integral

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

local instance jointIntegrabilityRing_rdf0d04_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance jointIntegrabilitySpace_rdf0d04_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance jointIntegrabilityAlgebra_rdf0d04_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem integrable_radialDerivative_product
    (A B Z V : Ω → Mat) (hZ : Continuous Z) (hV : Continuous V)
    (hsZ : ∀ x, symmetric (Z x)) (hsV : ∀ x, symmetric (V x))
    (hp : AEStronglyMeasurable (fun x => regularizedRadialDerivative 0 (A x) (Z x)) μ)
    (hq : AEStronglyMeasurable (fun x => regularizedRadialDerivative 0 (B x) (V x)) μ) :
    Integrable (fun x => regularizedRadialDerivative 0 (A x) (Z x) *
      regularizedRadialDerivative 0 (B x) (V x)) μ := by
  have hc := (continuous_normalizedBlockNorm.comp hZ).mul
    (continuous_normalizedBlockNorm.comp hV)
  apply (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mono'
    (hp.mul hq)
  filter_upwards [] with x
  change ‖regularizedRadialDerivative 0 (A x) (Z x) *
    regularizedRadialDerivative 0 (B x) (V x)‖ ≤ normalizedBlockNorm (Z x) * normalizedBlockNorm (V x)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_radialDerivative_zero_le _ _ (hsZ x))
    (abs_radialDerivative_zero_le _ _ (hsV x)) (abs_nonneg _)
    (normalizedBlockNorm_nonneg _)

end Integral

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem kappaTest_integrable (o : OppositeWeylData d) :
    Integrable (fun e => kappaNormIntegrand (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)
      (minusWeylGradient g e.base e.frame)) μ := by
  let k : C(FrameBundle g, ℝ) := ⟨fun e => regularizedKappa 0
    (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame),
    continuous_regularizedKappa 0 _ _ d.continuousWeyl o.continuousWeyl⟩
  let kv : C(FrameBundle g, ℝ) := ⟨fun e => Quadratic.kappaV
    (normalizedBlockNorm (plusWeyl g e.base e.frame))
    (normalizedBlockNorm (minusWeyl g e.base e.frame)),
    continuous_kappaV_fields _ _ d.plusNormField.continuous (d.minusNormField o).continuous⟩
  let kb : C(FrameBundle g, ℝ) := ⟨fun e => Quadratic.kappaB
    (normalizedBlockNorm (plusWeyl g e.base e.frame))
    (normalizedBlockNorm (minusWeyl g e.base e.frame)),
    continuous_kappaB_fields _ _ d.plusNormField.continuous (d.minusNormField o).continuous⟩
  have hpp (i : Fin 4) : Integrable (fun e =>
      regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i) *
      regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)) μ :=
    integrable_radialDerivative_product _ _ _ _ (d.continuousGradient i) (d.continuousGradient i)
      (fun e => (d.gradientConstraints e).1 i) (fun e => (d.gradientConstraints e).1 i)
      (d.radial_integrable i).aestronglyMeasurable (d.radial_integrable i).aestronglyMeasurable
  have hqp (i : Fin 4) : Integrable (fun e =>
      regularizedRadialDerivative 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame i) *
      regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)) μ :=
    integrable_radialDerivative_product _ _ _ _ (o.continuousGradient i) (d.continuousGradient i)
      (fun e => (o.gradientConstraints e).1 i) (fun e => (d.gradientConstraints e).1 i)
      (r.opposite_radial_integrable i).aestronglyMeasurable (d.radial_integrable i).aestronglyMeasurable
  have hs := integrable_finsetSum Finset.univ (fun i _ =>
    (integrable_continuous_weight (hpp i) kv).add (integrable_continuous_weight (hqp i) kb))
  have h := (integrable_continuous_weight d.scalarNorm_integrable k).add hs
  apply h.congr
  filter_upwards [] with e
  dsimp only [k, kv, kb, ContinuousMap.coe_mk]
  unfold kappaNormIntegrand regularizedKappaDerivative
  rw [regularizedBlockNorm_zero, regularizedBlockNorm_zero]
  simp only [Pi.add_apply, add_mul, mul_assoc, Finset.sum_add_distrib]

theorem opposite_kappaTest_integrable (o : OppositeWeylData d) :
    Integrable (fun e => kappaNormIntegrand (minusWeyl g e.base e.frame)
      (plusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)
      (plusWeylGradient g e.base e.frame)) μ := by
  exact (r.preserves.integrable_comp_of_integrable (r.kappaTest_integrable o)).congr
    (Eventually.of_forall kappaNormIntegrand_frameReflection)

theorem traceDeficit_integrable (o : OppositeWeylData d) :
    Integrable (d.traceDeficitIntegrand o) μ := by
  have h1 := (integrable_continuous_weight r.jointScalarNorm_integrable d.totalEnergyField).neg
  have h2 := (((d.deficitField o).continuous.mul d.totalEnergyField.continuous).const_mul 26).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have h3 := (((d.deficitField o).continuous.mul d.jointMatrixEnergy.continuous).const_mul 40).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have h4 := ((d.deficitField o).continuous.mul d.jointTraceEnergy.continuous).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  apply (((h1.sub h2).add h3).sub h4).congr
  filter_upwards [] with e
  dsimp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply,
    MetricGreenData.traceDeficitIntegrand]
  ring

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Express the reflected continuous fields as the actual opposite-block
contractions, so the trace-energy inequality can be used in scalar form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem matrixSlotAction_smul_right (A Z : Mat) (c : ℝ) :
    matrixSlotAction A (c • Z) = c • matrixSlotAction A Z := by
  simpa using QuaternionFrame.matrixSlotAction_sum_smul (ι := Unit) A (fun _ => c) (fun _ => Z)

theorem matrixPairing_same_smul (A B : Mat) (c : ℝ) :
    matrixPairing (c • A) (c • B) = c ^ 2 * matrixPairing A B := by
  simp only [matrixPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weylMatrixEnergy_reflected (A : Mat) (Z : Angular.Gradient) :
    weylMatrixEnergy A (reflectedGradient Z) = weylMatrixEnergy A Z := by
  unfold weylMatrixEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedGradient, matrixSlotAction_smul_right, matrixPairing_same_smul,
    orientationSign_sq, one_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

theorem jointMatrixEnergy_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.jointMatrixEnergy e =
      weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
      weylMatrixEnergy (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame) := by
  have hz : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change _ + weylMatrixEnergy (plusWeyl g e.base e.frame.reflect)
    (plusWeylGradient g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect, hz, weylMatrixEnergy_reflected]
  rfl

theorem jointTraceEnergy_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.jointTraceEnergy e = traceEnergy (plusWeyl g e.base e.frame) +
      traceEnergy (minusWeyl g e.base e.frame) := by
  change _ + traceEnergy (plusWeyl g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sum of the two Hessian inequalities, the trace-deficit inequality,
and both polynomial norm tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem jointHessianGreen (o : OppositeWeylData d)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    0 ≤ ∫ e, regularizedHessianIntegrand g 0 e +
      regularizedHessianIntegrand g 0 (frameReflection e) ∂μ := by
  have hi := d.hessianIntegrand_integrable o hpinch
  have hsplit := integral_add hi (r.preserves.integrable_comp_of_integrable hi)
  simp only [Function.comp_def] at hsplit
  rw [hsplit, r.integral_reflection]
  have h := d.unregularizedHessianGreen o hp hdecomp hpinch
  linarith only [h]

theorem preVarianceIntegrand_integrable (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    Integrable (d.preVarianceIntegrand o) μ := by
  have hi := d.hessianIntegrand_integrable o hpinch
  exact ((((hi.add (r.preserves.integrable_comp_of_integrable hi)).add
    ((r.traceDeficit_integrable o).const_mul (17 / 10))).add
      (r.kappaTest_integrable o)).add (r.opposite_kappaTest_integrable o))

theorem preVarianceGreen (o : OppositeWeylData d)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    0 ≤ ∫ e, d.preVarianceIntegrand o e ∂μ := by
  have hi := d.hessianIntegrand_integrable o hpinch
  have hj := hi.add (r.preserves.integrable_comp_of_integrable hi)
  have ht := (r.traceDeficit_integrable o).const_mul (17 / 10)
  have hk := r.kappaTest_integrable o
  have hb := r.opposite_kappaTest_integrable o
  have hs1 := integral_add ((hj.add ht).add hk) hb
  have hs2 := integral_add (hj.add ht) hk
  have hs3 := integral_add hj ht
  simp only [Pi.add_apply, Function.comp_def] at hs1 hs2 hs3
  have hk0 : (∫ e, kappaNormIntegrand (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)
      (minusWeylGradient g e.base e.frame) ∂μ) = 0 := d.kappaTest o hpinch
  unfold MetricGreenData.preVarianceIntegrand
  rw [hs1, hs2, hs3, integral_const_mul, hk0,
    r.opposite_kappaTest o hpinch, add_zero, add_zero]
  exact add_nonneg (r.jointHessianGreen o hp hdecomp hpinch)
    (mul_nonneg (by norm_num) (r.traceDeficit_integral_nonneg o hpinch))

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full finite-array integrand is the actual metric integral from
both Green identities, trace subtraction, variance, and polynomial tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

theorem totalEnergyField_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.totalEnergyField e = weylGradientEnergy (plusWeylGradient g e.base e.frame) +
      weylGradientEnergy (minusWeylGradient g e.base e.frame) := by
  have hz : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change _ + weylGradientEnergy (plusWeylGradient g e.base e.frame.reflect) = _
  rw [hz, reflectedGradient_energy]
  rfl

theorem traceDeficitIntegrand_eq_arrays (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (e : FrameBundle g) :
    d.traceDeficitIntegrand o e = traceCouplingTerm
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame) := by
  unfold traceDeficitIntegrand
  rw [d.totalEnergyField_apply, d.jointMatrixEnergy_apply, d.jointTraceEnergy_apply]
  unfold deficitField regularizedDeficit jointScalarNorm
  simp only [ContinuousMap.coe_mk, regularizedBlockNorm_zero]
  unfold traceCouplingTerm
  ring

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer the reflection-symmetric Green integral to the original
oriented frame measure. The variance correction is then performed on that
original measure, where its scalar means and Weyl gaps have the intended
geometric interpretation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

theorem traceCouplingTerm_reflected_swap (A U : Mat) (Z V : Angular.Gradient) :
    traceCouplingTerm U A (reflectedGradient V) (reflectedGradient Z) =
      traceCouplingTerm A U Z V := by
  unfold traceCouplingTerm
  rw [reflectedGradient_energy, reflectedGradient_energy,
    weylMatrixEnergy_reflected, weylMatrixEnergy_reflected,
    scalarNormExpression_reflected, scalarNormExpression_reflected]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.traceDeficitIntegrand_reflection (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (e : FrameBundle g) :
    d.traceDeficitIntegrand o (frameReflection e) = d.traceDeficitIntegrand o e := by
  rw [d.traceDeficitIntegrand_eq_arrays o, d.traceDeficitIntegrand_eq_arrays o]
  have hp : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  have hm : minusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (plusWeylGradient g e.base e.frame) := by
    funext i
    exact minusWeylGradient_reflect g e.base e.frame i
  dsimp only [frameReflection]
  rw [plusWeyl_reflect, minusWeyl_reflect, hp, hm, traceCouplingTerm_reflected_swap]

theorem MetricGreenData.preVarianceIntegrand_reflection (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (e : FrameBundle g) :
    d.preVarianceIntegrand o (frameReflection e) = d.preVarianceIntegrand o e := by
  unfold preVarianceIntegrand
  rw [frameReflection_involutive, d.traceDeficitIntegrand_reflection,
    kappaNormIntegrand_frameReflection]
  have hk := kappaNormIntegrand_frameReflection (frameReflection e)
  rw [← hk, frameReflection_involutive]
  ring

theorem MetricGreenData.preVarianceGreen_oriented_oai (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hparallel : ParallelReflection d) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    Integrable (d.preVarianceIntegrand o) μ ∧ 0 ≤ ∫ e, d.preVarianceIntegrand o e ∂μ := by
  let dS := d.onSymmetricMeasure hparallel
  let oS := o.onSymmetricMeasure hparallel
  let rS := d.symmetricReflection hparallel
  have hi : Integrable (d.preVarianceIntegrand o) (symmetricFrameMeasure g μ) :=
    rS.preVarianceIntegrand_integrable oS hpinch
  have hn : 0 ≤ ∫ e, d.preVarianceIntegrand o e ∂symmetricFrameMeasure g μ :=
    rS.preVarianceGreen oS hp hdecomp hpinch
  have hs := integral_symmetricFrameMeasure (d.preVarianceIntegrand o) hi
    (d.preVarianceIntegrand_reflection o)
  rw [hs] at hn
  refine ⟨(integrable_add_measure.mp hi).1, ?_⟩
  linarith only [hn]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.preVarianceGreen_oriented_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.preVarianceGreen_oriented_oai.{u_1}
