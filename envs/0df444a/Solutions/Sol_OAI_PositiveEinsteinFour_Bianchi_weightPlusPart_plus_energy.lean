-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:36:22.425986+00:00
-- url     : https://prove2.me/submissions/225c5522-5c4b-4dbb-bf1b-bc89fe531058

import Mathlib
import Definitions.Def_OAIQ091C013
import Definitions.Def_OAIQ091C015
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_costCoefficient_norm
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_coordinates

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

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCasimir
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Bianchi coupling operator on first derivatives. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- Quaternion multiplication preserves the full Euclidean inner product. -/
theorem quaternion_inner (s : Fin 3) (p q : Vec) :
    inner ℝ (quaternion s p) (quaternion s q) = inner ℝ p q := by
  have h := quaternion_norm_sq s (p + q)
  rw [quaternion_add, norm_add_sq_real, norm_add_sq_real,
    quaternion_norm_sq, quaternion_norm_sq] at h
  linarith

/-- The infinitesimal quaternion action is skew-adjoint. -/
theorem quaternion_inner_skew (s : Fin 3) (p q : Vec) :
    inner ℝ (quaternion s p) q = -inner ℝ p (quaternion s q) := by
  have h := quaternion_inner s p (quaternion s q)
  rw [quaternion_square, inner_neg_right] at h
  linarith

private theorem rotate_sums (f : Fin 3 → Fin 3 → Fin 3 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ s, ∑ u, f a b s u) = ∑ u, ∑ a, ∑ b, ∑ s, f a b s u := by
  calc
    _ = ∑ a, ∑ b, ∑ u, ∑ s, f a b s u := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ u, ∑ b, ∑ s, f a b s u := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

private theorem matrixRotation_component (s : Fin 3) (Z : Tensor)
    (a b : Fin 3) (u : Fin 4) :
    matrixRotation s Z a b u = matrixAction s (fun a b => Z.matrix a b u) a b := by
  simp [matrixRotation, matrixAction, Finset.sum_sub_distrib,
    Fin.sum_univ_succ]
  ring

/-- The matrix-spin Casimir on the actual four-vector-valued tensor. -/
theorem matrixRotation_energy (Z : Tensor) (hz : Z.traceFree) :
    (∑ a, ∑ b, ∑ s, ‖matrixRotation s Z a b‖ ^ 2) = 24 * Z.squaredNorm := by
  let M (u : Fin 4) : Mat := fun a b => Z.matrix a b u
  have hs (u : Fin 4) : symmetric (M u) := by
    intro a b
    exact congrArg (fun q : Vec => q u) (Z.matrix_symmetric a b)
  have ht (u : Fin 4) : traceFree (M u) := by
    have h := congrArg (fun q : Vec => q u) hz
    simpa [traceFree, M, Tensor.traceFree, Tensor.matrix, Fin.sum_univ_succ] using h
  have hc (u : Fin 4) := matrixAction_casimir (M u) (hs u) (ht u)
  have hr : (∑ u : Fin 4, ∑ a, ∑ b, Z.matrix a b u ^ 2) = Z.squaredNorm := by
    unfold Tensor.squaredNorm
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [rotate_sums]
  simp_rw [matrixRotation_component]
  change (∑ u : Fin 4, ∑ a, ∑ b, ∑ s, matrixAction s (M u) a b ^ 2) = _
  simp_rw [hc]
  simp only [matrixNormSq, M, ← Finset.mul_sum]
  rw [hr]

/-- The Bianchi gradient has the exact inner Casimir energy 35. -/
theorem gradientGenerator_energy (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ a, ∑ b, ∑ s, ‖gradientGenerator s Z a b‖ ^ 2) = 35 * Z.squaredNorm := by
  have hi : (∑ a, ∑ b, ∑ s : Fin 3, ‖quaternion s (Z.matrix a b)‖ ^ 2) =
      3 * Z.squaredNorm := by
    simp [Tensor.squaredNorm, Fin.sum_univ_succ]
    ring
  have he (a b : Fin 3) :
      (∑ s, inner ℝ (quaternion s (Z.matrix a b)) (matrixRotation s Z a b)) =
        4 * ‖Z.matrix a b‖ ^ 2 := by
    simp only [quaternion_inner_skew, Finset.sum_neg_distrib]
    rw [← inner_sum]
    change -inner ℝ (Z.matrix a b) (gradientCoupling Z a b) = _
    rw [gradientCoupling_eq Z hb]
    simp [real_inner_smul_right]
  have hx : (∑ a, ∑ b, ∑ s,
      inner ℝ (quaternion s (Z.matrix a b)) (matrixRotation s Z a b)) =
      4 * Z.squaredNorm := by
    simp_rw [he]
    simp only [← Finset.mul_sum, Tensor.squaredNorm]
  have hr := matrixRotation_energy Z hz
  have hsplit : (∑ a, ∑ b, ∑ s, ‖gradientGenerator s Z a b‖ ^ 2) =
      (∑ a, ∑ b, ∑ s : Fin 3, ‖quaternion s (Z.matrix a b)‖ ^ 2) +
      (∑ a, ∑ b, ∑ s, ‖matrixRotation s Z a b‖ ^ 2) +
      2 * (∑ a, ∑ b, ∑ s,
        inner ℝ (quaternion s (Z.matrix a b)) (matrixRotation s Z a b)) := by
    simp only [gradientGenerator, norm_add_sq_real, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  rw [hsplit, hi, hr, hx]
  ring

end
end PositiveEinsteinFour.Bianchi

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

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestSquare
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted positive square on the actual highest-Hessian arrays. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem tensorCoordinates_add (X Y : Hessian) (p : TensorIndex) :
    tensorCoordinates (X + Y) p = tensorCoordinates X p + tensorCoordinates Y p := rfl

private theorem tensorCoordinates_smul (r : ℝ) (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (r • X) p = r * tensorCoordinates X p := rfl

theorem totalPlus_add (s : Fin 3) (X Y : Hessian) :
    totalPlus s (X + Y) = totalPlus s X + totalPlus s Y := by
  funext i j a b
  change tensorCoordinates (totalPlus s (X + Y)) (i, j, a, b) =
    tensorCoordinates (totalPlus s X) (i, j, a, b) +
      tensorCoordinates (totalPlus s Y) (i, j, a, b)
  simp only [totalPlus_coordinates, tensorCoordinates_add, mul_add,
    Finset.sum_add_distrib]

theorem totalPlus_smul (s : Fin 3) (r : ℝ) (X : Hessian) :
    totalPlus s (r • X) = r • totalPlus s X := by
  funext i j a b
  change tensorCoordinates (totalPlus s (r • X)) (i, j, a, b) =
    r * tensorCoordinates (totalPlus s X) (i, j, a, b)
  simp only [totalPlus_coordinates, tensorCoordinates_smul, mul_left_comm,
    ← Finset.mul_sum]

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoupledOperator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.fieldRaw_rawField _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real coupled operator used for the plus projection. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The total infinitesimal action obeys the product rule on an actual tensor. -/
theorem totalPlus_rawWeight (s : Fin 3) (a : Vec) (Z : RawGradient) :
    totalPlus s (rawWeight a Z) =
      rawWeight (quaternion s a) Z + rawWeight a (rawGradientGenerator s Z) := by
  funext i j b c
  change totalPlus s (rawWeight a Z) i j b c =
    quaternion s a i * Z b c j + a i * rawGradientGenerator s Z b c j
  have ha := quaternionMatrix_apply s a i
  have hZ := quaternionMatrix_apply s (Z b c) j
  simp only [Fin.sum_univ_four] at ha hZ
  simp [totalPlus, rawWeight, rawGradientGenerator, rawMatrixRotation,
    matrixAction, Fin.sum_univ_three, Fin.sum_univ_four]
  rw [← ha, ← hZ]
  ring

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCoordinateModel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed twelve real coordinates for the inner generators in the cost calculation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian
set_option maxHeartbeats 1000000

/-- The fixed coordinates cover every trace-free Bianchi tensor. -/
theorem exists_costParameters (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    ∃ v : Fin 3 → Vec, costParameters v = Z := by
  refine ⟨![radialCoordinate costShape Z, secondCoordinate costShape Z, thirdCoordinate costShape Z], ?_⟩
  exact parameters_reconstruction costShape Z hz hb


theorem costParameters_matrix_add (v w : Fin 3 → Vec) :
    (costParameters (v + w)).matrix =
      (costParameters v).matrix + (costParameters w).matrix := by
  funext a b
  fin_cases a <;> fin_cases b <;>
    simp [costParameters, parameters, Tensor.matrix, costShape, difference,
      next, previous, quaternion_add, smul_add]
  all_goals module

theorem costParameters_matrix_smul (r : ℝ) (v : Fin 3 → Vec) :
    (costParameters (r • v)).matrix = r • (costParameters v).matrix := by
  funext a b
  fin_cases a <;> fin_cases b <;>
    simp [costParameters, parameters, Tensor.matrix, costShape, difference,
      next, previous, quaternion_smul, smul_smul]
  all_goals module

theorem costParameters_matrix_neg (v : Fin 3 → Vec) :
    (costParameters (-v)).matrix = -(costParameters v).matrix := by
  simpa only [neg_one_smul] using costParameters_matrix_smul (-1) v

theorem costParameters_matrix_sub (v w : Fin 3 → Vec) :
    (costParameters (v - w)).matrix =
      (costParameters v).matrix - (costParameters w).matrix := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ w, costParameters_matrix_add,
    costParameters_matrix_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

theorem costParameters_norm (v : Fin 3 → Vec) :
    (costParameters v).squaredNorm = coordinateNorm v := by
  have h := parameters_energy costShape (v 0) (v 1) (v 2)
  unfold costParameters coordinateNorm
  linarith

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RealVectorProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-vector norm calculation behind the plus projection cost. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The real quaternion frame is orthogonal, with common norm `|a|`.
This includes the scalar direction and avoids any complex factorization. -/
theorem quaternion_combination_norm_sq (a : Vec) (r : ℝ) (c : Fin 3 → ℝ) :
    (∑ i : Fin 4, (r * a i + ∑ s : Fin 3, c s * quaternion s a i) ^ 2) =
      (r ^ 2 + ∑ s : Fin 3, c s ^ 2) * ‖a‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, quaternion, Fin.sum_univ_succ]
  ring

private theorem weightPlusPart_outer_norm (a : Vec) (Z : Tensor)
    (b c : Fin 3) (j : Fin 4) :
    (∑ i : Fin 4, weightPlusPart a Z i j b c ^ 2) =
      (‖a‖ ^ 2 / 144) * (49 * Z.matrix b c j ^ 2 +
        ∑ s : Fin 3, gradientGenerator s Z b c j ^ 2) := by
  have h := quaternion_combination_norm_sq a (7 * Z.matrix b c j)
    (fun s => -gradientGenerator s Z b c j)
  have hentry (i : Fin 4) :
      7 * a i * Z.matrix b c j -
          ∑ s : Fin 3, quaternion s a i * gradientGenerator s Z b c j =
        (7 * Z.matrix b c j) * a i +
          ∑ s : Fin 3, (-gradientGenerator s Z b c j) * quaternion s a i := by
    simp only [Fin.sum_univ_three]
    ring
  simp only [weightPlusPart, weightCoupling, hentry, div_pow, ← Finset.sum_div]
  rw [h]
  simp only [neg_sq, mul_pow]
  ring

/-- The coefficient `7/12` is proved directly for real vectors using the
actual Bianchi Casimir, with no representation or partial-trace premise. -/
theorem weightPlusPart_norm (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianNormSq (weightPlusPart a Z) = (7 / 12) * ‖a‖ ^ 2 * Z.squaredNorm := by
  have hZ : (∑ b, ∑ c, ∑ j : Fin 4, Z.matrix b c j ^ 2) = Z.squaredNorm := by
    simp only [Tensor.squaredNorm, EuclideanSpace.real_norm_sq_eq]
  have hG : (∑ b, ∑ c, ∑ j : Fin 4, ∑ s : Fin 3,
      gradientGenerator s Z b c j ^ 2) = 35 * Z.squaredNorm := by
    calc
      _ = ∑ b, ∑ c, ∑ s : Fin 3, ∑ j : Fin 4,
          gradientGenerator s Z b c j ^ 2 := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
      _ = _ := by
        simpa only [EuclideanSpace.real_norm_sq_eq] using gradientGenerator_energy Z hz hb
  calc
    _ = ∑ b, ∑ c, ∑ j : Fin 4, ∑ i : Fin 4, weightPlusPart a Z i j b c ^ 2 := by
      unfold hessianNormSq
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ j : Fin 4,
        (‖a‖ ^ 2 / 144) * (49 * Z.matrix b c j ^ 2 +
          ∑ s : Fin 3, gradientGenerator s Z b c j ^ 2) := by
      simp_rw [weightPlusPart_outer_norm]
    _ = (‖a‖ ^ 2 / 144) *
        (49 * (∑ b, ∑ c, ∑ j : Fin 4, Z.matrix b c j ^ 2) +
          ∑ b, ∑ c, ∑ j : Fin 4, ∑ s : Fin 3, gradientGenerator s Z b c j ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hZ, hG]; ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RealVectorCost
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.fieldRaw_rawField _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second real-vector projection identity in actual tensor coordinates. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian HighestHessian

theorem rawNorm_smul (r : ℝ) (Z : RawGradient) :
    rawNorm (r • Z) = r ^ 2 * rawNorm Z := by
  simp only [rawNorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, ← Finset.mul_sum]

theorem rawCostCoefficient_coordinates (s r : Fin 3) (v : Fin 3 → Vec) :
    rawCostCoefficient s r (costParameters v).matrix =
      (costParameters (costCoefficientCoordinates s r v)).matrix := by
  unfold rawCostCoefficient costCoefficientCoordinates
  split_ifs <;>
    simp only [costParameters_matrix_sub, costParameters_matrix_smul,
      costParameters_matrix_neg, generator_coordinates]

/-- The coefficient identity uses the actual twelve Bianchi coordinates. -/
theorem rawCostCoefficient_norm (s : Fin 3) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    64 * rawNorm (rawGradientGenerator s Z.matrix) +
      (∑ r : Fin 3, rawNorm (rawCostCoefficient s r Z.matrix)) =
        84 * Z.squaredNorm + 108 * rawNorm (rawGradientGenerator s Z.matrix) := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  simp_rw [rawCostCoefficient_coordinates, generator_coordinates, rawNorm_matrix,
    costParameters_norm]
  exact costCoefficient_norm s v

private theorem quaternionCombination_slice_norm (a : Vec) (Z : RawGradient)
    (C : Fin 3 → RawGradient) (b c : Fin 3) (j : Fin 4) :
    (∑ i : Fin 4, quaternionCombination a Z C i j b c ^ 2) =
      ‖a‖ ^ 2 * (Z b c j ^ 2 + ∑ s : Fin 3, C s b c j ^ 2) := by
  have h := quaternion_combination_norm_sq a (Z b c j) (fun s => C s b c j)
  simpa only [quaternionCombination, mul_comm] using h

/-- No product assumption is made on the inner plus and minus factors. -/
theorem quaternionCombination_norm (a : Vec) (Z : RawGradient)
    (C : Fin 3 → RawGradient) :
    hessianNormSq (quaternionCombination a Z C) =
      ‖a‖ ^ 2 * (rawNorm Z + ∑ s : Fin 3, rawNorm (C s)) := by
  calc
    _ = ∑ b, ∑ c, ∑ j : Fin 4, ∑ i : Fin 4,
        quaternionCombination a Z C i j b c ^ 2 := by
      unfold hessianNormSq
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ j : Fin 4,
        ‖a‖ ^ 2 * (Z b c j ^ 2 + ∑ s : Fin 3, C s b c j ^ 2) := by
      simp_rw [quaternionCombination_slice_norm]
    _ = _ := by
      simp only [rawNorm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
        Fin.sum_univ_four]
      ring


theorem weightPlusPart_linearCombination (a : Vec) (Z : Tensor) :
    weightPlusPart a Z = (1 / 12 : ℝ) •
      ((7 : ℝ) • rawWeight a Z.matrix -
        ∑ r : Fin 3, rawWeight (quaternion r a) (rawGradientGenerator r Z.matrix)) := by
  funext i j b c
  simp [weightPlusPart, weightCoupling, rawWeight, Fin.sum_univ_three]
  ring

/-- The total generator is evaluated before taking its norm. -/
theorem totalPlus_weightPlusPart (s : Fin 3) (a : Vec) (Z : Tensor) :
    totalPlus s (weightPlusPart a Z) = (1 / 12 : ℝ) •
      quaternionCombination a ((8 : ℝ) • rawGradientGenerator s Z.matrix)
        (fun r => rawCostCoefficient s r Z.matrix) := by
  rw [weightPlusPart_linearCombination, totalPlus_smul]
  congr 1
  rw [sub_eq_add_neg,
    ← neg_one_smul ℝ (∑ r : Fin 3,
      rawWeight (quaternion r a) (rawGradientGenerator r Z.matrix))]
  simp only [Fin.sum_univ_three, totalPlus_add, totalPlus_smul, totalPlus_rawWeight]
  funext i j b c
  fin_cases s <;> fin_cases i <;>
    simp [rawWeight, quaternionCombination, rawCostCoefficient, quaternion,
      next, previous, Fin.sum_univ_three]
  all_goals ring

private theorem hessianNormSq_smul (r : ℝ) (X : Hessian) :
    hessianNormSq (r • X) = r ^ 2 * hessianNormSq X := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (r * X i j a b) ^ 2) = _
  simp only [mul_pow, hessianNormSq, ← Finset.mul_sum]

/-- The real-vector identity is proved separately for each actual generator. -/
theorem totalPlus_weightPlusPart_norm (s : Fin 3) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianNormSq (totalPlus s (weightPlusPart a Z)) = ‖a‖ ^ 2 *
      ((7 / 12) * Z.squaredNorm +
        (3 / 4) * rawNorm (rawGradientGenerator s Z.matrix)) := by
  rw [totalPlus_weightPlusPart, hessianNormSq_smul, quaternionCombination_norm,
    rawNorm_smul]
  norm_num only [show (8 : ℝ) ^ 2 = 64 by norm_num]
  rw [rawCostCoefficient_norm s Z hz hb]
  ring


/-- The raw inner energy is the Bianchi Casimir. -/
theorem rawGenerator_energy (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawNorm (rawGradientGenerator s Z.matrix)) = 35 * Z.squaredNorm := by
  calc
    _ = ∑ a, ∑ b, ∑ s : Fin 3, ‖gradientGenerator s Z a b‖ ^ 2 := by
      simp only [rawNorm, rawGradientGenerator_matrix]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := gradientGenerator_energy Z hz hb

/-- The explicit real plus part has actual total-plus energy forty-eight. -/
theorem weightPlusPart_plus_energy_oai (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, hessianNormSq (totalPlus s (weightPlusPart a Z))) =
      48 * hessianNormSq (weightPlusPart a Z) := by
  calc
    _ = ‖a‖ ^ 2 * ((7 / 4) * Z.squaredNorm +
        (3 / 4) * ∑ s : Fin 3, rawNorm (rawGradientGenerator s Z.matrix)) := by
      simp only [totalPlus_weightPlusPart_norm _ a Z hz hb, Fin.sum_univ_three]
      ring
    _ = _ := by rw [rawGenerator_energy Z hz hb, weightPlusPart_norm a Z hz hb]; ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy_oai := @OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy_oai
