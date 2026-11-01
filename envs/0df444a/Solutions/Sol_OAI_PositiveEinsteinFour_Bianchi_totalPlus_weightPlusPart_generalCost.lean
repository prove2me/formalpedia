-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:32:38.415387+00:00
-- url     : https://prove2.me/submissions/b405926f-9e10-4133-8fe0-2dfae1549f9c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C013
import Definitions.Def_OAIQ091C015
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_costCoefficient_norm
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_coupling_matrix_coordinates
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_coordinates
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_totalGradientTensor_bianchi
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_totalGradientTensor_matrix

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCasimir
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceAdjoint
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

theorem hessianPairing_comm (X Y : Hessian) :
    hessianPairing X Y = hessianPairing Y X := by
  simp only [hessianPairing, mul_comm]

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
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
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

/-- The Clifford anticommutator, with the normalization of the fixed frame. -/
theorem quaternion_anticommutator (r s : Fin 3) (q : Vec) :
    quaternion r (quaternion s q) + quaternion s (quaternion r q) =
      if r = s then (-2 : ℝ) • q else 0 := by
  fin_cases r <;> fin_cases s <;> ext u <;> fin_cases u <;>
    simp [quaternion]
  all_goals ring

/-- Matrix rotations commute with the action on the derivative slot. -/
theorem matrixRotation_derivativeQuaternion (r s : Fin 3) (Z : Tensor)
    (a b : Fin 3) :
    matrixRotation s (derivativeQuaternion r Z) a b =
      quaternion r (matrixRotation s Z a b) := by
  simp only [matrixRotation, derivativeQuaternion_matrix, Fin.sum_univ_three]
  simp only [sub_eq_add_neg, quaternion_add, quaternion_neg, quaternion_smul]

/-- The exact anticommutator between the Bianchi coupling and a derivative
quaternion. No irreducible-representation assertion is assumed. -/
theorem gradientCoupling_anticommutator (r : Fin 3) (Z : Tensor)
    (a b : Fin 3) :
    gradientCoupling (derivativeQuaternion r Z) a b +
      quaternion r (gradientCoupling Z a b) = (-2 : ℝ) • matrixRotation r Z a b := by
  simp only [gradientCoupling, matrixRotation_derivativeQuaternion,
    Fin.sum_univ_three, quaternion_add]
  have h0 := quaternion_anticommutator 0 r (matrixRotation 0 Z a b)
  have h1 := quaternion_anticommutator 1 r (matrixRotation 1 Z a b)
  have h2 := quaternion_anticommutator 2 r (matrixRotation 2 Z a b)
  calc
    _ = (quaternion 0 (quaternion r (matrixRotation 0 Z a b)) +
          quaternion r (quaternion 0 (matrixRotation 0 Z a b))) +
        (quaternion 1 (quaternion r (matrixRotation 1 Z a b)) +
          quaternion r (quaternion 1 (matrixRotation 1 Z a b))) +
        (quaternion 2 (quaternion r (matrixRotation 2 Z a b)) +
          quaternion r (quaternion 2 (matrixRotation 2 Z a b))) := by module
    _ = _ := by
      rw [h0, h1, h2]
      fin_cases r <;> norm_num [Fin.ext_iff] <;> rfl


/-- Compressing the derivative quaternion to the Bianchi subspace gives one
fifth of the total inner generator, with the coefficient derived explicitly. -/
theorem gradientProjection_derivativeQuaternion (r : Fin 3) (Z : Tensor)
    (hb : Z.bianchi) (a b : Fin 3) :
    gradientProjection (derivativeQuaternion r Z) a b =
      (1 / 5 : ℝ) • gradientGenerator r Z a b := by
  have h := gradientCoupling_anticommutator r Z a b
  rw [gradientCoupling_eq Z hb, quaternion_smul] at h
  rw [gradientProjection, derivativeQuaternion_matrix, gradientGenerator,
    eq_sub_of_add_eq h]
  module

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear compression on the actual Bianchi gradient space. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

theorem rawPairing_comm (Z W : RawGradient) : rawPairing Z W = rawPairing W Z := by
  simp only [rawPairing, mul_comm]

theorem rawPairing_add_left (Z W U : RawGradient) :
    rawPairing (Z + W) U = rawPairing Z U + rawPairing W U := by
  change (∑ p : GradientIndex,
    (rawCoordinates Z p + rawCoordinates W p) * rawCoordinates U p) = _
  simp only [add_mul, rawPairing, Finset.sum_add_distrib]

theorem rawPairing_add_right (Z W U : RawGradient) :
    rawPairing Z (W + U) = rawPairing Z W + rawPairing Z U := by
  rw [rawPairing_comm Z, rawPairing_add_left, rawPairing_comm W, rawPairing_comm U]

theorem gradientCouplingKernel_symmetric (p q : GradientIndex) :
    gradientCouplingKernel p q = gradientCouplingKernel q p := by
  unfold gradientCouplingKernel
  apply Finset.sum_congr rfl
  intro s _
  rw [quaternionMatrix_skew s p.1 q.1,
    rotation_skew s p.2.1 q.2.1, rotation_skew s p.2.2 q.2.2]
  simp only [eq_comm (a := q.2.1) (b := p.2.1),
    eq_comm (a := q.2.2) (b := p.2.2)]
  split_ifs <;> ring

theorem rawCoupling_selfadjoint (Z W : RawGradient) :
    rawPairing (rawCoupling Z) W = rawPairing Z (rawCoupling W) := by
  simp only [rawPairing, rawCoupling_coordinates, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [gradientCouplingKernel_symmetric q p]
  ring

theorem rawPairing_smul_left (r : ℝ) (Z W : RawGradient) :
    rawPairing (r • Z) W = r * rawPairing Z W := by
  change (∑ p : GradientIndex, (r * rawCoordinates Z p) * rawCoordinates W p) = _
  simp only [mul_assoc, rawPairing, ← Finset.mul_sum]

theorem rawPairing_smul_right (r : ℝ) (Z W : RawGradient) :
    rawPairing Z (r • W) = r * rawPairing Z W := by
  change (∑ p : GradientIndex, rawCoordinates Z p * (r * rawCoordinates W p)) = _
  simp only [mul_left_comm, rawPairing, ← Finset.mul_sum]

theorem rawPairing_sub_left (Z W U : RawGradient) :
    rawPairing (Z - W) U = rawPairing Z U - rawPairing W U := by
  change (∑ p : GradientIndex,
    (rawCoordinates Z p - rawCoordinates W p) * rawCoordinates U p) = _
  simp only [sub_mul, rawPairing, Finset.sum_sub_distrib]

/-- Pairing with a genuine Bianchi tensor removes the displayed polynomial
projection, by self-adjointness of the actual finite-dimensional coupling. -/
theorem gradientProjection_pairing (Z W : Tensor) (hw : W.bianchi) :
    rawPairing (gradientProjection Z) W.matrix = rawPairing Z.matrix W.matrix := by
  have hW : rawCoupling W.matrix = (-4 : ℝ) • W.matrix := by
    funext a b
    exact gradientCoupling_eq W hw a b
  have hC := rawCoupling_selfadjoint Z.matrix W.matrix
  rw [hW, rawPairing_smul_right] at hC
  have hP : gradientProjection Z =
      (1 / 10 : ℝ) • ((6 : ℝ) • Z.matrix - rawCoupling Z.matrix) := rfl
  rw [hP, rawPairing_smul_left, rawPairing_sub_left, rawPairing_smul_left, hC]
  ring

/-- The derivative-slot quaternion has the actual one-fifth compression
against any other Bianchi gradient, retaining both bilinear arguments. -/
theorem derivativeQuaternion_pairing (r : Fin 3) (Z W : Tensor)
    (hz : Z.bianchi) (hw : W.bianchi) :
    rawPairing (derivativeQuaternion r Z).matrix W.matrix =
      (1 / 5 : ℝ) * rawPairing (rawGradientGenerator r Z.matrix) W.matrix := by
  have h := gradientProjection_pairing (derivativeQuaternion r Z) W hw
  have hp : gradientProjection (derivativeQuaternion r Z) =
      (1 / 5 : ℝ) • rawGradientGenerator r Z.matrix := by
    funext a b
    exact gradientProjection_derivativeQuaternion r Z hz a b
  rw [hp, rawPairing_smul_left] at h
  exact h.symm

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeneralMatrixCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bianchi compression for an arbitrary symmetric trace-free Weyl matrix,
with no choice of a moving diagonal frame. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The full coefficient matrix satisfies the same coupling identity as
the diagonal specialization. The proof uses the actual twelve-dimensional
Bianchi coordinates and the five free entries of the symmetric matrix. -/
theorem rawCoupling_generalMatrixAction (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    rawCoupling (generalMatrixAction A Z.matrix) =
      (-(1 / 2 : ℝ)) • generalMixedAction A Z.matrix := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  rw [← coordinates_eq A hA hAt]
  exact coupling_matrix_coordinates _ _ _ _ _ v

/-- Bilinear compression against any Bianchi test tensor. No pointwise
diagonal frame is assumed for either the Weyl coefficient or the test. -/
theorem generalMixedAction_pairing (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z W : Tensor) (hz : Z.traceFree) (hbz : Z.bianchi) (hbw : W.bianchi) :
    rawPairing (generalMixedAction A Z.matrix) W.matrix =
      8 * rawPairing (generalMatrixAction A Z.matrix) W.matrix := by
  have hW : rawCoupling W.matrix = (-4 : ℝ) • W.matrix := by
    funext a b
    exact gradientCoupling_eq W hbw a b
  have h := rawCoupling_selfadjoint (generalMatrixAction A Z.matrix) W.matrix
  rw [rawCoupling_generalMatrixAction A hA hAt Z hz hbz, hW,
    rawPairing_smul_left, rawPairing_smul_right] at h
  linarith

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

end
end PositiveEinsteinFour.Bianchi

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

/-! Curvature contractions with the entire symmetric Weyl matrix.
No moving eigenframe enters these identities. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open Matrix TraceHessian Bianchi PositiveEinsteinFour.Geometry

noncomputable section

theorem generalMixedAction_self_pairing (A : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    rawPairing (generalMixedAction A Z.matrix) Z.matrix = 8 * generalGradientForm A Z :=
  generalMixedAction_pairing A hs ht Z Z hz hb hb

private theorem sum_four_swap {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (α × β) (γ × δ)).sum_comp
    (fun p : (γ × δ) × (α × β) => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

theorem generalMixedAction_pairing_sum (A : Mat) (Z : Tensor) :
    rawPairing (generalMixedAction A Z.matrix) Z.matrix =
      ∑ r, ∑ s, A r s *
        (∑ a, ∑ b, inner ℝ (quaternion r (matrixRotation s Z a b)) (Z.matrix a b)) := by
  simp only [rawPairing_vectors, generalMixedAction, rawMatrixRotation_matrix,
    sum_inner, real_inner_smul_left]
  rw [sum_four_swap]
  simp only [Finset.mul_sum]

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! The original weighted-Hessian curvature form with complete Weyl matrices.
The contractions retain the full symmetric Weyl matrices. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

theorem hessianPairing_smul_right (c : ℝ) (X Y : Hessian) :
    hessianPairing X (c • Y) = c * hessianPairing X Y := by
  rw [hessianPairing_comm X, hessianPairing_smul_left, hessianPairing_comm Y X]

end
end PositiveEinsteinFour.TraceHessian

end


section

/-! Full-matrix generator compression on the actual Bianchi gradient space.
This is the ingredient for retaining unsymmetrized inner-Bianchi Hessians. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open Matrix TraceHessian HighestHessian CurvatureContraction

noncomputable section

private theorem quaternion_frame_inner (r s : Fin 3) (v : Vec) :
    inner ℝ (quaternion r v) (quaternion s v) =
      if r = s then ‖v‖ ^ 2 else 0 := by
  fin_cases r <;> fin_cases s <;>
    simp [quaternion, PiLp.inner_apply, RCLike.inner_apply,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  all_goals ring

private theorem rawQuaternion_self_pairing (r s : Fin 3) (Z : Tensor) :
    rawPairing (rawQuaternion r Z.matrix) (rawQuaternion s Z.matrix) =
      if r = s then Z.squaredNorm else 0 := by
  rw [rawPairing_vectors]
  simp only [rawQuaternion, quaternion_frame_inner]
  by_cases h : r = s
  · simp only [h, ite_true, if_true, Tensor.squaredNorm]
  · simp only [h, ite_false, if_false, Finset.sum_const_zero]

private theorem weighted_rawQuaternion_self (A : Mat) (Z : Tensor) :
    (∑ r, ∑ s, A r s * rawPairing (rawQuaternion r Z.matrix)
      (rawQuaternion s Z.matrix)) = Matrix.trace A * Z.squaredNorm := by
  simp only [rawQuaternion_self_pairing, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Matrix.trace, Matrix.diag,
    Finset.sum_mul]

private theorem quaternion_matrix_pairing (r s : Fin 3) (Z : Tensor) :
    rawPairing (rawQuaternion r Z.matrix) (rawMatrixRotation s Z.matrix) =
      -(∑ a, ∑ b, inner ℝ (quaternion r (matrixRotation s Z a b)) (Z.matrix a b)) := by
  rw [rawPairing_vectors, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  change inner ℝ (quaternion r (Z.matrix a b)) (matrixRotation s Z a b) = _
  rw [quaternion_inner_skew, real_inner_comm]

private theorem weighted_quaternion_matrix_pairing (A : Mat) (Z : Tensor) :
    (∑ r, ∑ s, A r s * rawPairing (rawQuaternion r Z.matrix)
      (rawMatrixRotation s Z.matrix)) =
        -rawPairing (generalMixedAction A Z.matrix) Z.matrix := by
  simp_rw [quaternion_matrix_pairing]
  simp only [mul_neg, Finset.sum_neg_distrib]
  rw [generalMixedAction_pairing_sum]

/-- The full matrix generator energy follows from the actual one-fifth
Bianchi projection and the arbitrary-matrix mixed compression. -/
theorem general_generator_energy (A : Mat) (hA : symmetric A) (htA : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ r, ∑ s, A r s * rawPairing (rawGradientGenerator r Z.matrix)
      (rawGradientGenerator s Z.matrix)) = -40 * generalGradientForm A Z := by
  have hp (r s : Fin 3) :
      rawPairing (rawGradientGenerator r Z.matrix) (rawGradientGenerator s Z.matrix) =
        5 * rawPairing (rawQuaternion r Z.matrix) (rawGradientGenerator s Z.matrix) := by
    have h := derivativeQuaternion_pairing r Z (totalGradientTensor s Z) hb
      (totalGradientTensor_bianchi s Z hz hb)
    rw [totalGradientTensor_matrix s Z hz hb] at h
    change rawPairing (rawQuaternion r Z.matrix) (rawGradientGenerator s Z.matrix) = _ at h
    linarith
  have hgen (s : Fin 3) : rawGradientGenerator s Z.matrix =
      rawQuaternion s Z.matrix + rawMatrixRotation s Z.matrix := rfl
  have hs :
      (∑ r, ∑ s, A r s * rawPairing (rawGradientGenerator r Z.matrix)
        (rawGradientGenerator s Z.matrix)) =
      5 * ((∑ r, ∑ s, A r s * rawPairing (rawQuaternion r Z.matrix)
        (rawQuaternion s Z.matrix)) +
        (∑ r, ∑ s, A r s * rawPairing (rawQuaternion r Z.matrix)
          (rawMatrixRotation s Z.matrix))) := by
    simp_rw [hp, hgen, rawPairing_add_right]
    simp only [Fin.sum_univ_three]
    ring
  rw [hs, weighted_rawQuaternion_self, weighted_quaternion_matrix_pairing,
    generalMixedAction_self_pairing A hA htA Z hz hb]
  have ht : Matrix.trace A = 0 := htA
  rw [ht]
  ring

end
end PositiveEinsteinFour.Bianchi


end


section

/-! Polarized real-vector cost identities in twelve Bianchi coordinates,
including the three off-diagonal generator pairs. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian HighestHessian

noncomputable section

private theorem coordinatePairing_comm (v w : Fin 3 → Vec) :
    coordinatePairing v w = coordinatePairing w v := by
  unfold coordinatePairing
  rw [real_inner_comm (v 0) (w 0), real_inner_comm (v 1) (w 1),
    real_inner_comm (v 2) (w 2)]

private theorem reverse_coefficient_pairing (s t : Fin 3) (v : Fin 3 → Vec)
    (h : (∑ r, coordinatePairing (costCoefficientCoordinates s r v)
      (costCoefficientCoordinates t r v)) =
        44 * coordinatePairing (generatorCoordinates s v) (generatorCoordinates t v)) :
    (∑ r, coordinatePairing (costCoefficientCoordinates t r v)
      (costCoefficientCoordinates s r v)) =
        44 * coordinatePairing (generatorCoordinates t v) (generatorCoordinates s v) := by
  calc
    _ = ∑ r, coordinatePairing (costCoefficientCoordinates s r v)
        (costCoefficientCoordinates t r v) := by
      apply Finset.sum_congr rfl
      intro r _
      exact coordinatePairing_comm _ _
    _ = 44 * coordinatePairing (generatorCoordinates s v) (generatorCoordinates t v) := h
    _ = _ := congrArg (fun z : ℝ => 44 * z) (coordinatePairing_comm _ _)

theorem rawPairing_eq_rawNorm (Z : RawGradient) : rawPairing Z Z = rawNorm Z := by
  rw [rawPairing_vectors]
  simp only [real_inner_self_eq_norm_sq, rawNorm]

theorem costParameters_pairing (v w : Fin 3 → Vec) :
    rawPairing (costParameters v).matrix (costParameters w).matrix =
      coordinatePairing v w := by
  have h : rawPairing (costParameters (v + w)).matrix (costParameters (v + w)).matrix =
      coordinateNorm (v + w) := by
    rw [rawPairing_eq_rawNorm, rawNorm_matrix, costParameters_norm]
  simp only [costParameters_matrix_add, rawPairing_add_left, rawPairing_add_right] at h
  rw [rawPairing_comm (costParameters w).matrix (costParameters v).matrix] at h
  simp only [rawPairing_eq_rawNorm, rawNorm_matrix, costParameters_norm] at h
  simp only [coordinateNorm, Pi.add_apply, norm_add_sq_real] at h
  unfold coordinatePairing
  linarith

private theorem coefficient_pairing_01 (v : Fin 3 → Vec) :
    (∑ r, coordinatePairing (costCoefficientCoordinates 0 r v)
      (costCoefficientCoordinates 1 r v)) =
      44 * coordinatePairing (generatorCoordinates 0 v) (generatorCoordinates 1 v) := by
  simp [coordinatePairing, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion, PiLp.inner_apply,
    RCLike.inner_apply, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

private theorem coefficient_pairing_02 (v : Fin 3 → Vec) :
    (∑ r, coordinatePairing (costCoefficientCoordinates 0 r v)
      (costCoefficientCoordinates 2 r v)) =
      44 * coordinatePairing (generatorCoordinates 0 v) (generatorCoordinates 2 v) := by
  simp [coordinatePairing, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion, PiLp.inner_apply,
    RCLike.inner_apply, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

private theorem coefficient_pairing_12 (v : Fin 3 → Vec) :
    (∑ r, coordinatePairing (costCoefficientCoordinates 1 r v)
      (costCoefficientCoordinates 2 r v)) =
      44 * coordinatePairing (generatorCoordinates 1 v) (generatorCoordinates 2 v) := by
  simp [coordinatePairing, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion, PiLp.inner_apply,
    RCLike.inner_apply, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

private theorem rawCostCoefficient_pairing_of_ne (s t : Fin 3) (hst : s ≠ t)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ r, rawPairing (rawCostCoefficient s r Z.matrix) (rawCostCoefficient t r Z.matrix)) =
      44 * rawPairing (rawGradientGenerator s Z.matrix) (rawGradientGenerator t Z.matrix) := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  simp_rw [rawCostCoefficient_coordinates, generator_coordinates, costParameters_pairing]
  fin_cases s <;> fin_cases t
  · exact (hst rfl).elim
  · exact coefficient_pairing_01 v
  · exact coefficient_pairing_02 v
  · exact reverse_coefficient_pairing 0 1 v (coefficient_pairing_01 v)
  · exact (hst rfl).elim
  · exact coefficient_pairing_12 v
  · exact reverse_coefficient_pairing 0 2 v (coefficient_pairing_02 v)
  · exact reverse_coefficient_pairing 1 2 v (coefficient_pairing_12 v)
  · exact (hst rfl).elim

/-- The full polarized coefficient identity, including the trace term. -/
theorem rawCostCoefficient_pairing (s t : Fin 3)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ r, rawPairing (rawCostCoefficient s r Z.matrix) (rawCostCoefficient t r Z.matrix)) =
      (if s = t then 84 * Z.squaredNorm else 0) +
        44 * rawPairing (rawGradientGenerator s Z.matrix) (rawGradientGenerator t Z.matrix) := by
  by_cases hst : s = t
  · subst t
    simp only [ite_true, if_true, rawPairing_eq_rawNorm]
    have h := rawCostCoefficient_norm s Z hz hb
    linarith
  · simp only [hst, ite_false, if_false, zero_add]
    exact rawCostCoefficient_pairing_of_ne s t hst Z hz hb

end
end PositiveEinsteinFour.Bianchi
end


section

/-! The sharp real-vector projection cost in an arbitrary Weyl frame. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open Matrix TraceHessian HighestHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

private theorem quaternion_combination_pairing (a : Vec) (r t : ℝ)
    (c d : Fin 3 → ℝ) :
    (∑ i : Fin 4, (r * a i + ∑ s, c s * quaternion s a i) *
      (t * a i + ∑ s, d s * quaternion s a i)) =
        ‖a‖ ^ 2 * (r * t + ∑ s, c s * d s) := by
  simp [EuclideanSpace.real_norm_sq_eq, quaternion, Fin.sum_univ_four, Fin.sum_univ_three]
  ring

private theorem rawPairing_entries (Z W : RawGradient) :
    rawPairing Z W = ∑ b, ∑ c, ∑ j : Fin 4, Z b c j * W b c j := by
  rw [rawPairing_vectors]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Polarized version of the real outer-quaternion calculation. -/
theorem quaternionCombination_pairing (a : Vec) (Z W : RawGradient)
    (C D : Fin 3 → RawGradient) :
    hessianPairing (quaternionCombination a Z C) (quaternionCombination a W D) =
      ‖a‖ ^ 2 * (rawPairing Z W + ∑ s, rawPairing (C s) (D s)) := by
  have h (b c : Fin 3) (j : Fin 4) :
      (∑ i, quaternionCombination a Z C i j b c * quaternionCombination a W D i j b c) =
        ‖a‖ ^ 2 * (Z b c j * W b c j + ∑ s, C s b c j * D s b c j) := by
    simpa only [quaternionCombination, mul_comm] using
      quaternion_combination_pairing a (Z b c j) (W b c j)
        (fun s => C s b c j) (fun s => D s b c j)
  calc
    _ = ∑ b, ∑ c, ∑ j : Fin 4, ∑ i : Fin 4,
        quaternionCombination a Z C i j b c * quaternionCombination a W D i j b c := by
      unfold hessianPairing
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ‖a‖ ^ 2 * ((∑ b, ∑ c, ∑ j : Fin 4, Z b c j * W b c j) +
        ∑ b, ∑ c, ∑ j : Fin 4, ∑ s, C s b c j * D s b c j) := by
      simp_rw [h]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      simp only [rawPairing_entries]
      congr 2
      calc
        _ = ∑ b, ∑ c, ∑ s, ∑ j : Fin 4, C s b c j * D s b c j := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
        _ = ∑ b, ∑ s, ∑ c, ∑ j : Fin 4, C s b c j * D s b c j := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm

/-- Both generator indices of the real-vector identity are retained. -/
theorem totalPlus_weightPlusPart_pairing (s t : Fin 3) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianPairing (totalPlus s (weightPlusPart a Z))
      (totalPlus t (weightPlusPart a Z)) =
      ‖a‖ ^ 2 * ((if s = t then (7 / 12 : ℝ) * Z.squaredNorm else 0) +
        (3 / 4 : ℝ) * rawPairing (rawGradientGenerator s Z.matrix)
          (rawGradientGenerator t Z.matrix)) := by
  rw [totalPlus_weightPlusPart, totalPlus_weightPlusPart,
    hessianPairing_smul_left, hessianPairing_smul_right,
    quaternionCombination_pairing, rawPairing_smul_left, rawPairing_smul_right,
    rawCostCoefficient_pairing s t Z hz hb]
  by_cases hst : s = t <;> simp only [hst, ite_true, if_true, ite_false, if_false] <;> ring

/-- The plus contribution to the sharp cost, with a full symmetric Weyl matrix. -/
theorem totalPlus_weightPlusPart_generalCost_oai (A : Mat)
    (hA : symmetric A) (ht : traceFree A) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianGram A (fun r => totalPlus r (weightPlusPart a Z)) =
      -30 * ‖a‖ ^ 2 * generalGradientForm A Z := by
  have he := general_generator_energy A hA ht Z hz hb
  change (∑ r, A r r) = 0 at ht
  simp only [hessianGram, totalPlus_weightPlusPart_pairing _ _ a Z hz hb]
  simp only [Fin.sum_univ_three] at he ht ⊢
  norm_num
  linear_combination (3 / 4 : ℝ) * ‖a‖ ^ 2 * he +
    (7 / 12 : ℝ) * ‖a‖ ^ 2 * Z.squaredNorm * ht

end
end PositiveEinsteinFour.Bianchi

end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost_oai := @OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost_oai
