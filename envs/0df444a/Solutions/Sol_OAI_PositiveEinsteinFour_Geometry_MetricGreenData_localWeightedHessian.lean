-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:34:43.584406+00:00
-- url     : https://prove2.me/submissions/23130ef4-7de8-497f-96e2-dfbcf1bcf4b7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_coupling_matrix_coordinates
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_totalGradientTensor_bianchi
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_totalGradientTensor_matrix
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_add_left
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_add_right
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_comm
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_self
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_general_weighted_highestProjection_square
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_general_weighted_trace_subtraction

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

theorem hessianPairing_add_left (X Y Z : Hessian) :
    hessianPairing (X + Y) Z = hessianPairing X Z + hessianPairing Y Z := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b + Y i j a b) * Z i j a b) = _
  simp only [add_mul, hessianPairing, Finset.sum_add_distrib]

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
-- module Solutions.OAIQ091_EF.EinsteinFour_CoupledCasimir
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.QuaternionFrame.fieldRaw_rawField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The plus spectral polynomial on the actual highest-Hessian space. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem totalPlus_inner_outer (s : Fin 3) (X : Hessian) :
    totalPlus s X = innerAction s X + outerAction s X := by
  funext i j b c
  change totalPlus s X i j b c = innerAction s X i j b c + outerAction s X i j b c
  rw [show outerAction s X i j b c =
    ∑ k, quaternionMatrix s i k * X k j b c from
      (quaternionMatrix_apply s (WithLp.toLp 2 (fun k => X k j b c)) i).symm]
  simp only [totalPlus, innerAction]
  ring

theorem innerAction_rawSlice (s : Fin 3) (X : Hessian) (i : Fin 4) :
    rawSlice (innerAction s X) i = rawGradientGenerator s (rawSlice X i) := by
  funext b c
  ext j
  have h := quaternionMatrix_apply s (rawSlice X i b c) j
  simp only [rawSlice, Fin.sum_univ_four] at h
  simp [rawSlice, innerAction, rawGradientGenerator, rawMatrixRotation,
    matrixAction, Fin.sum_univ_three, Fin.sum_univ_four]
  rw [← h]
  ring

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCoordinateModel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

theorem rawPairing_sum_left {ι : Type*} [Fintype ι]
    (f : ι → RawGradient) (W : RawGradient) :
    rawPairing (∑ i, f i) W = ∑ i, rawPairing (f i) W := by
  simp only [rawPairing_vectors, Finset.sum_apply, sum_inner]
  calc
    _ = ∑ a : Fin 3, ∑ i : ι, ∑ b : Fin 3, inner ℝ (f i a b) (W a b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

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
theorem matrixSlotOperator_apply (A : Mat) (Z : GradientVector) (p : GradientIndex) :
    matrixSlotOperator A Z p = ∑ q, matrixSlotKernel A p q * Z q := rfl

private theorem matrixEntryKernel_action (A M : Mat) (hM : traceFree M)
    (a b : Fin 3) :
    (∑ p : Fin 3 × Fin 3, matrixEntryKernel A (a, b) p * M p.1 p.2) =
      matrixSlotAction A M a b := by
  have ht := hM
  simp only [traceFree, Fin.sum_univ_three] at ht
  have h22 : M 2 2 = -M 0 0 - M 1 1 := by linarith
  fin_cases a <;> fin_cases b <;>
    simp [matrixEntryKernel, matrixSlotAction, Fintype.sum_prod_type, Fin.sum_univ_three, h22]
  all_goals ring

/-- On actual trace-free gradient slices, the bounded operator is precisely
`B_F(A)` rather than an independently postulated coefficient. -/
theorem matrixSlotOperator_on_traceFree (A : Mat) (Z : GradientVector)
    (hZ : ∀ i, (∑ a, Z (i, a, a)) = 0) (i : Fin 4) (a b : Fin 3) :
    matrixSlotOperator A Z (i, a, b) =
      matrixSlotAction A (fun c d => Z (i, c, d)) a b := by
  rw [matrixSlotOperator_apply]
  simp only [matrixSlotKernel, Fintype.sum_prod_type, ite_mul, zero_mul]
  have hs : (∑ j : Fin 4, ∑ c : Fin 3, ∑ d : Fin 3,
      if i = j then matrixEntryKernel A (a, b) (c, d) * Z (j, c, d) else 0) =
      ∑ c : Fin 3, ∑ d : Fin 3, matrixEntryKernel A (a, b) (c, d) * Z (i, c, d) := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp
  rw [hs]
  simpa only [Fintype.sum_prod_type] using
    matrixEntryKernel_action A (fun c d => Z (i, c, d)) (hZ i) a b

end

end PositiveEinsteinFour.Geometry

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
-- module Solutions.OAIQ091_EF.EinsteinFour_HessianCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.QuaternionFrame.fieldRaw_rawField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Curvature compression on all actual inner-Bianchi Hessian tensors. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem hessianPairing_slices (X Y : Hessian) :
    hessianPairing X Y = ∑ i, rawPairing (rawSlice X i) (rawSlice Y i) := by
  rw [← tensorCoordinates_pairing]
  simp only [Fintype.sum_prod_type, tensorCoordinates, rawPairing, rawCoordinates, rawSlice]

theorem rawSlice_eq_innerSlice (X : Hessian)
    (hmatrix : ∀ i j, symmetric (X i j)) (i : Fin 4) :
    rawSlice X i = (innerSlice X i).matrix := by
  funext a b
  exact (innerSlice_matrix X i (hmatrix i) a b).symm

theorem outerAction_rawSlice (s : Fin 3) (X : Hessian) (i : Fin 4) :
    rawSlice (outerAction s X) i =
      ∑ k : Fin 4, quaternionMatrix s i k • rawSlice X k := by
  funext a b
  ext j
  have h := quaternionMatrix_apply s (WithLp.toLp 2 (fun k => X k j a b)) i
  simpa [rawSlice, outerAction, Fin.sum_univ_four] using h.symm

private theorem sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem rawQuaternion_pairing (s : Fin 3) (Z W : RawGradient) :
    rawPairing (rawQuaternion s Z) W =
      ∑ j, ∑ k, quaternionMatrix s j k *
        matrixPairing (rawMatrixAt Z k) (rawMatrixAt W j) := by
  simp only [rawPairing, rawCoordinates, rawQuaternion, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [← quaternionMatrix_apply]
  simp only [Finset.sum_mul]
  rw [sum_rotate]
  simp only [rawMatrixAt, matrixPairing, Finset.mul_sum, mul_assoc]

end
end PositiveEinsteinFour.HighestHessian

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
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The matrix-slot Hessian quadratic form is exactly the left side of
the varying-operator Green identity, including the unsymmetrized weight. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem gradientVector_innerSlice (X : Hessian) (i : Fin 4)
    (hs : ∀ j, symmetric (X i j)) :
    tensorGradientVector (innerSlice X i) = gradientVector (X i) := by
  ext p
  rcases p with ⟨j, a, b⟩
  change (innerSlice X i).matrix a b j = X i j a b
  rw [innerSlice_matrix X i hs]

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Match the opposite-block Hessian quadratic with the same covector
ordering used by the actual curvature Green identity. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

theorem oppositeMatrix_eq_neg_rightQuaternion (s : Fin 3) (i j : Fin 4) :
    Angular.oppositeMatrix s i j = -rightQuaternion s i j := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [Angular.oppositeMatrix, oppositeQuaternion, quaternionMatrix, rightQuaternion]

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The invariant Ricci equation has the actual Bianchi compression in
every orthonormal frame, without imposing a diagonal Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open Bianchi TraceHessian

noncomputable section

/-- The concrete vector-valued matrix action is the bounded matrix-slot
operator used in the metric Green identity. -/
theorem matrixSlotOperator_generalTensor (A : Mat) (Z : Tensor) (hz : Z.traceFree) :
    matrixSlotOperator A (tensorGradientVector Z) =
      rawGradientVector (generalMatrixAction A Z.matrix) := by
  have htrace (i : Fin 4) : (∑ a, tensorGradientVector Z (i, a, a)) = 0 := by
    have h := congrArg (fun v : Vec => v i) hz
    simpa [tensorGradientVector, rawGradientVector, rawCoordinates,
      Tensor.traceFree, Tensor.matrix, Fin.sum_univ_three] using h
  ext p
  rcases p with ⟨i, a, b⟩
  rw [matrixSlotOperator_on_traceFree A _ htrace]
  rfl

theorem matrixSlotOperator_general_pairing (A : Mat) (Z : Tensor) (hz : Z.traceFree) :
    inner ℝ (matrixSlotOperator A (tensorGradientVector Z)) (tensorGradientVector Z) =
      rawPairing (generalMatrixAction A Z.matrix) Z.matrix := by
  rw [matrixSlotOperator_generalTensor A Z hz]
  exact inner_rawGradientVector _ _

end
end PositiveEinsteinFour.Geometry
end


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

theorem hessianPairing_add_right (X Y Z : Hessian) :
    hessianPairing X (Y + Z) = hessianPairing X Y + hessianPairing X Z := by
  rw [hessianPairing_comm X, hessianPairing_add_left,
    hessianPairing_comm Y X, hessianPairing_comm Z X]

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


namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian CurvatureContraction PositiveEinsteinFour.Geometry

noncomputable section

private theorem sum_rotate_three {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The actual matrix-slot operator is the sum of its four inner-slice forms. -/
theorem matrixHessianPairing_innerSlices (A : Mat) (X : Hessian)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j)) :
    matrixHessianPairing A X X = ∑ i, generalGradientForm A (innerSlice X i) := by
  unfold matrixHessianPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm, ← gradientVector_innerSlice X i (fun j => (hm i j).1),
    matrixSlotOperator_general_pairing A _ (innerSlice_traceFree X i (fun j => (hm i j).2))]
  rfl

/-- The full weighted inner-generator energy uses only each slice's Bianchi identity. -/
theorem general_innerAction_energy (A : Mat) (hA : symmetric A) (htA : traceFree A)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    hessianGram A (fun r => innerAction r X) = -40 * matrixHessianPairing A X X := by
  simp only [hessianGram, hessianPairing_slices, innerAction_rawSlice, Finset.mul_sum]
  rw [sum_rotate_three]
  simp_rw [rawSlice_eq_innerSlice X (fun i j => (hm i j).1)]
  simp_rw [general_generator_energy A hA htA _
    (innerSlice_traceFree X _ (fun j => (hm _ j).2))
    (innerSlice_bianchi X _ (fun j => (hm _ j).1) (hb _))]
  rw [← Finset.mul_sum, matrixHessianPairing_innerSlices A X hm]

private theorem generalDerivativeSlot_slices (r s : Fin 3) (X : Hessian) :
    generalDerivativeSlot quaternionMatrix r s X =
      ∑ i, ∑ k, quaternionMatrix r i k *
        rawPairing (rawQuaternion s (rawSlice X k)) (rawSlice X i) := by
  have hm (k l : Fin 4) : rawMatrixAt (rawSlice X k) l = X k l := rfl
  simp_rw [rawQuaternion_pairing, hm]
  simp only [Finset.mul_sum, mul_assoc, generalDerivativeSlot]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

private theorem hessianPairing_outer_inner_cross (r s : Fin 3) (X : Hessian) :
    hessianPairing (outerAction r X) (innerAction s X) =
      ∑ i, ∑ k, quaternionMatrix r i k *
        rawPairing (rawSlice X k) (rawGradientGenerator s (rawSlice X i)) := by
  rw [hessianPairing_slices]
  simp_rw [outerAction_rawSlice, rawPairing_sum_left, rawPairing_smul_left,
    innerAction_rawSlice]

/-- Off-diagonal as well as diagonal derivative-slot compression. -/
theorem generalDerivativeSlot_inner_cross (r s : Fin 3) (X : Hessian)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i t, divergence X i t = 0) :
    generalDerivativeSlot quaternionMatrix r s X =
      -(1 / 5 : ℝ) * hessianPairing (outerAction r X) (innerAction s X) := by
  have hr := rawSlice_eq_innerSlice X (fun i j => (hm i j).1)
  have hbianchi (i : Fin 4) : (innerSlice X i).bianchi :=
    innerSlice_bianchi X i (fun j => (hm i j).1) (hb i)
  have hc (i k : Fin 4) :
      rawPairing (rawQuaternion s (rawSlice X k)) (rawSlice X i) =
        (1 / 5 : ℝ) * rawPairing (rawGradientGenerator s (rawSlice X k))
          (rawSlice X i) := by
    simp_rw [hr]
    exact derivativeQuaternion_pairing s (innerSlice X k) (innerSlice X i)
      (hbianchi k) (hbianchi i)
  rw [generalDerivativeSlot_slices, hessianPairing_outer_inner_cross]
  simp_rw [hc]
  have hswap : (∑ i, ∑ k, quaternionMatrix r i k *
      rawPairing (rawGradientGenerator s (rawSlice X k)) (rawSlice X i)) =
        -(∑ i, ∑ k, quaternionMatrix r i k *
          rawPairing (rawSlice X k) (rawGradientGenerator s (rawSlice X i))) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [quaternionMatrix_skew r k i, rawPairing_comm]
    ring
  calc
    _ = (1 / 5 : ℝ) * (∑ i, ∑ k, quaternionMatrix r i k *
        rawPairing (rawGradientGenerator s (rawSlice X k)) (rawSlice X i)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hswap]; ring


private theorem outerAction_pairing (r s : Fin 3) (X : Hessian) :
    hessianPairing (outerAction r X) (outerAction s X) =
      if r = s then hessianNormSq X else 0 := by
  have h (a b : Fin 3) (j : Fin 4) :
      (∑ i, outerAction r X i j a b * outerAction s X i j a b) =
        if r = s then ∑ i, X i j a b ^ 2 else 0 := by
    have hh := Bianchi.quaternion_frame_inner r s
      (WithLp.toLp 2 (fun i => X i j a b))
    simpa only [outerAction, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      EuclideanSpace.real_norm_sq_eq, mul_comm] using hh
  unfold hessianPairing hessianNormSq
  have hf (a b : Fin 3) :
      (∑ i, ∑ j, outerAction r X i j a b * outerAction s X i j a b) =
        if r = s then ∑ i, ∑ j, X i j a b ^ 2 else 0 := by
    rw [Finset.sum_comm]
    simp_rw [h]
    by_cases hrs : r = s
    · simp only [hrs, ite_true, if_true]
      exact Finset.sum_comm
    · simp [hrs]
  simp_rw [hf]
  by_cases hrs : r = s <;> simp [hrs]

private theorem general_outerAction_energy (A : Mat) (X : Hessian) (htA : traceFree A) :
    hessianGram A (fun r => outerAction r X) = 0 := by
  simp only [hessianGram, outerAction_pairing, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, ← Finset.sum_mul]
  change (∑ r, A r r) * hessianNormSq X = 0
  rw [htA, zero_mul]

private theorem sum_swap_last_two {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

/-- Reordering the actual derivative contraction and the two Weyl indices. -/
theorem generalDerivativePairing_eq (Q : Fin 3 → Mat4) (A : Mat) (X : Hessian) :
    derivativePairing (generalCoefficient Q A) X X =
      (1 / 2 : ℝ) * ∑ r, ∑ s, A r s * generalDerivativeSlot Q r s X := by
  simp only [derivativePairing, generalCoefficient, Finset.sum_mul, Finset.mul_sum]
  rw [sum_swap_last_two]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fintype.sum_prod_type, generalDerivativeSlot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have hm : matrixPairing (X i j) (X k l) = matrixPairing (X k l) (X i j) := by
    simp only [matrixPairing, mul_comm]
  rw [hm]
  ring

private theorem general_cross_energy (A : Mat) (X : Hessian)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    (∑ r, ∑ s, A r s * hessianPairing (outerAction r X) (innerAction s X)) =
      -10 * derivativePairing (generalCoefficient quaternionMatrix A) X X := by
  rw [generalDerivativePairing_eq]
  have hc (r s : Fin 3) := generalDerivativeSlot_inner_cross r s X hm hb
  have hh (r s : Fin 3) : hessianPairing (outerAction r X) (innerAction s X) =
      -5 * generalDerivativeSlot quaternionMatrix r s X := by linarith [hc r s]
  simp_rw [hh]
  simp only [Fin.sum_univ_three]
  ring

/-- No outer-slot symmetry is required for the full-matrix plus compression. -/
theorem general_plus_energy (A : Mat) (hA : symmetric A) (htA : traceFree A)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    hessianGram A (fun r => totalPlus r X) =
      -40 * matrixHessianPairing A X X -
        20 * derivativePairing (generalCoefficient quaternionMatrix A) X X := by
  have hcross : (∑ r, ∑ s, A r s * hessianPairing (innerAction r X) (outerAction s X)) =
      ∑ r, ∑ s, A r s * hessianPairing (outerAction r X) (innerAction s X) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [hA s r, hessianPairing_comm]
  have hi := general_innerAction_energy A hA htA X hm hb
  have ho := general_outerAction_energy A X htA
  have hc := general_cross_energy A X hm hb
  unfold hessianGram at hi ho ⊢
  simp_rw [totalPlus_inner_outer, hessianPairing_add_left, hessianPairing_add_right]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hi, ho, hcross, hc]
  ring

private theorem totalMinus_pairing_slice (r s : Fin 3) (X : Hessian) (a b : Fin 3) :
    (∑ i, ∑ j, totalMinus r X i j a b * totalMinus s X i j a b) =
      (if r = s then 2 * ∑ i, ∑ j, X i j a b ^ 2 else 0) -
      (∑ i, ∑ j, ∑ k, ∑ l,
        rightQuaternion r i k * rightQuaternion s j l * X k l a b * X i j a b) -
      (∑ i, ∑ j, ∑ k, ∑ l,
        rightQuaternion s i k * rightQuaternion r j l * X k l a b * X i j a b) := by
  fin_cases r <;> fin_cases s <;>
    simp [totalMinus, rightQuaternion, Fin.sum_univ_four] <;> ring

private theorem sum_six_rotate
    (f : Fin 3 → Fin 3 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ i, ∑ j, ∑ k, ∑ l, f a b i j k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, f a b i j k l := by
  have h := (Equiv.prodComm (Fin 3 × Fin 3)
    (Fin 4 × Fin 4 × Fin 4 × Fin 4)).sum_comp
    (fun p => f p.2.1 p.2.2 p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem general_minus_energy_entry (r s : Fin 3) (X : Hessian) :
    hessianPairing (totalMinus r X) (totalMinus s X) =
      (if r = s then 2 * hessianNormSq X else 0) -
        generalDerivativeSlot rightQuaternion r s X - generalDerivativeSlot rightQuaternion s r X := by
  unfold hessianPairing
  simp_rw [totalMinus_pairing_slice]
  simp only [Finset.sum_sub_distrib]
  have hex (r s : Fin 3) :
      (∑ a, ∑ b, ∑ i, ∑ j, ∑ k, ∑ l,
        rightQuaternion r i k * rightQuaternion s j l * X k l a b * X i j a b) =
      generalDerivativeSlot rightQuaternion r s X := by
    unfold generalDerivativeSlot matrixPairing
    simp only [Finset.mul_sum]
    rw [sum_six_rotate]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hex, hex]
  by_cases hrs : r = s <;>
    simp only [hrs, ite_true, if_true, ite_false, if_false, hessianNormSq, ← Finset.mul_sum,
      Finset.sum_const_zero]

/-- The full-matrix opposite-block compression holds on every tensor. -/
theorem general_minus_energy (U : Mat) (hU : symmetric U) (htU : traceFree U)
    (X : Hessian) :
    hessianGram U (fun r => totalMinus r X) =
      -4 * derivativePairing (generalCoefficient Angular.oppositeMatrix U) X X := by
  have hQ (r s : Fin 3) : generalDerivativeSlot Angular.oppositeMatrix r s X =
      generalDerivativeSlot rightQuaternion r s X := by
    simp only [generalDerivativeSlot, oppositeMatrix_eq_neg_rightQuaternion, neg_mul_neg]
  have hc : (∑ r, ∑ s, U r s * generalDerivativeSlot rightQuaternion s r X) =
      ∑ r, ∑ s, U r s * generalDerivativeSlot rightQuaternion r s X := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [hU s r]
  rw [generalDerivativePairing_eq]
  simp_rw [hQ]
  simp only [hessianGram, general_minus_energy_entry, mul_sub, Finset.sum_sub_distrib]
  rw [hc]
  have hz : (∑ r, ∑ s, U r s * if r = s then 2 * hessianNormSq X else 0) = 0 := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true,
      ← Finset.sum_mul]
    rw [show (∑ r, U r r) = 0 from htU, zero_mul]
  rw [hz]
  ring

/-- Exact equality on the full inner-Bianchi space, including the
unsymmetrized derivative of a scalar weight. -/
theorem generalOriginalCurvatureForm_eq_of_inner_bianchi (A U : Mat) (X : Hessian)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) :
    generalOriginalCurvatureForm A U X = generalCasimirCurvatureForm A U X := by
  unfold generalOriginalCurvatureForm generalCasimirCurvatureForm
  rw [general_plus_energy A hA htA X hm hb, general_minus_energy U hU htU X]
  ring

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The exact prescribed trace in arbitrary matrix coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

/-- Subtracting the actual matrix Weyl equation removes the complete
Ricci commutator, including the skew derivative part. -/
theorem general_trace_subtracted_condition (A : Mat) (X : Hessian)
    (hA : symmetric A) (htA : traceFree A)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0)
    (hcomm : ∀ i j a b, X i j a b - X j i a b = bundleCurvatureAction A i j A a b) :
    condition (X - traceComponent (weylLaplacian A)) := by
  have hsM := weylLaplacian_symmetric A hA
  have htM := weylLaplacian_traceFree A htA
  have htrace := weyl_trace_eq_of_bianchi_commutator A hA htA X hmatrix hbianchi hcomm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    ext a b
    change X i j a b - traceComponent (weylLaplacian A) i j a b =
      X j i a b - traceComponent (weylLaplacian A) j i a b
    have h := hcomm i j a b
    have hc := traceComponent_weylLaplacian_skew A hA htA i j a b
    linarith
  · intro i j
    constructor
    · intro a b
      change X i j a b - traceComponent (weylLaplacian A) i j a b =
        X i j b a - traceComponent (weylLaplacian A) i j b a
      rw [(hmatrix i j).1 a b, traceComponent_symmetric _ hsM htM i j a b]
    · change (∑ a, (X i j a a - traceComponent (weylLaplacian A) i j a a)) = 0
      rw [Finset.sum_sub_distrib, (hmatrix i j).2,
        traceComponent_traceFree _ hsM htM i j, sub_self]
  · unfold hessianTrace
    change (∑ i, (X i i - traceComponent (weylLaplacian A) i i)) = 0
    rw [Finset.sum_sub_distrib]
    change hessianTrace X - hessianTrace (traceComponent (weylLaplacian A)) = 0
    rw [htrace, trace_traceComponent, sub_self]
  · intro i r
    rw [divergence_sub, hbianchi, traceComponent_divergence _ hsM htM, sub_self]

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The arbitrary-frame weighted Hessian square in the original Green form. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

private theorem innerBianchi_add (X Y : Hessian)
    (hmX : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbX : ∀ i r, divergence X i r = 0)
    (hmY : ∀ i j, symmetric (Y i j) ∧ traceFree (Y i j))
    (hbY : ∀ i r, divergence Y i r = 0) :
    (∀ i j, symmetric ((X + Y) i j) ∧ traceFree ((X + Y) i j)) ∧
      (∀ i r, divergence (X + Y) i r = 0) := by
  constructor
  · intro i j
    constructor
    · intro a b
      change X i j a b + Y i j a b = X i j b a + Y i j b a
      rw [(hmX i j).1 a b, (hmY i j).1 a b]
    · change (∑ a, (X i j a a + Y i j a a)) = 0
      rw [Finset.sum_add_distrib, (hmX i j).2, (hmY i j).2, add_zero]
  · intro i r
    rw [divergence_add, hbX i r, hbY i r, add_zero]

/-- Polarization retains the exact full-matrix Green form on arbitrary
inner-Bianchi tensors, including nonsymmetric outer derivative slots. -/
theorem generalOriginal_polarization (A U : Mat) (hA : symmetric A) (hU : symmetric U)
    (htA : traceFree A) (htU : traceFree U) (X Y : Hessian)
    (hmX : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbX : ∀ i r, divergence X i r = 0)
    (hmY : ∀ i j, symmetric (Y i j) ∧ traceFree (Y i j))
    (hbY : ∀ i r, divergence Y i r = 0) :
    (generalOriginalCurvatureForm A U (X + Y) - generalOriginalCurvatureForm A U X -
      generalOriginalCurvatureForm A U Y) / 2 = generalCurvaturePairing A U X Y := by
  have hsum := innerBianchi_add X Y hmX hbX hmY hbY
  rw [generalOriginalCurvatureForm_eq_of_inner_bianchi A U (X + Y) hA hU htA htU
      hsum.1 hsum.2,
    generalOriginalCurvatureForm_eq_of_inner_bianchi A U X hA hU htA htU hmX hbX,
    generalOriginalCurvatureForm_eq_of_inner_bianchi A U Y hA hU htA htU hmY hbY,
    ← generalCurvaturePairing_self, ← generalCurvaturePairing_self,
    ← generalCurvaturePairing_self]
  rw [generalCurvaturePairing_add_left, generalCurvaturePairing_add_right,
    generalCurvaturePairing_add_right, generalCurvaturePairing_comm A U hA hU Y X]
  ring

theorem general_weightedQuadratic_eq (A U : Mat) (hA : symmetric A) (hU : symmetric U)
    (htA : traceFree A) (htU : traceFree U) (m : ℝ) (X Y : Hessian)
    (hmX : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbX : ∀ i r, divergence X i r = 0)
    (hmY : ∀ i j, symmetric (Y i j) ∧ traceFree (Y i j))
    (hbY : ∀ i r, divergence Y i r = 0) :
    weightedQuadratic (generalOriginalCurvatureForm A U) m X Y =
      (m * generalCurvaturePairing A U X X + generalCurvaturePairing A U X Y) / 6 := by
  unfold weightedQuadratic
  rw [generalOriginal_polarization A U hA hU htA htU X Y hmX hbX hmY hbY,
    generalOriginalCurvatureForm_eq_of_inner_bianchi A U X hA hU htA htU hmX hbX,
    ← generalCurvaturePairing_self]


/-- The full arbitrary-frame local Hessian inequality, including the exact
prescribed trace and the constructed highest-projection cost. -/
theorem general_local_weighted_original_square (A U M : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hM : symmetric M) (htM : traceFree M) (X L : Hessian)
    (hmX : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbX : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M)
    (hY : condition (X - traceComponent M))
    (hmL : ∀ i j, symmetric (L i j) ∧ traceFree (L i j))
    (hbL : ∀ i r, divergence L i r = 0)
    (x y m : ℝ) (hm : 0 < m)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    0 ≤ weightedQuadratic (generalOriginalCurvatureForm A U) m X L +
      generalTraceCorrection A U M m L +
      generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
  have hsquare := general_weighted_highestProjection_square A U hA hU
    (X - traceComponent M) L hY x y m hm hAx hUy hxy
  have hsub := general_weighted_trace_subtraction A U M hA hU htA hM htM X L
    hmX hbX htrace m
  rw [general_weightedQuadratic_eq A U hA hU htA htU m X L hmX hbX hmL hbL]
  unfold generalTraceCorrection
  linarith

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The actual Hessian after subtracting its forced trace belongs to the
highest tensor subspace. Its trace and outer symmetry are derived from
the same raw curvature commutator used in the Green identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Membership of the actual trace-free Hessian in the highest subspace
is a theorem, rather than an additional geometric input. -/
theorem MetricGreenData.highestRemainder
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (e : FrameBundle g) :
    condition (plusWeylHessian g e.base e.frame -
      traceComponent (weylLaplacian (plusWeyl g e.base e.frame))) :=
  general_trace_subtracted_condition _ _ (d.weyl.symmetric e) (d.weyl.traceFree e)
    (d.weyl.hessianMatrix e) (d.weyl.hessianBianchi e) (d.weyl.hessianCommutator e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Apply the arbitrary-matrix highest-square inequality to the actual
metric Hessian and its exact trace. No eigenframe is differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem MetricGreenData.localWeightedHessian_oai
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (hp : ShiftedCurvaturePositive g) (e : FrameBundle g)
    (m : ℝ) (hm : 0 < m) (a : Vec) :
    let A := plusWeyl g e.base e.frame
    let U := minusWeyl g e.base e.frame
    let X := plusWeylHessian g e.base e.frame
    let L := weightTensor a (plusGradientTensor g e.base e.frame)
    0 ≤ weightedQuadratic (generalOriginalCurvatureForm A U) m X L +
      generalTraceCorrection A U (weylLaplacian A) m L +
      generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
  dsimp only
  obtain ⟨x, y, hAx, hUy, hxy⟩ := hp e
  have hL := weightTensor_matrix_bianchi a (plusGradientTensor g e.base e.frame)
    (gradientTensor_traceFree _ (d.gradientConstraints e).2)
    (gradientTensor_bianchi _ (d.gradientConstraints e).1 (d.gradientBianchi e))
  exact general_local_weighted_original_square _ _ _ (d.weyl.symmetric e) (o.symmetric e)
    (d.weyl.traceFree e) (o.traceFree e)
    (weylLaplacian_symmetric _ (d.weyl.symmetric e))
    (weylLaplacian_traceFree _ (d.weyl.traceFree e)) _ _
    (d.weyl.hessianMatrix e) (d.weyl.hessianBianchi e)
    (metric_weyl_trace g d.weyl e) (d.highestRemainder e) hL.1 hL.2
    x y m hm hAx hUy hxy

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian_oai.{u_1}
