-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.costCoefficient_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T18:49:05.60597+00:00
-- url     : https://prove2.me/submissions/32d44d2a-a3f1-45d1-a557-4c14c19f31b8

import Mathlib
import Definitions.Def_OAIQ091C035
import Definitions.Def_OAIQ091C007
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_norm_0
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_norm_1
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_norm_2

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCoordinateModel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix
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

private theorem coefficient_norm_0_0 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 0 0 v) =
      6880 * ‖v 0‖ ^ 2 + 8160 * ‖v 1‖ ^ 2 + 2304 * ‖v 2‖ ^ 2 +
      (12480) * inner ℝ (v 0) (v 1) + (-3840) * inner ℝ (v 0) (v 2) +
      (-3840) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_0_1 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 0 1 v) =
      1120 * ‖v 0‖ ^ 2 + 160 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (0) * inner ℝ (v 0) (v 1) + (0) * inner ℝ (v 0) (v 2) +
      (640) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_0_2 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 0 2 v) =
      320 * ‖v 0‖ ^ 2 + 2560 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (1600) * inner ℝ (v 0) (v 1) + (320) * inner ℝ (v 0) (v 2) +
      (-320) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_1_0 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 1 0 v) =
      1120 * ‖v 0‖ ^ 2 + 160 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (0) * inner ℝ (v 0) (v 1) + (0) * inner ℝ (v 0) (v 2) +
      (640) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_1_1 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 1 1 v) =
      6880 * ‖v 0‖ ^ 2 + 8160 * ‖v 1‖ ^ 2 + 2304 * ‖v 2‖ ^ 2 +
      (-12480) * inner ℝ (v 0) (v 1) + (3840) * inner ℝ (v 0) (v 2) +
      (-3840) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_1_2 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 1 2 v) =
      320 * ‖v 0‖ ^ 2 + 2560 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (-1600) * inner ℝ (v 0) (v 1) + (-320) * inner ℝ (v 0) (v 2) +
      (-320) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_2_0 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 2 0 v) =
      320 * ‖v 0‖ ^ 2 + 2560 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (1600) * inner ℝ (v 0) (v 1) + (320) * inner ℝ (v 0) (v 2) +
      (-320) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_2_1 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 2 1 v) =
      320 * ‖v 0‖ ^ 2 + 2560 * ‖v 1‖ ^ 2 + 640 * ‖v 2‖ ^ 2 +
      (-1600) * inner ℝ (v 0) (v 1) + (-320) * inner ℝ (v 0) (v 2) +
      (-320) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, next, previous, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem coefficient_norm_2_2 (v : Fin 3 → Vec) :
    coordinateNorm (costCoefficientCoordinates 2 2 v) =
      640 * ‖v 0‖ ^ 2 + 26880 * ‖v 1‖ ^ 2 + 2304 * ‖v 2‖ ^ 2 +
      (0) * inner ℝ (v 0) (v 1) + (0) * inner ℝ (v 0) (v 2) +
      (7680) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, costCoefficientCoordinates, generatorCoordinates,
    generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

private theorem costCoefficient_norm_0 (v : Fin 3 → Vec) :
    64 * coordinateNorm (generatorCoordinates 0 v) +
      (∑ r : Fin 3, coordinateNorm (costCoefficientCoordinates 0 r v)) =
        84 * coordinateNorm v + 108 * coordinateNorm (generatorCoordinates 0 v) := by
  rw [Fin.sum_univ_three, generator_norm_0,
    coefficient_norm_0_0, coefficient_norm_0_1, coefficient_norm_0_2]
  unfold coordinateNorm
  ring

private theorem costCoefficient_norm_1 (v : Fin 3 → Vec) :
    64 * coordinateNorm (generatorCoordinates 1 v) +
      (∑ r : Fin 3, coordinateNorm (costCoefficientCoordinates 1 r v)) =
        84 * coordinateNorm v + 108 * coordinateNorm (generatorCoordinates 1 v) := by
  rw [Fin.sum_univ_three, generator_norm_1,
    coefficient_norm_1_0, coefficient_norm_1_1, coefficient_norm_1_2]
  unfold coordinateNorm
  ring

private theorem costCoefficient_norm_2 (v : Fin 3 → Vec) :
    64 * coordinateNorm (generatorCoordinates 2 v) +
      (∑ r : Fin 3, coordinateNorm (costCoefficientCoordinates 2 r v)) =
        84 * coordinateNorm v + 108 * coordinateNorm (generatorCoordinates 2 v) := by
  rw [Fin.sum_univ_three, generator_norm_2,
    coefficient_norm_2_0, coefficient_norm_2_1, coefficient_norm_2_2]
  unfold coordinateNorm
  ring

/-- The scalar matrix certificate yielding the real-vector curvature cost. -/
theorem costCoefficient_norm_oai (s : Fin 3) (v : Fin 3 → Vec) :
    64 * coordinateNorm (generatorCoordinates s v) +
      (∑ r : Fin 3, coordinateNorm (costCoefficientCoordinates s r v)) =
        84 * coordinateNorm v + 108 * coordinateNorm (generatorCoordinates s v) := by
  fin_cases s
  · exact costCoefficient_norm_0 v
  · exact costCoefficient_norm_1 v
  · exact costCoefficient_norm_2 v


end
end PositiveEinsteinFour.Bianchi

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.costCoefficient_norm_oai := @OAI.PositiveEinsteinFour.Bianchi.costCoefficient_norm_oai
