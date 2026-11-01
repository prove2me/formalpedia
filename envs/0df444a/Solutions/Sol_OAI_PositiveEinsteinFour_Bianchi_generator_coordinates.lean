-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.generator_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T18:50:13.654699+00:00
-- url     : https://prove2.me/submissions/21aca1e5-f3c7-4ccf-8cc4-e72e5e7ad511

import Mathlib
import Definitions.Def_OAIQ091C007
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_coordinates_2_1
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_coordinates_2_2

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

private theorem generator_coordinates_0_0 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 0 (costParameters v).matrix 0 b =
      (costParameters (generatorCoordinates 0 v)).matrix 0 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, TraceHessian.rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_0_1 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 0 (costParameters v).matrix 1 b =
      (costParameters (generatorCoordinates 0 v)).matrix 1 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, TraceHessian.rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_0_2 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 0 (costParameters v).matrix 2 b =
      (costParameters (generatorCoordinates 0 v)).matrix 2 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, TraceHessian.rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_1_0 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 1 (costParameters v).matrix 0 b =
      (costParameters (generatorCoordinates 1 v)).matrix 0 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, TraceHessian.rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_1_1 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 1 (costParameters v).matrix 1 b =
      (costParameters (generatorCoordinates 1 v)).matrix 1 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, TraceHessian.rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_1_2 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 1 (costParameters v).matrix 2 b =
      (costParameters (generatorCoordinates 1 v)).matrix 2 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, TraceHessian.rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem generator_coordinates_2_0 (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 2 (costParameters v).matrix 0 b =
      (costParameters (generatorCoordinates 2 v)).matrix 0 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, TraceHessian.rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

/-- Exact generator action in the fixed Bianchi coordinate frame. -/
theorem generator_coordinates_oai (s : Fin 3) (v : Fin 3 → Vec) :
    rawGradientGenerator s (costParameters v).matrix =
      (costParameters (generatorCoordinates s v)).matrix := by
  funext a b
  fin_cases s <;> fin_cases a
  · exact generator_coordinates_0_0 v b
  · exact generator_coordinates_0_1 v b
  · exact generator_coordinates_0_2 v b
  · exact generator_coordinates_1_0 v b
  · exact generator_coordinates_1_1 v b
  · exact generator_coordinates_1_2 v b
  · exact generator_coordinates_2_0 v b
  · exact generator_coordinates_2_1 v b
  · exact generator_coordinates_2_2 v b

end
end PositiveEinsteinFour.Bianchi

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.generator_coordinates_oai := @OAI.PositiveEinsteinFour.Bianchi.generator_coordinates_oai
