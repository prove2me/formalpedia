-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:12:39.517152+00:00
-- url     : https://prove2.me/submissions/99e59f40-0ebc-4edd-80a9-60d14efae648

import Mathlib
import Definitions.Def_OAIQ091C035
import Definitions.Def_OAIQ091C007
import Definitions.Def_OAIQ091C012

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeneralMatrixCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3
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

private theorem costParameters_matrix_eq_0_0 (v : Fin 3 → Vec) :
    (costParameters v).matrix 0 0 = costMatrix v 0 0 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_0_1 (v : Fin 3 → Vec) :
    (costParameters v).matrix 0 1 = costMatrix v 0 1 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]

private theorem costParameters_matrix_eq_0_2 (v : Fin 3 → Vec) :
    (costParameters v).matrix 0 2 = costMatrix v 0 2 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_1_0 (v : Fin 3 → Vec) :
    (costParameters v).matrix 1 0 = costMatrix v 1 0 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]

private theorem costParameters_matrix_eq_1_1 (v : Fin 3 → Vec) :
    (costParameters v).matrix 1 1 = costMatrix v 1 1 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals exact Or.inl (by norm_num)

private theorem costParameters_matrix_eq_1_2 (v : Fin 3 → Vec) :
    (costParameters v).matrix 1 2 = costMatrix v 1 2 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_2_0 (v : Fin 3 → Vec) :
    (costParameters v).matrix 2 0 = costMatrix v 2 0 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_2_1 (v : Fin 3 → Vec) :
    (costParameters v).matrix 2 1 = costMatrix v 2 1 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_2_2 (v : Fin 3 → Vec) :
    (costParameters v).matrix 2 2 = costMatrix v 2 2 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]

private theorem costParameters_matrix_eq (v : Fin 3 → Vec) :
    (costParameters v).matrix = costMatrix v := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact costParameters_matrix_eq_0_0 v
  · exact costParameters_matrix_eq_0_1 v
  · exact costParameters_matrix_eq_0_2 v
  · exact costParameters_matrix_eq_1_0 v
  · exact costParameters_matrix_eq_1_1 v
  · exact costParameters_matrix_eq_1_2 v
  · exact costParameters_matrix_eq_2_0 v
  · exact costParameters_matrix_eq_2_1 v
  · exact costParameters_matrix_eq_2_2 v


private theorem coupling_matrix_coordinates_2_0_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_0_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_0_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_0_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_0_oai
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_2_0_0 a b c d e v
  · exact coupling_matrix_coordinates_2_0_1 a b c d e v
  · exact coupling_matrix_coordinates_2_0_2 a b c d e v
  · exact coupling_matrix_coordinates_2_0_3 a b c d e v

end
end PositiveEinsteinFour.Bianchi

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_0_oai := @OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_0_oai
