-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.totalMinus_highest
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:47:25.361249+00:00
-- url     : https://prove2.me/submissions/f5ad3142-2572-4952-9a25-6c091d9eb912

import Mathlib
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_0_3_2
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_2_2_0
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_2_2_1
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_2_2_2
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_2_2_3
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_2_3_0
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_2_3_1
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_2_3_2
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_2_3_3

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinusCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate action of the three total minus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem totalMinus_entry_0_0_0 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 0 0 = highest (minusCoordinates 0 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_0_1 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 0 1 = highest (minusCoordinates 0 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_0_2 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 0 2 = highest (minusCoordinates 0 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_0_3 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 0 3 = highest (minusCoordinates 0 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_1_0 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 1 0 = highest (minusCoordinates 0 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_1_1 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 1 1 = highest (minusCoordinates 0 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_1_2 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 1 2 = highest (minusCoordinates 0 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_1_3 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 1 3 = highest (minusCoordinates 0 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_2_0 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 2 0 = highest (minusCoordinates 0 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_2_1 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 2 1 = highest (minusCoordinates 0 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_2_2 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 2 2 = highest (minusCoordinates 0 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_2_3 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 2 3 = highest (minusCoordinates 0 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_3_0 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 3 0 = highest (minusCoordinates 0 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_3_1 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 3 1 = highest (minusCoordinates 0 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_3_3 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 3 3 = highest (minusCoordinates 0 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_0_0 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 0 0 = highest (minusCoordinates 1 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_0_1 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 0 1 = highest (minusCoordinates 1 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_0_2 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 0 2 = highest (minusCoordinates 1 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_0_3 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 0 3 = highest (minusCoordinates 1 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_1_0 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 1 0 = highest (minusCoordinates 1 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_1_1 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 1 1 = highest (minusCoordinates 1 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_1_2 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 1 2 = highest (minusCoordinates 1 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_1_3 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 1 3 = highest (minusCoordinates 1 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_2_0 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 2 0 = highest (minusCoordinates 1 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_2_1 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 2 1 = highest (minusCoordinates 1 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_2_2 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 2 2 = highest (minusCoordinates 1 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_2_3 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 2 3 = highest (minusCoordinates 1 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_3_0 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 3 0 = highest (minusCoordinates 1 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_3_1 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 3 1 = highest (minusCoordinates 1 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_3_2 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 3 2 = highest (minusCoordinates 1 c) 3 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_3_3 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 3 3 = highest (minusCoordinates 1 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_0_0 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 0 0 = highest (minusCoordinates 2 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_0_1 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 0 1 = highest (minusCoordinates 2 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_0_2 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 0 2 = highest (minusCoordinates 2 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_0_3 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 0 3 = highest (minusCoordinates 2 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_1_0 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 1 0 = highest (minusCoordinates 2 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_1_1 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 1 1 = highest (minusCoordinates 2 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_1_2 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 1 2 = highest (minusCoordinates 2 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_1_3 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 1 3 = highest (minusCoordinates 2 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

theorem totalMinus_highest_oai (s : Fin 3) (c : Fin 21 → ℝ) :
    totalMinus s (highest c) = highest (minusCoordinates s c) := by
  funext i j
  fin_cases s <;> fin_cases i <;> fin_cases j
  · exact totalMinus_entry_0_0_0 c
  · exact totalMinus_entry_0_0_1 c
  · exact totalMinus_entry_0_0_2 c
  · exact totalMinus_entry_0_0_3 c
  · exact totalMinus_entry_0_1_0 c
  · exact totalMinus_entry_0_1_1 c
  · exact totalMinus_entry_0_1_2 c
  · exact totalMinus_entry_0_1_3 c
  · exact totalMinus_entry_0_2_0 c
  · exact totalMinus_entry_0_2_1 c
  · exact totalMinus_entry_0_2_2 c
  · exact totalMinus_entry_0_2_3 c
  · exact totalMinus_entry_0_3_0 c
  · exact totalMinus_entry_0_3_1 c
  · exact totalMinus_entry_0_3_2 c
  · exact totalMinus_entry_0_3_3 c
  · exact totalMinus_entry_1_0_0 c
  · exact totalMinus_entry_1_0_1 c
  · exact totalMinus_entry_1_0_2 c
  · exact totalMinus_entry_1_0_3 c
  · exact totalMinus_entry_1_1_0 c
  · exact totalMinus_entry_1_1_1 c
  · exact totalMinus_entry_1_1_2 c
  · exact totalMinus_entry_1_1_3 c
  · exact totalMinus_entry_1_2_0 c
  · exact totalMinus_entry_1_2_1 c
  · exact totalMinus_entry_1_2_2 c
  · exact totalMinus_entry_1_2_3 c
  · exact totalMinus_entry_1_3_0 c
  · exact totalMinus_entry_1_3_1 c
  · exact totalMinus_entry_1_3_2 c
  · exact totalMinus_entry_1_3_3 c
  · exact totalMinus_entry_2_0_0 c
  · exact totalMinus_entry_2_0_1 c
  · exact totalMinus_entry_2_0_2 c
  · exact totalMinus_entry_2_0_3 c
  · exact totalMinus_entry_2_1_0 c
  · exact totalMinus_entry_2_1_1 c
  · exact totalMinus_entry_2_1_2 c
  · exact totalMinus_entry_2_1_3 c
  · exact totalMinus_entry_2_2_0 c
  · exact totalMinus_entry_2_2_1 c
  · exact totalMinus_entry_2_2_2 c
  · exact totalMinus_entry_2_2_3 c
  · exact totalMinus_entry_2_3_0 c
  · exact totalMinus_entry_2_3_1 c
  · exact totalMinus_entry_2_3_2 c
  · exact totalMinus_entry_2_3_3 c


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.totalMinus_highest_oai := @OAI.PositiveEinsteinFour.HighestHessian.totalMinus_highest_oai
