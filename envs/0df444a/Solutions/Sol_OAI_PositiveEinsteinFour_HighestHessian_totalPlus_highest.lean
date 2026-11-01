-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.totalPlus_highest
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:49:40.576633+00:00
-- url     : https://prove2.me/submissions/96663b99-0bf4-418d-9317-3eb6e7401630

import Mathlib
import Definitions.Def_OAIQ091C015
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_1_3_1
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_1_0
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_1_1
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_1_2
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_1_3
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_2_0
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_2_1
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_2_2
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_2_3
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_3_0
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_3_1
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_3_2
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_entry_2_3_3

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestActionCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate action of the three total plus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem totalPlus_entry_0_0_0 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 0 0 = highest (plusCoordinates 0 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_0_1 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 0 1 = highest (plusCoordinates 0 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_0_2 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 0 2 = highest (plusCoordinates 0 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_0_3 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 0 3 = highest (plusCoordinates 0 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_1_0 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 1 0 = highest (plusCoordinates 0 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_1_1 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 1 1 = highest (plusCoordinates 0 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_1_2 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 1 2 = highest (plusCoordinates 0 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_1_3 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 1 3 = highest (plusCoordinates 0 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_2_0 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 2 0 = highest (plusCoordinates 0 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_2_1 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 2 1 = highest (plusCoordinates 0 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_2_2 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 2 2 = highest (plusCoordinates 0 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_2_3 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 2 3 = highest (plusCoordinates 0 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_3_0 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 3 0 = highest (plusCoordinates 0 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_3_1 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 3 1 = highest (plusCoordinates 0 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_3_2 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 3 2 = highest (plusCoordinates 0 c) 3 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_3_3 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 3 3 = highest (plusCoordinates 0 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_0_0 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 0 0 = highest (plusCoordinates 1 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_0_1 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 0 1 = highest (plusCoordinates 1 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_0_2 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 0 2 = highest (plusCoordinates 1 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_0_3 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 0 3 = highest (plusCoordinates 1 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_1_0 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 1 0 = highest (plusCoordinates 1 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_1_1 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 1 1 = highest (plusCoordinates 1 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_1_2 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 1 2 = highest (plusCoordinates 1 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_1_3 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 1 3 = highest (plusCoordinates 1 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_2_0 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 2 0 = highest (plusCoordinates 1 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_2_1 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 2 1 = highest (plusCoordinates 1 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_2_2 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 2 2 = highest (plusCoordinates 1 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_2_3 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 2 3 = highest (plusCoordinates 1 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_3_0 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 3 0 = highest (plusCoordinates 1 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_3_2 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 3 2 = highest (plusCoordinates 1 c) 3 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_3_3 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 3 3 = highest (plusCoordinates 1 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_0_0 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 0 0 = highest (plusCoordinates 2 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_0_1 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 0 1 = highest (plusCoordinates 2 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_0_2 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 0 2 = highest (plusCoordinates 2 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_0_3 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 0 3 = highest (plusCoordinates 2 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

/-- The total plus rotation preserves the explicit constrained space. -/
theorem totalPlus_highest_oai (s : Fin 3) (c : Fin 21 → ℝ) :
    totalPlus s (highest c) = highest (plusCoordinates s c) := by
  funext i j
  fin_cases s <;> fin_cases i <;> fin_cases j
  · exact totalPlus_entry_0_0_0 c
  · exact totalPlus_entry_0_0_1 c
  · exact totalPlus_entry_0_0_2 c
  · exact totalPlus_entry_0_0_3 c
  · exact totalPlus_entry_0_1_0 c
  · exact totalPlus_entry_0_1_1 c
  · exact totalPlus_entry_0_1_2 c
  · exact totalPlus_entry_0_1_3 c
  · exact totalPlus_entry_0_2_0 c
  · exact totalPlus_entry_0_2_1 c
  · exact totalPlus_entry_0_2_2 c
  · exact totalPlus_entry_0_2_3 c
  · exact totalPlus_entry_0_3_0 c
  · exact totalPlus_entry_0_3_1 c
  · exact totalPlus_entry_0_3_2 c
  · exact totalPlus_entry_0_3_3 c
  · exact totalPlus_entry_1_0_0 c
  · exact totalPlus_entry_1_0_1 c
  · exact totalPlus_entry_1_0_2 c
  · exact totalPlus_entry_1_0_3 c
  · exact totalPlus_entry_1_1_0 c
  · exact totalPlus_entry_1_1_1 c
  · exact totalPlus_entry_1_1_2 c
  · exact totalPlus_entry_1_1_3 c
  · exact totalPlus_entry_1_2_0 c
  · exact totalPlus_entry_1_2_1 c
  · exact totalPlus_entry_1_2_2 c
  · exact totalPlus_entry_1_2_3 c
  · exact totalPlus_entry_1_3_0 c
  · exact totalPlus_entry_1_3_1 c
  · exact totalPlus_entry_1_3_2 c
  · exact totalPlus_entry_1_3_3 c
  · exact totalPlus_entry_2_0_0 c
  · exact totalPlus_entry_2_0_1 c
  · exact totalPlus_entry_2_0_2 c
  · exact totalPlus_entry_2_0_3 c
  · exact totalPlus_entry_2_1_0 c
  · exact totalPlus_entry_2_1_1 c
  · exact totalPlus_entry_2_1_2 c
  · exact totalPlus_entry_2_1_3 c
  · exact totalPlus_entry_2_2_0 c
  · exact totalPlus_entry_2_2_1 c
  · exact totalPlus_entry_2_2_2 c
  · exact totalPlus_entry_2_2_3 c
  · exact totalPlus_entry_2_3_0 c
  · exact totalPlus_entry_2_3_1 c
  · exact totalPlus_entry_2_3_2 c
  · exact totalPlus_entry_2_3_3 c


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.totalPlus_highest_oai := @OAI.PositiveEinsteinFour.HighestHessian.totalPlus_highest_oai
