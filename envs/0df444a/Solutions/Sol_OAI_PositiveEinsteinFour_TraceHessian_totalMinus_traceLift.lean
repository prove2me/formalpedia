-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:51:32.731223+00:00
-- url     : https://prove2.me/submissions/612d6e58-57be-415c-9ac6-3c1339f5fd0d

import Mathlib
import Definitions.Def_OAIQ091C015
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_0_2
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_0_3
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_1_0
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_1_1
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_1_2
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_1_3
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_2_0
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_2_1
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_2_2
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_2_3

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceActionIntertwining
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
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

private theorem traceLift_minus_0_0 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 0 (traceLift M) 0 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_0_1 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 0 (traceLift M) 1 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

/-- The minus tensor action on the explicit restricted trace adjoint. -/
theorem totalMinus_traceLift_oai (s : Fin 3) (M : Mat) :
    totalMinus s (traceLift M) = 0 := by
  funext i j a b
  fin_cases s <;> fin_cases i
  · exact traceLift_minus_0_0 M j a b
  · exact traceLift_minus_0_1 M j a b
  · exact traceLift_minus_0_2 M j a b
  · exact traceLift_minus_0_3 M j a b
  · exact traceLift_minus_1_0 M j a b
  · exact traceLift_minus_1_1 M j a b
  · exact traceLift_minus_1_2 M j a b
  · exact traceLift_minus_1_3 M j a b
  · exact traceLift_minus_2_0 M j a b
  · exact traceLift_minus_2_1 M j a b
  · exact traceLift_minus_2_2 M j a b
  · exact traceLift_minus_2_3 M j a b

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift_oai := @OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift_oai
