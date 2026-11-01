-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:29:28.322207+00:00
-- url     : https://prove2.me/submissions/bab8fa59-defb-4838-aeb7-cb116a840d7b

import Mathlib
import Definitions.Def_OAIQ091C015
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_2_1_3

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

private theorem traceLift_plus_2_1_0 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 1 0 a b =
      traceLift (matrixAction 2 M) 1 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_1_1 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 1 1 a b =
      traceLift (matrixAction 2 M) 1 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_1_2 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 1 2 a b =
      traceLift (matrixAction 2 M) 1 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_1_oai (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 1 j a b = traceLift (matrixAction 2 M) 1 j a b := by
  fin_cases j
  · exact traceLift_plus_2_1_0 M a b
  · exact traceLift_plus_2_1_1 M a b
  · exact traceLift_plus_2_1_2 M a b
  · exact traceLift_plus_2_1_3 M a b

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_1_oai := @OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_1_oai
