-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:14:35.600325+00:00
-- url     : https://prove2.me/submissions/ca5278a5-cecb-4488-82bd-674fe4227703

import Mathlib
import Definitions.Def_OAIQ091C015
import Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_0_0_3

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

private theorem traceLift_plus_0_0_0 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 0 0 a b =
      traceLift (matrixAction 0 M) 0 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_0_1 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 0 1 a b =
      traceLift (matrixAction 0 M) 0 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_0_2 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 0 2 a b =
      traceLift (matrixAction 0 M) 0 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_0_oai (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 0 j a b = traceLift (matrixAction 0 M) 0 j a b := by
  fin_cases j
  · exact traceLift_plus_0_0_0 M a b
  · exact traceLift_plus_0_0_1 M a b
  · exact traceLift_plus_0_0_2 M a b
  · exact traceLift_plus_0_0_3 M a b

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_0_oai := @OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_0_oai
