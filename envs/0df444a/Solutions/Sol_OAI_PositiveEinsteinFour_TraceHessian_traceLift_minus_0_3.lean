-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_0_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:08:04.130844+00:00
-- url     : https://prove2.me/submissions/25ee6064-3287-468f-9839-78d634614abf

import Mathlib
import Definitions.Def_OAIQ091C015

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

private theorem traceLift_minus_0_3_oai (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 0 (traceLift M) 3 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_0_3_oai := @OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_0_3_oai
