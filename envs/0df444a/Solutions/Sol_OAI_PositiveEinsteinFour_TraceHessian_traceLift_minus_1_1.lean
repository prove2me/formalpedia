-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:08:49.972213+00:00
-- url     : https://prove2.me/submissions/af78eea9-dda2-4229-8348-8092fd11bb44

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

private theorem traceLift_minus_1_1_oai (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 1 (traceLift M) 1 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_1_oai := @OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_1_oai
