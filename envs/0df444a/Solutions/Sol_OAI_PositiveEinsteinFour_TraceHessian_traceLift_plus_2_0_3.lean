-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:28:21.397193+00:00
-- url     : https://prove2.me/submissions/2daa69f1-2cbc-4841-8d05-cea91cf01872

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

private theorem traceLift_plus_2_0_3_oai (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 0 3 a b =
      traceLift (matrixAction 2 M) 0 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0_3_oai := @OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0_3_oai
