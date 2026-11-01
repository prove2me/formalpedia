-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:56:19.540976+00:00
-- url     : https://prove2.me/submissions/f764cf34-a8c9-496a-89db-1250784b9b49

import Mathlib
import Definitions.Def_OAIQ091C015

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

private theorem totalPlus_entry_2_2_0_oai (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 2 0 = highest (plusCoordinates 2 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_0_oai := @OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_0_oai
