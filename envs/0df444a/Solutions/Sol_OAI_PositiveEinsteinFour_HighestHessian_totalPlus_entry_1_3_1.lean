-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_1_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:51:33.856004+00:00
-- url     : https://prove2.me/submissions/d3cfcbd9-e53c-4bdb-8d37-022f75660260

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

private theorem totalPlus_entry_1_3_1_oai (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 3 1 = highest (plusCoordinates 1 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates] <;> ring)


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_1_3_1_oai := @OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_1_3_1_oai
