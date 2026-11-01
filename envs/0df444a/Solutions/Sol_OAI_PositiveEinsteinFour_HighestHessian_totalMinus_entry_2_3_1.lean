-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:05:23.930817+00:00
-- url     : https://prove2.me/submissions/a0bc5f47-15cf-42b7-93ed-0728815c0872

import Mathlib
import Definitions.Def_OAIQ091C018

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

private theorem totalMinus_entry_2_3_1_oai (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 3 1 = highest (minusCoordinates 2 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_1_oai := @OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_1_oai
