-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:54:32.959988+00:00
-- url     : https://prove2.me/submissions/22cdf04e-2846-4fe1-9773-6101e972e7b9

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

private theorem totalPlus_entry_2_1_1_oai (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 1 1 = highest (plusCoordinates 2 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_1_oai := @OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_1_oai
