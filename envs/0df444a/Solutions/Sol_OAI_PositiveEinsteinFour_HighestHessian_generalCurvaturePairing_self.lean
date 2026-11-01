-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_self
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:40:09.820876+00:00
-- url     : https://prove2.me/submissions/33d2ada8-3e50-400a-a9d5-41d892108fad

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C015

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The exact prescribed trace in arbitrary matrix coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

theorem generalCurvaturePairing_self_oai (A U : Mat) (X : Hessian) :
    generalCurvaturePairing A U X X = generalCasimirCurvatureForm A U X := by
  simp only [generalCurvaturePairing, generalCasimirCurvatureForm,
    hessianGram, hessianPairing_self]

end
end PositiveEinsteinFour.HighestHessian
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_self_oai := @OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_self_oai
