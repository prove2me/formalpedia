-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_comm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:38:16.969336+00:00
-- url     : https://prove2.me/submissions/bc18944d-c941-473d-ac87-d2e48542cf01

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C015

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceAdjoint
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit trace lift is the actual adjoint on the Bianchi subspace. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

theorem hessianPairing_comm (X Y : Hessian) :
    hessianPairing X Y = hessianPairing Y X := by
  simp only [hessianPairing, mul_comm]

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

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

private theorem weightedPairing_comm (A : Mat) (hA : symmetric A)
    (F G : Fin 3 → Hessian) :
    (∑ r, ∑ s, A r s * hessianPairing (F r) (G s)) =
      ∑ r, ∑ s, A r s * hessianPairing (G r) (F s) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hA s r, hessianPairing_comm]

theorem generalCurvaturePairing_comm_oai (A U : Mat) (hA : symmetric A) (hU : symmetric U)
    (X Y : Hessian) :
    generalCurvaturePairing A U X Y = generalCurvaturePairing A U Y X := by
  rw [generalCurvaturePairing, generalCurvaturePairing, hessianPairing_comm X Y,
    weightedPairing_comm A hA, weightedPairing_comm U hU]

end
end PositiveEinsteinFour.HighestHessian
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_comm_oai := @OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_comm_oai
