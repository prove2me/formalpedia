-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.generator_coordinates_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:16:03.28084+00:00
-- url     : https://prove2.me/submissions/34e078b7-14bb-46f4-b9fc-70c0a1140001

import Mathlib
import Definitions.Def_OAIQ091C007

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCoordinateModel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed twelve real coordinates for the inner generators in the cost calculation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian
set_option maxHeartbeats 1000000

private theorem generator_coordinates_2_1_oai (v : Fin 3 → Vec) (b : Fin 3) :
    rawGradientGenerator 2 (costParameters v).matrix 1 b =
      (costParameters (generatorCoordinates 2 v)).matrix 1 b := by
  ext j
  fin_cases b <;> fin_cases j <;>
    simp [rawGradientGenerator, rawMatrixRotation, costParameters, parameters,
      costShape, Tensor.matrix, generatorCoordinates, generatorCoefficients,
      difference, next, previous, TraceHessian.rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.generator_coordinates_2_1_oai := @OAI.PositiveEinsteinFour.Bianchi.generator_coordinates_2_1_oai
