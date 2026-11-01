-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.generator_norm_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T18:53:20.955277+00:00
-- url     : https://prove2.me/submissions/f55df884-8bcf-4d99-8f59-3f915ab2e71f

import Mathlib
import Definitions.Def_OAIQ091C007

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCoordinateModel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix
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

theorem generator_norm_2_oai (v : Fin 3 → Vec) :
    coordinateNorm (generatorCoordinates 2 v) =
      10 * ‖v 0‖ ^ 2 + 670 * ‖v 1‖ ^ 2 + 70 * ‖v 2‖ ^ 2 +
      (0) * inner ℝ (v 0) (v 1) + (0) * inner ℝ (v 0) (v 2) +
      (160) * inner ℝ (v 1) (v 2) := by
  simp [coordinateNorm, generatorCoordinates, generatorCoefficients, quaternion,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.generator_norm_2_oai := @OAI.PositiveEinsteinFour.Bianchi.generator_norm_2_oai
