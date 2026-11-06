-- Prove2me | solution 1 for OAI.SharpPlanar.complexLambda_differentiableAt_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:32:18.047197+00:00
-- url     : https://prove2.me/submissions/a16f4d0f-6c86-4aee-9f9d-d48322ba51b5

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_b_pos_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory Set

lemma complexLambda_differentiableAt_e_oai {t : ℂ} (ht : t+Complex.I*(h:ℂ) ≠ 0) :
    DifferentiableAt ℂ complexLambda t := by
  unfold complexLambda
  fun_prop (disch := exact mul_ne_zero (Complex.ofReal_ne_zero.mpr b_pos_e.ne') ht)

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexLambda_differentiableAt_e_oai := @OAI.SharpPlanar.complexLambda_differentiableAt_e_oai
