-- Prove2me | solution 1 for OAI.SharpPlanar.complexLambda_differentiableAt_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:13:05.395941+00:00
-- url     : https://prove2.me/submissions/6839a81c-d032-4aa3-a39b-0a13047dd23f

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_b_pos_g

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

lemma complexLambda_differentiableAt_g_oai {t : ℂ} (ht : t+Complex.I*(h:ℂ) ≠ 0) :
    DifferentiableAt ℂ complexLambda t := by
  unfold complexLambda
  fun_prop (disch := exact mul_ne_zero (Complex.ofReal_ne_zero.mpr b_pos_g.ne') ht)

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexLambda_differentiableAt_g_oai := @OAI.SharpPlanar.complexLambda_differentiableAt_g_oai
