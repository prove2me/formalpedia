-- Prove2me | solution 1 for OAI.SharpPlanar.complexTransformedFactor_differentiableAt_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:33:26.052767+00:00
-- url     : https://prove2.me/submissions/5c5b32f9-e735-4754-a731-a7e026dcd9de

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_complexLambda_differentiableAt_e

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

lemma complexZ_differentiableAt {t : ℂ} (ht : t+Complex.I*(h:ℂ) ≠ 0) :
    DifferentiableAt ℂ complexZ t := by
  unfold complexZ
  fun_prop (disch := exact ht)
lemma complexTransformedFactor_differentiableAt_e_oai {t : ℂ}
    (ht : t+Complex.I*(h:ℂ) ≠ 0) (m y : ℝ) (ell : ℕ) :
    DifferentiableAt ℂ (complexTransformedFactor m y ell) t := by
  have hL := complexLambda_differentiableAt_e ht
  have hZ := complexZ_differentiableAt ht
  unfold complexTransformedFactor
  fun_prop

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexTransformedFactor_differentiableAt_e_oai := @OAI.SharpPlanar.complexTransformedFactor_differentiableAt_e_oai
