-- Prove2me | solution 1 for OAI.SharpPlanar.complexTransformedFactor_differentiableAt_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:13:19.292335+00:00
-- url     : https://prove2.me/submissions/98ce56e4-fb6d-4b8e-a4c2-c531391c4444

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_complexLambda_differentiableAt_g

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
lemma complexTransformedFactor_differentiableAt_g_oai {t : ℂ}
    (ht : t+Complex.I*(h:ℂ) ≠ 0) (m y : ℝ) (ell : ℕ) :
    DifferentiableAt ℂ (complexTransformedFactor m y ell) t := by
  have hL := complexLambda_differentiableAt_g ht
  have hZ := complexZ_differentiableAt ht
  unfold complexTransformedFactor
  fun_prop

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexTransformedFactor_differentiableAt_g_oai := @OAI.SharpPlanar.complexTransformedFactor_differentiableAt_g_oai
