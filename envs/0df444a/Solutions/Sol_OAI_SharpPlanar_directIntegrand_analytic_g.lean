-- Prove2me | solution 1 for OAI.SharpPlanar.directIntegrand_analytic_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:14:58.177288+00:00
-- url     : https://prove2.me/submissions/d7e5ec4d-75de-45ab-a468-afe77ba0a8ce

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G1643

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

lemma finiteDensity_differentiable (c d : ℕ → ℝ) (j : ℕ) :
    Differentiable ℂ (finiteDensity c d j) := by
  unfold finiteDensity complexU complexV
  fun_prop
lemma complexDirectFactor_differentiable (m y : ℝ) (ell : ℕ) :
    Differentiable ℂ (complexDirectFactor m y ell) := by
  unfold complexDirectFactor
  fun_prop

lemma directIntegrand_analytic_g_oai (c d : ℕ → ℝ) (j : ℕ) (m y : ℝ) (ell : ℕ) :
    DiffContOnCl ℂ (fun w => finiteDensity c d j (diskAffine j w) *
      complexDirectFactor m y ell (diskAffine j w)) (Metric.ball 0 2) := by
  apply Differentiable.diffContOnCl
  have hA : Differentiable ℂ (diskAffine j) := by unfold diskAffine; fun_prop
  exact ((finiteDensity_differentiable c d j).comp hA).mul
    ((complexDirectFactor_differentiable m y ell).comp hA)

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.directIntegrand_analytic_g_oai := @OAI.SharpPlanar.directIntegrand_analytic_g_oai
