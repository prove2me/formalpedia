-- Prove2me | solution 1 for OAI.SharpPlanar.transformedIntegrand_analytic_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:26:50.719195+00:00
-- url     : https://prove2.me/submissions/78e4ad68-0311-4aff-9b3e-f2a257947045

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_complexTransformedFactor_differentiableAt_g
import Theorems.Thm_OAI_SharpPlanar_diskAffine_mem_g
import Theorems.Thm_OAI_SharpPlanar_disk_denominator_ne_g

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

lemma transformedIntegrand_analytic_g_oai (c d : ℕ → ℝ) {j : ℕ} (hj : j < 6) (m y : ℝ) (ell : ℕ) :
    DiffContOnCl ℂ (fun w => finiteDensity c d j (diskAffine j w) *
      complexTransformedFactor m y ell (diskAffine j w)) (Metric.ball 0 2) := by
  apply DifferentiableOn.diffContOnCl
  intro w hw
  have hw' : ‖w‖ ≤ 2 := by
    rw [closure_ball (0:ℂ) (by norm_num : (2:ℝ) ≠ 0),Metric.mem_closedBall,dist_zero_right] at hw
    exact hw
  have ht := disk_denominator_ne_g hj (diskAffine_mem_g hw')
  have hA : DifferentiableAt ℂ (diskAffine j) w := by unfold diskAffine; fun_prop
  exact (((finiteDensity_differentiable c d j).differentiableAt.comp w hA).mul
    ((complexTransformedFactor_differentiableAt_g ht m y ell).comp w hA)).differentiableWithinAt

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.transformedIntegrand_analytic_g_oai := @OAI.SharpPlanar.transformedIntegrand_analytic_g_oai
