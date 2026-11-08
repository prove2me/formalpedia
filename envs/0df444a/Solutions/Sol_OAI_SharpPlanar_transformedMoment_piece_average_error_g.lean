-- Prove2me | solution 1 for OAI.SharpPlanar.transformedMoment_piece_average_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:28:21.114149+00:00
-- url     : https://prove2.me/submissions/97793647-681a-4780-9e61-5d757a1ff4c4

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_diskAffine_mem_g
import Theorems.Thm_OAI_SharpPlanar_fejer_analytic_average_error_g
import Theorems.Thm_OAI_SharpPlanar_transformedIntegrand_analytic_g
import Theorems.Thm_OAI_SharpPlanar_transformedIntegrand_disk_bound_g

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

lemma transformedMoment_piece_average_error_g_oai (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(1/2:ℂ)*(∫ x in (-1:ℝ)..1, finiteDensity c d j (diskAffine j x) *
        complexTransformedFactor m y ell (diskAffine j x)) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*
        (finiteDensity c d j (diskAffine j (fejerNode v.val)) *
          complexTransformedFactor m y ell (diskAffine j (fejerNode v.val)))‖ < 1/10^22 := by
  apply fejer_analytic_average_error_g _ (transformedIntegrand_analytic_g c d hj m y ell)
  intro w hw'
  apply transformedIntegrand_disk_bound_g c d hw hj (diskAffine_mem_g ?_) hm0 hm1 hy ell
  simpa only [Metric.mem_sphere,dist_zero_right] using le_of_eq hw'

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.transformedMoment_piece_average_error_g_oai := @OAI.SharpPlanar.transformedMoment_piece_average_error_g_oai
