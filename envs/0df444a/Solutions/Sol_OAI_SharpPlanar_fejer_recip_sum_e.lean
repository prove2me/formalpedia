-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_recip_sum_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:08:35.97049+00:00
-- url     : https://prove2.me/submissions/779f3b2a-0dcb-41de-ad45-d5fca5c5b0f5

import Mathlib
import Theorems.Thm_OAI_SharpPlanar_fejer_recip_telescope_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma fejer_recip_sum_e_oai (m : ℕ) :
    (∑ a ∈ Finset.Icc 1 m, (2:ℝ)/(4*(a:ℝ)^2-1)) = 1-1/(2*(m:ℝ)+1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih,
      fejer_recip_telescope_e (m+1) (by omega)]
    push_cast
    have he : 2*((m:ℝ)+1)-1=2*(m:ℝ)+1 := by ring
    rw [he]
    ring

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_recip_sum_e_oai := @OAI.SharpPlanar.fejer_recip_sum_e_oai
