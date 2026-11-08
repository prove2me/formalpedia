-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_recip_sum_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:07.603794+00:00
-- url     : https://prove2.me/submissions/a1f3e637-7b49-426f-b4c1-7c78ab45dccf

import Mathlib
import Theorems.Thm_OAI_SharpPlanar_fejer_recip_telescope_g

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

lemma fejer_recip_sum_g_oai (m : ℕ) :
    (∑ a ∈ Finset.Icc 1 m, (2:ℝ)/(4*(a:ℝ)^2-1)) = 1-1/(2*(m:ℝ)+1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih,
      fejer_recip_telescope_g (m+1) (by omega)]
    push_cast
    have he : 2*((m:ℝ)+1)-1=2*(m:ℝ)+1 := by ring
    rw [he]
    ring

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_recip_sum_g_oai := @OAI.SharpPlanar.fejer_recip_sum_g_oai
