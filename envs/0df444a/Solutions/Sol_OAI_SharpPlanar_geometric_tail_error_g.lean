-- Prove2me | solution 1 for OAI.SharpPlanar.geometric_tail_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:25.188368+00:00
-- url     : https://prove2.me/submissions/a38d54c2-d85f-451a-bbd2-d59ed7df7633

import Mathlib

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

lemma geometric_tail_error_g_oai {a : ℕ → ℂ} {v : ℂ} {M r : ℝ}
    (ha : HasSum a v) (hr0 : 0 ≤ r) (hr : r < 1)
    (hb : ∀ n, ‖a n‖ ≤ M*r^n) (N : ℕ) :
    ‖v-∑ n ∈ Finset.range N, a n‖ ≤ M*r^N/(1-r) := by
  have hsum := ha.summable.sum_add_tsum_nat_add N
  rw [ha.tsum_eq] at hsum
  have he : v-∑ n ∈ Finset.range N, a n = ∑' n, a (n+N) := by
    rw [← hsum]
    abel
  rw [he]
  have hg : HasSum (fun n : ℕ => M*r^N*r^n) (M*r^N/(1-r)) :=
    (hasSum_geometric_of_lt_one hr0 hr).mul_left (M*r^N)
  apply tsum_of_norm_bounded hg
  intro n
  calc
    ‖a (n+N)‖ ≤ M*r^(n+N) := hb _
    _ = M*r^N*r^n := by rw [pow_add]; ring

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.geometric_tail_error_g_oai := @OAI.SharpPlanar.geometric_tail_error_g_oai
