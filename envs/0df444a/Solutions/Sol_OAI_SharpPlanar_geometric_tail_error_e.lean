-- Prove2me | solution 1 for OAI.SharpPlanar.geometric_tail_error_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:09:22.069958+00:00
-- url     : https://prove2.me/submissions/8bf18469-1c71-4097-9bca-4ec848666739

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

lemma geometric_tail_error_e_oai {a : ℕ → ℂ} {v : ℂ} {M r : ℝ}
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

theorem solution : type_of% @OAI.SharpPlanar.geometric_tail_error_e_oai := @OAI.SharpPlanar.geometric_tail_error_e_oai
