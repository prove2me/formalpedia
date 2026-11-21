-- Prove2me | solution 1 for NymanBeurling.damped_moebius_truncation_mean_square_convergence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T04:06:18.581722+00:00
-- url     : https://prove2.me/submissions/2ad62fa0-e6bc-4778-97d5-a4fe5c309886
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_moebius_polynomial_critical_strip_bound
import Theorems.Thm_NymanBeurling_damped_mellin_completion_of_polynomial_bound

set_option autoImplicit false
open scoped BigOperators

theorem solution
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
      (∑ n ∈ Finset.range H,
        (NymanBeurling.dampedResidualFinite N ε (n+1) -
          NymanBeurling.dampedResidualProfile ε (n+1))^2 /
            ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by
  exact (NymanBeurling.damped_mellin_completion_of_polynomial_bound
    NymanBeurling.moebius_polynomial_critical_strip_bound).1 ε hε hεhalf δ hδ
