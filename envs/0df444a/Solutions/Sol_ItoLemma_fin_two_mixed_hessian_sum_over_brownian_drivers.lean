-- Prove2me | solution 1 for ItoLemma.fin_two_mixed_hessian_sum_over_brownian_drivers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:45:54.680935+00:00
-- url     : https://prove2.me/submissions/adf99a55-cb44-4cbd-a7bf-c7204c58c3a2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The mixed Hessian term collapses to the quadratic-covariation
sum over all Brownian driving coordinates. -/
theorem solution {d : ℕ} (H : Fin 2 → Fin d → ℝ) :
    (1 / 2 : ℝ) *
      (∑ p : Fin 2, ∑ q : Fin 2,
        (if p = q then (0 : ℝ) else 1) *
          (∑ k : Fin d, H p k * H q k)) =
      ∑ k : Fin d, H 0 k * H 1 k := by
  have hswap : (∑ k : Fin d, H 1 k * H 0 k) =
      ∑ k : Fin d, H 0 k * H 1 k := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp [Fin.sum_univ_two, hswap]
  ring
