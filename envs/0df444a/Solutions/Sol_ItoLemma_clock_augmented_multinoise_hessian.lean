-- Prove2me | solution 1 for ItoLemma.clock_augmented_multinoise_hessian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:34:23.931483+00:00
-- url     : https://prove2.me/submissions/7dc6f5f2-ae5f-49c4-85e7-ee72469bf45d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- The clock coordinate has zero diffusion under every Brownian driver.
Only the spatial-spatial Hessian entry survives the covariance contraction. -/

theorem solution
    {d : ℕ} (hessian : Fin 2 → Fin 2 → ℝ) (diffusion : Fin d → ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      hessian i j *
        (∑ k : Fin d,
          (if i = 0 then (0 : ℝ) else diffusion k) *
            (if j = 0 then (0 : ℝ) else diffusion k))) =
      hessian 1 1 * (∑ k : Fin d, diffusion k * diffusion k) := by
  simp [Fin.sum_univ_two]
