-- Prove2me | solution 1 for MarginalUtility.marginalUtility_eq_limit_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:21:35.355238+00:00
-- url     : https://prove2.me/submissions/84ab24d6-29f9-46e2-be42-6d4f952ba10a

import Mathlib
import Definitions.Def_MarginalUtility_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set

open MarginalUtility

theorem solution (U : ℝ → ℝ) (g : ℝ)
    (hU : DifferentiableAt ℝ U g) :
    Tendsto (fun Δg : ℝ => utilityChange U g (g + Δg) / Δg) (𝓝[≠] 0)
      (𝓝 (marginalUtility U g)) := by
  -- Checkpoint: DIRECT_CANDIDATE.
  -- Mathematical route: differentiability at `g` yields `HasDerivAt U (deriv U g) g`
  -- (exact signature at pinned revision confirmed by signature probe). The slope-limit
  -- characterization of `HasDerivAt` states that `fun t => t⁻¹ • (f (x + t) - f x)`
  -- tends to `f'` in `nhdsWithin 0 {0}ᶜ`. For scalar `ℝ`-action this is exactly the
  -- quotient `(U (g + t) - U g) / t` with the two factors in the opposite order,
  -- so transporting `Tendsto` through that pointwise equality closes the goal.
  have heq :
      (fun Δg : ℝ => utilityChange U g (g + Δg) / Δg)
        = fun t : ℝ => t⁻¹ • (U (g + t) - U g) := by
    funext Δg
    show (U (g + Δg) - U g) / Δg = _
    rw [div_eq_mul_inv, smul_eq_mul]
    exact mul_comm _ _
  have h : Tendsto (fun t : ℝ => t⁻¹ • (U (g + t) - U g)) (𝓝[≠] 0)
      (𝓝 (marginalUtility U g)) := hU.hasDerivAt.tendsto_slope_zero
  rw [heq]
  exact h
