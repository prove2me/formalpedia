-- Prove2me | solution 1 for MarginalUtility.utility_monotone_of_marginal_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T21:14:49.371327+00:00
-- url     : https://prove2.me/submissions/50a0f89e-24ca-40ae-b93a-05d6e2af216f

import Mathlib
import Definitions.Def_MarginalUtility_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set

open MarginalUtility

theorem solution (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : DifferentiableOn ℝ U D) :
    ((∀ g ∈ D, 0 < marginalUtility U g) → StrictMonoOn U D) ∧
      ((∀ g ∈ D, marginalUtility U g < 0) → StrictAntiOn U D) := by
  -- Checkpoint: DIRECT_CANDIDATE.
  -- Mathematical route: `marginalUtility U g` is definitionally `deriv U g`.
  -- Mathlib's `strictMonoOn_of_deriv_pos` (resp. `strictAntiOn_of_deriv_neg`) turns
  -- positivity (resp. negativity) of `deriv U` on `interior D` plus `ContinuousOn U D`
  -- into `StrictMonoOn U D` (resp. `StrictAntiOn U D`). Since `interior D ⊆ D`, the
  -- pointwise hypothesis on `D` transfers to `interior D`, and `DifferentiableOn`
  -- supplies continuity. The `marginalUtility = deriv` defeq closes each branch.
  have hcU : ContinuousOn U D := hU.continuousOn
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact strictMonoOn_of_deriv_pos hDc hcU fun x hx => h x (interior_subset hx)
  · exact strictAntiOn_of_deriv_neg hDc hcU fun x hx => h x (interior_subset hx)
