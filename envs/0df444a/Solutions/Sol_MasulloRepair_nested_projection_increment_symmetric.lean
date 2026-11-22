-- Prove2me | solution 1 for MasulloRepair.nested_projection_increment_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T22:06:05.351076+00:00
-- url     : https://prove2.me/submissions/6091a6e6-9d32-4b8f-899e-a0b5712c99f5

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U V : Submodule ℂ H}
    [hU : U.HasOrthogonalProjection] [hV : V.HasOrthogonalProjection]
    (hUV : U ≤ V) :
    ((V.starProjection - U.starProjection : H →L[ℂ] H) : H →ₗ[ℂ] H).IsSymmetricProjection := by
  have hrange : LinearMap.range (U.starProjection : H →ₗ[ℂ] H) ≤
      LinearMap.range (V.starProjection : H →ₗ[ℂ] H) := by
    simpa only [Submodule.range_starProjection] using hUV
  exact LinearMap.IsSymmetricProjection.sub_of_range_le_range
    (Submodule.isSymmetricProjection_starProjection U)
    (Submodule.isSymmetricProjection_starProjection V) hrange
