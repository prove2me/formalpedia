-- Prove2me | solution 1 for MasulloRepair.nested_projection_increment_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T21:51:31.570939+00:00
-- url     : https://prove2.me/submissions/d9b9c048-7f15-44b6-90bc-beb5af823d07

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem projection_comp_sub_projection_left
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U V : Submodule ℂ H}
    [hU : U.HasOrthogonalProjection] [hV : V.HasOrthogonalProjection]
    (hUV : U ≤ V) :
    U.starProjection ∘L (V.starProjection - U.starProjection) = 0 := by
  have hUVleft : U.starProjection ∘L V.starProjection = U.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le hUV
  have hUU : U.starProjection ∘L U.starProjection = U.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (le_refl U)
  calc
    U.starProjection ∘L (V.starProjection - U.starProjection) =
        (U.starProjection ∘L V.starProjection) -
          (U.starProjection ∘L U.starProjection) := by
            ext x
            simp [ContinuousLinearMap.comp_apply]
    _ = U.starProjection - U.starProjection := by rw [hUVleft, hUU]
    _ = 0 := sub_self _

private theorem projection_comp_sub_projection_right
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U V : Submodule ℂ H}
    [hU : U.HasOrthogonalProjection] [hV : V.HasOrthogonalProjection]
    (hUV : U ≤ V) :
    (V.starProjection - U.starProjection) ∘L U.starProjection = 0 := by
  have hVU : V.starProjection ∘L U.starProjection = U.starProjection := by
    ext x
    rw [ContinuousLinearMap.comp_apply]
    exact Submodule.starProjection_eq_self_iff.mpr
      (hUV (Submodule.starProjection_apply_mem U x))
  have hUU : U.starProjection ∘L U.starProjection = U.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (le_refl U)
  calc
    (V.starProjection - U.starProjection) ∘L U.starProjection =
        (V.starProjection ∘L U.starProjection) -
          (U.starProjection ∘L U.starProjection) := by
            ext x
            simp [ContinuousLinearMap.comp_apply]
    _ = U.starProjection - U.starProjection := by rw [hVU, hUU]
    _ = 0 := sub_self _

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U V : Submodule ℂ H}
    [hU : U.HasOrthogonalProjection] [hV : V.HasOrthogonalProjection]
    (hUV : U ≤ V) :
    U.starProjection ∘L (V.starProjection - U.starProjection) = 0 ∧
      (V.starProjection - U.starProjection) ∘L U.starProjection = 0 := by
  exact ⟨projection_comp_sub_projection_left hUV,
    projection_comp_sub_projection_right hUV⟩
