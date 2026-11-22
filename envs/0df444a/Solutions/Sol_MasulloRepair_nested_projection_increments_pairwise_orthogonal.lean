-- Prove2me | solution 1 for MasulloRepair.nested_projection_increments_pairwise_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T22:42:23.491704+00:00
-- url     : https://prove2.me/submissions/4440366b-a0ba-4570-a8b7-906e59d31d46

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem solution_pairwise_left
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U V W : Submodule ℂ H}
    [hU : U.HasOrthogonalProjection] [hV : V.HasOrthogonalProjection]
    [hW : W.HasOrthogonalProjection]
    (hUV : U ≤ V) (hVW : V ≤ W) :
    (V.starProjection - U.starProjection) ∘L
        (W.starProjection - V.starProjection) = 0 := by
  have hVWleft : V.starProjection ∘L W.starProjection = V.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le hVW
  have hVV : V.starProjection ∘L V.starProjection = V.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (le_refl V)
  have hUWleft : U.starProjection ∘L W.starProjection = U.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (hUV.trans hVW)
  have hUVleft : U.starProjection ∘L V.starProjection = U.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le hUV
  calc
    (V.starProjection - U.starProjection) ∘L
        (W.starProjection - V.starProjection) =
        (V.starProjection ∘L W.starProjection) -
          (V.starProjection ∘L V.starProjection) -
          (U.starProjection ∘L W.starProjection) +
          (U.starProjection ∘L V.starProjection) := by
            ext x
            simp [ContinuousLinearMap.comp_apply]
            abel
    _ = V.starProjection - V.starProjection - U.starProjection + U.starProjection := by
      rw [hVWleft, hVV, hUWleft, hUVleft]
    _ = 0 := by simp

private theorem solution_pairwise_right
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U V W : Submodule ℂ H}
    [hU : U.HasOrthogonalProjection] [hV : V.HasOrthogonalProjection]
    [hW : W.HasOrthogonalProjection]
    (hUV : U ≤ V) (hVW : V ≤ W) :
    (W.starProjection - V.starProjection) ∘L
        (V.starProjection - U.starProjection) = 0 := by
  have hWV : W.starProjection ∘L V.starProjection = V.starProjection := by
    ext x
    rw [ContinuousLinearMap.comp_apply]
    exact Submodule.starProjection_eq_self_iff.mpr
      (hVW (Submodule.starProjection_apply_mem V x))
  have hWU : W.starProjection ∘L U.starProjection = U.starProjection := by
    ext x
    rw [ContinuousLinearMap.comp_apply]
    exact Submodule.starProjection_eq_self_iff.mpr
      ((hUV.trans hVW) (Submodule.starProjection_apply_mem U x))
  have hVV : V.starProjection ∘L V.starProjection = V.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (le_refl V)
  have hVU : V.starProjection ∘L U.starProjection = U.starProjection := by
    ext x
    rw [ContinuousLinearMap.comp_apply]
    exact Submodule.starProjection_eq_self_iff.mpr
      (hUV (Submodule.starProjection_apply_mem U x))
  calc
    (W.starProjection - V.starProjection) ∘L
        (V.starProjection - U.starProjection) =
        (W.starProjection ∘L V.starProjection) -
          (W.starProjection ∘L U.starProjection) -
          (V.starProjection ∘L V.starProjection) +
          (V.starProjection ∘L U.starProjection) := by
            ext x
            simp [ContinuousLinearMap.comp_apply]
            abel
    _ = V.starProjection - U.starProjection - V.starProjection + U.starProjection := by
      rw [hWV, hWU, hVV, hVU]
    _ = 0 := by simp

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U V W : Submodule ℂ H}
    [hU : U.HasOrthogonalProjection] [hV : V.HasOrthogonalProjection]
    [hW : W.HasOrthogonalProjection]
    (hUV : U ≤ V) (hVW : V ≤ W) :
    ((V.starProjection - U.starProjection) ∘L
        (W.starProjection - V.starProjection) = 0) ∧
      ((W.starProjection - V.starProjection) ∘L
        (V.starProjection - U.starProjection) = 0) := by
  exact ⟨solution_pairwise_left hUV hVW, solution_pairwise_right hUV hVW⟩
