-- Prove2me | solution 1 for MasulloRepair.isometric_image_projection
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T19:29:45.225284+00:00
-- url     : https://prove2.me/submissions/00dae838-1945-4ad5-889c-b95dacbc45e0

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit false

open ContinuousLinearMap
open scoped InnerProductSpace

theorem solution {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : H →ₗᵢ[ℂ] K) (P : Submodule ℂ H)
    [CompleteSpace P] :
    (P.map (U : H →ₗ[ℂ] K)).starProjection =
      U.toContinuousLinearMap ∘L P.starProjection ∘L U.toContinuousLinearMap.adjoint := by
  ext x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_map_of_mem (P.starProjection_apply_mem _)
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hw
    change ⟪x - U (P.starProjection (U.toContinuousLinearMap.adjoint x)), U v⟫_ℂ = 0
    rw [inner_sub_left, U.inner_map_map]
    have hu := U.toContinuousLinearMap.adjoint_inner_left v x
    change ⟪U.toContinuousLinearMap.adjoint x, v⟫_ℂ = ⟪x, U v⟫_ℂ at hu
    rw [← hu]
    simpa only [inner_sub_left] using
      Submodule.starProjection_inner_eq_zero (K := P)
        (U.toContinuousLinearMap.adjoint x) v hv

#print axioms solution
