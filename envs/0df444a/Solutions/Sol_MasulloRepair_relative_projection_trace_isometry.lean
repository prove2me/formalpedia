-- Prove2me | solution 1 for MasulloRepair.relative_projection_trace_isometry
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T19:32:07.120829+00:00
-- url     : https://prove2.me/submissions/ec33425c-89d1-465e-af87-881199474abd

import Theorems.Thm_MasulloRepair_isometric_image_projection
import Theorems.Thm_MasulloRepair_nuclear_isometry_transport

set_option autoImplicit false

open MasulloGRH MasulloRepair ContinuousLinearMap

theorem solution {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : H →ₗᵢ[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (P Q : Submodule ℂ H) [CompleteSpace P] [CompleteSpace Q]
    (hinter : ∀ v : H, B (U v) = U (A v))
    (hnuc : IsNuclearOperator (A ∘L (P.starProjection - Q.starProjection))) :
    let T := A ∘L (P.starProjection - Q.starProjection)
    let S := B ∘L ((P.map (U : H →ₗ[ℂ] K)).starProjection -
      (Q.map (U : H →ₗ[ℂ] K)).starProjection)
    S = U.toContinuousLinearMap ∘L T ∘L U.toContinuousLinearMap.adjoint ∧
      IsNuclearOperator S ∧ operatorTrace S = operatorTrace T := by
  dsimp only
  have heq : B ∘L ((P.map (U : H →ₗ[ℂ] K)).starProjection -
      (Q.map (U : H →ₗ[ℂ] K)).starProjection) =
      U.toContinuousLinearMap ∘L (A ∘L (P.starProjection - Q.starProjection)) ∘L
        U.toContinuousLinearMap.adjoint := by
    rw [isometric_image_projection U P, isometric_image_projection U Q]
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      LinearIsometry.coe_toContinuousLinearMap, ← U.map_sub, hinter]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact nuclear_isometry_transport U _ hnuc

#print axioms solution
