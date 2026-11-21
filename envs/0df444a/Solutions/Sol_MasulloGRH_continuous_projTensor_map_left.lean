-- Prove2me | solution 1 for MasulloGRH.continuous_projTensor_map_left
-- status  : ACCEPTED   (prove)
-- author  : @nlehmann
-- created : 2026-11-20T22:43:07.356173+00:00
-- url     : https://prove2.me/submissions/ea03eeaa-11ff-4f34-859d-e0185b275452

import Definitions.Def_MasulloGRH_LocallyConvex
open TensorProduct
universe u

theorem solution (F G H : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] (f : F →L[ℂ] G) :
    @Continuous (F ⊗[ℂ] H) (G ⊗[ℂ] H) (MasulloGRH.projTensorTopology F H)
      (MasulloGRH.projTensorTopology G H)
      (TensorProduct.map f.toLinearMap (LinearMap.id : H →ₗ[ℂ] H)) := by
  set L : F ⊗[ℂ] H →ₗ[ℂ] G ⊗[ℂ] H := TensorProduct.map f.toLinearMap LinearMap.id with hL
  rw [continuous_iff_le_induced]
  unfold MasulloGRH.projTensorTopology
  rw [induced_sInf]
  refine le_sInf ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨⟨ι, hι, p, hp⟩, hcont⟩ := ht
  apply sInf_le
  refine ⟨⟨ι, hι, p.comp L, ?_⟩, ?_⟩
  · letI : TopologicalSpace (G ⊗[ℂ] H) := t
    exact L.withSeminorms_induced hp
  · letI : TopologicalSpace (G ⊗[ℂ] H) := t
    rw [continuous_induced_rng]
    have hcomp : (L ∘ fun q : F × H => q.1 ⊗ₜ[ℂ] q.2) =
        (fun q : G × H => q.1 ⊗ₜ[ℂ] q.2) ∘ Prod.map f id := by
      funext q; simp [hL]
    rw [hcomp]
    exact hcont.comp (f.continuous.prodMap continuous_id)
