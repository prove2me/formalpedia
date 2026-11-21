-- Prove2me | solution 1 for MasulloGRH.frechet_of_closed_linear_embedding
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:38:16.54331+00:00
-- url     : https://prove2.me/submissions/e336f663-0337-4b2f-bf53-ef7a3d1685b7

import Definitions.Def_MasulloGRH_LocallyConvex

open MasulloGRH Set Filter Topology
universe u

theorem solution (F G : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (u : F →ₗ[ℂ] G)
    (hu : IsClosedEmbedding u) (hG : IsFrechet G) : IsFrechet F := by
  obtain ⟨⟨I, hI, p, hp⟩, ⟨hT, hcomplete⟩, hmetric⟩ := hG
  haveI := hT
  haveI := hmetric
  refine ⟨⟨I, hI, p.comp u, hu.isEmbedding.isInducing.withSeminorms hp⟩,
    ⟨hu.isEmbedding.t2Space, ?_⟩, hu.isEmbedding.metrizableSpace⟩
  intro f hf
  haveI : NeBot f := hf.1
  have hc : IsCauchyFilter (map u f) := by
    refine ⟨inferInstance, ?_⟩
    intro U hU
    have hpre : u ⁻¹' U ∈ 𝓝 (0 : F) := (hu.continuous.tendsto' 0 0 (map_zero u)) hU
    obtain ⟨A, hA, hsmall⟩ := hf.2 _ hpre
    refine ⟨u '' A, (image_mem_map_iff hu.injective).mpr hA, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa only [mem_preimage, map_sub] using hsmall x hx y hy
  obtain ⟨y, hy⟩ := hcomplete _ hc
  have hmem : y ∈ range u := hu.isClosed_range.mem_of_tendsto
    (show Tendsto u f (𝓝 y) from hy) (Eventually.of_forall (fun x => mem_range_self x))
  obtain ⟨x, rfl⟩ := hmem
  refine ⟨x, ?_⟩
  rw [hu.isEmbedding.isInducing.nhds_eq_comap]
  exact map_le_iff_le_comap.mp hy
