-- Prove2me | solution 1 for MasulloGRH.nuclear_of_continuousLinearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:42:45.885996+00:00
-- url     : https://prove2.me/submissions/59bafd38-52b4-485a-a6b2-736e1941aa06

import Theorems.Thm_MasulloGRH_continuous_projTensor_map_left
import Theorems.Thm_MasulloGRH_continuous_epsTensor_map_left

open MasulloGRH TopologicalSpace TensorProduct
universe u

private theorem induced_of_equiv {A B : Type*} (a : TopologicalSpace A) (b : TopologicalSpace B)
    (e : A ≃ B) (hf : @Continuous A B a b e) (hi : @Continuous B A b a e.symm) :
    a = induced e b := by
  letI := a
  letI := b
  let h : A ≃ₜ B := ⟨e, hf, hi⟩
  exact h.isInducing.eq_induced

theorem solution (F G : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (e : F ≃L[ℂ] G)
    (hG : IsNuclear G) : IsNuclear F := by
  obtain ⟨⟨⟨I, hI, p, hp⟩, hT⟩, htop⟩ := hG
  have he : Topology.IsInducing e.toLinearEquiv.toLinearMap := e.toHomeomorph.isInducing
  refine ⟨⟨⟨I, hI, p.comp e.toLinearEquiv.toLinearMap, he.withSeminorms hp⟩,
    e.toHomeomorph.isEmbedding.t2Space⟩, ?_⟩
  intro H _ _ _ hH
  let L := (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl ℂ H)).toEquiv
  have hπ := induced_of_equiv (projTensorTopology F H) (projTensorTopology G H) L
    (continuous_projTensor_map_left F G H e.toContinuousLinearMap)
    (continuous_projTensor_map_left G F H e.symm.toContinuousLinearMap)
  have hε := induced_of_equiv (epsTensorTopology F H) (epsTensorTopology G H) L
    (continuous_epsTensor_map_left F G H e.toContinuousLinearMap)
    (continuous_epsTensor_map_left G F H e.symm.toContinuousLinearMap)
  rw [hπ, hε, htop H hH]
