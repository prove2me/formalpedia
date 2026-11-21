-- Prove2me | solution 2 for MasulloGRH.continuous_projTensor_map_left
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:46:15.154301+00:00
-- url     : https://prove2.me/submissions/e2658868-b628-4467-864b-e85db95f07a3

import Definitions.Def_MasulloGRH_LocallyConvex
open Set MasulloGRH TensorProduct TopologicalSpace
universe u

theorem solution (F G H : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] (f : F →L[ℂ] G) :
    @Continuous (F ⊗[ℂ] H) (G ⊗[ℂ] H) (projTensorTopology F H) (projTensorTopology G H)
      (TensorProduct.map f.toLinearMap (LinearMap.id : H →ₗ[ℂ] H)) := by
  let L := TensorProduct.map f.toLinearMap (LinearMap.id : H →ₗ[ℂ] H)
  change @Continuous _ _ (projTensorTopology F H) (projTensorTopology G H) L
  rw [continuous_iff_le_induced]
  unfold projTensorTopology
  rw [induced_sInf]
  apply le_sInf
  rintro _ ⟨τ, ⟨⟨I, hI, p, hp⟩, hcan⟩, rfl⟩
  letI := τ
  refine sInf_le ⟨⟨I, hI, p.comp L, L.withSeminorms_induced hp⟩, continuous_induced_rng.mpr ?_⟩
  have hprod : Continuous (fun x : F × H => (f x.1, x.2)) :=
    (f.continuous.comp continuous_fst).prodMk continuous_snd
  simpa only [L, Function.comp_def, TensorProduct.map_tmul, LinearMap.id_apply,
    ContinuousLinearMap.coe_coe] using hcan.comp hprod
