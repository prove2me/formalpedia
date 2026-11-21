-- Prove2me | solution 1 for MasulloGRH.nuclear_projTensor
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T22:57:52.12623+00:00
-- url     : https://prove2.me/submissions/4f4d1fd4-d0c8-43b9-8f46-b43d5b16893f

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_projTensor_isHLCS
import Theorems.Thm_MasulloGRH_projTensor_assoc
import Theorems.Thm_MasulloGRH_epsTensor_assoc

set_option autoImplicit false

open MasulloGRH
open TensorProduct Topology

universe u

theorem solution (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsNuclear E) (hF : IsNuclear F) :
    @IsNuclear (E ⊗[ℂ] F) _ _ (projTensorTopology E F) := by
  refine ⟨projTensor_isHLCS E F hE.1 hF.1, ?_⟩
  intro G _ _ _ hG
  -- `F ⊗_π G = F ⊗_ε G`, and this space is Hausdorff locally convex.
  have hFG : projTensorTopology F G = epsTensorTopology F G := hF.2 G hG
  have hFG' : @IsHLCS (F ⊗[ℂ] G) _ _ (epsTensorTopology F G) := by
    rw [← hFG]; exact projTensor_isHLCS F G hF.1 hG
  -- `E ⊗_π (F ⊗_ε G) = E ⊗_ε (F ⊗_ε G)` by nuclearity of `E`.
  have hE' := @hE.2 (F ⊗[ℂ] G) _ _ (epsTensorTopology F G) hFG'
  -- `E ⊗_π F = E ⊗_ε F` by nuclearity of `E`.
  have hEF : projTensorTopology E F = epsTensorTopology E F := hE.2 F hF.1
  calc @projTensorTopology (E ⊗[ℂ] F) _ _ (projTensorTopology E F) G _ _ _
      = TopologicalSpace.induced (TensorProduct.assoc ℂ E F G)
          (@projTensorTopology E _ _ _ (F ⊗[ℂ] G) _ _ (projTensorTopology F G)) :=
        projTensor_assoc E F G hE.1 hF.1 hG
    _ = TopologicalSpace.induced (TensorProduct.assoc ℂ E F G)
          (@epsTensorTopology E _ _ _ (F ⊗[ℂ] G) _ _ (epsTensorTopology F G)) := by
        rw [hFG, hE']
    _ = @epsTensorTopology (E ⊗[ℂ] F) _ _ (epsTensorTopology E F) G _ _ _ :=
        (epsTensor_assoc E F G hE.1 hF.1 hG).symm
    _ = @epsTensorTopology (E ⊗[ℂ] F) _ _ (projTensorTopology E F) G _ _ _ := by
        rw [hEF]
