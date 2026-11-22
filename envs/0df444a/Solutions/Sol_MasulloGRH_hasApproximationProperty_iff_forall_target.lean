-- Prove2me | solution 1 for MasulloGRH.hasApproximationProperty_iff_forall_target
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:37:28.507657+00:00
-- url     : https://prove2.me/submissions/51ea9883-2130-42ac-956b-a7c86570c545

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_TopologicalTensorProduct_ApproximationProperty

open Topology Filter TopologicalTensorProduct
set_option autoImplicit false
universe u

open MasulloGRH

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E) :
    HasApproximationProperty ℂ E ↔
      ∀ (F : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F], IsHLCS F →
        ∀ (T : E →L[ℂ] F) (K : Set E), IsPrecompact K → ∀ V ∈ 𝓝 (0 : F),
          ∃ (N : ℕ) (φ : Fin N → StrongDual ℂ E) (y : Fin N → F),
            ∀ x ∈ K, T x - ∑ i, φ i x • y i ∈ V := by
  constructor
  · -- approximation property of `E` ⟹ approximation of every `T : E → F`
    intro h F _ _ _ _ T K hK V hV
    -- `T ⁻¹' V` is a neighbourhood of `0` in `E`
    have hU : T ⁻¹' V ∈ 𝓝 (0 : E) := by
      have hT : Filter.Tendsto T (𝓝 (0 : E)) (𝓝 (T 0)) := T.continuous.tendsto 0
      rw [map_zero] at hT
      exact hT hV
    obtain ⟨N, φ, y, hy⟩ := h K hK (T ⁻¹' V) hU
    refine ⟨N, φ, fun i => T (y i), fun x hx => ?_⟩
    have hx' : T (x - ∑ i, φ i x • y i) ∈ V := hy x hx
    have hT : T (x - ∑ i, φ i x • y i) = T x - ∑ i, φ i x • T (y i) := by
      rw [map_sub, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => map_smul T (φ i x) (y i)
    rw [hT] at hx'
    exact hx'
  · -- the case `F = E`, `T = id`
    intro h K hK U hU
    obtain ⟨N, φ, y, hy⟩ := h E hE (ContinuousLinearMap.id ℂ E) K hK U hU
    exact ⟨N, φ, y, fun x hx => by simpa using hy x hx⟩
