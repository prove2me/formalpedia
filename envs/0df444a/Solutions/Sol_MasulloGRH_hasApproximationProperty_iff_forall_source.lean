-- Prove2me | solution 1 for MasulloGRH.hasApproximationProperty_iff_forall_source
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:38:51.197519+00:00
-- url     : https://prove2.me/submissions/084a78e4-70e5-4780-916a-179f32b007ff

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_TopologicalTensorProduct_ApproximationProperty

open Topology Filter TopologicalTensorProduct
set_option autoImplicit false
universe u

namespace Sol_MasulloGRH_hasApproximationProperty_iff_forall_source

/-- The image of a pre-compact set under a continuous linear map is pre-compact. -/
theorem isPrecompact_image {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (T : F →L[ℂ] E) {K : Set F}
    (hK : IsPrecompact K) : IsPrecompact (T '' K) := by
  intro V hV
  have hV' : T ⁻¹' V ∈ 𝓝 (0 : F) := by
    have h0 : V ∈ 𝓝 (T 0) := by rw [map_zero]; exact hV
    exact T.continuous.continuousAt.preimage_mem_nhds h0
  obtain ⟨t, ht⟩ := hK (T ⁻¹' V) hV'
  classical
  refine ⟨t.image T, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
  refine Set.mem_iUnion₂.mpr ⟨T x, Finset.mem_image_of_mem T hx, ?_⟩
  have h : T (y - x) ∈ V := hyx
  rw [map_sub] at h
  exact h

end Sol_MasulloGRH_hasApproximationProperty_iff_forall_source

open MasulloGRH Sol_MasulloGRH_hasApproximationProperty_iff_forall_source

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E) :
    HasApproximationProperty ℂ E ↔
      ∀ (F : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F], IsHLCS F →
        ∀ (T : F →L[ℂ] E) (K : Set F), IsPrecompact K → ∀ U ∈ 𝓝 (0 : E),
          ∃ (N : ℕ) (ψ : Fin N → StrongDual ℂ F) (x : Fin N → E),
            ∀ y ∈ K, T y - ∑ i, ψ i y • x i ∈ U := by
  constructor
  · intro hAP F _ _ _ _ T K hK U hU
    obtain ⟨N, φ, x, h⟩ := hAP (T '' K) (isPrecompact_image T hK) U hU
    refine ⟨N, fun i => (φ i).comp T, x, ?_⟩
    intro y hy
    exact h (T y) (Set.mem_image_of_mem T hy)
  · intro h K hK U hU
    obtain ⟨N, ψ, x, hx⟩ := h E hE (ContinuousLinearMap.id ℂ E) K hK U hU
    exact ⟨N, ψ, x, fun y hy => hx y hy⟩
