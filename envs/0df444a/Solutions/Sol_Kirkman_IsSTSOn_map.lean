-- Prove2me | solution 1 for Kirkman.IsSTSOn.map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:41:24.983524+00:00
-- url     : https://prove2.me/submissions/f6064897-a170-43f8-afad-49bbb49e4d9c

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
variable {P : Type*}
namespace Kirkman
namespace IsSTSOn
theorem _root_.solution [DecidableEq P] {Q : Type*} [DecidableEq Q] {𝒯 : Finset (Finset P)} (h :
    IsSTSOn 𝒯)
    (e : P ≃ Q) : IsSTSOn (𝒯.map ⟨fun T => T.map e.toEmbedding, map_injective _⟩) := by
  refine ⟨fun T hT => ?_, fun x y hxy => ?_⟩
  · obtain ⟨T₁, hT₁, rfl⟩ := mem_map.1 hT
    simp only [Function.Embedding.coeFn_mk, card_map]
    exact h.1 T₁ hT₁
  · have hxy' : e.symm x ≠ e.symm y := fun h' => hxy (e.symm.injective h')
    obtain ⟨T, ⟨hT, hxT, hyT⟩, huniq⟩ := h.2 _ _ hxy'
    refine ⟨T.map e.toEmbedding, ⟨mem_map_of_mem _ hT, ?_, ?_⟩, ?_⟩
    · exact mem_map.2 ⟨_, hxT, by simp⟩
    · exact mem_map.2 ⟨_, hyT, by simp⟩
    · rintro T' ⟨hT', hxT', hyT'⟩
      obtain ⟨T₀, hT₀, rfl⟩ := mem_map.1 hT'
      simp only [Function.Embedding.coeFn_mk] at hxT' hyT' ⊢
      have hx0 : e.symm x ∈ T₀ := by
        obtain ⟨u, hu, hux⟩ := mem_map.1 hxT'
        simp only [Equiv.coe_toEmbedding] at hux
        rw [← hux, Equiv.symm_apply_apply]; exact hu
      have hy0 : e.symm y ∈ T₀ := by
        obtain ⟨u, hu, hux⟩ := mem_map.1 hyT'
        simp only [Equiv.coe_toEmbedding] at hux
        rw [← hux, Equiv.symm_apply_apply]; exact hu
      rw [huniq T₀ ⟨hT₀, hx0, hy0⟩]
end IsSTSOn
end Kirkman
