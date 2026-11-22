-- Prove2me | solution 1 for LCAGroup.openCompactlyGenerated_directed_union
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:06:23.533492+00:00
-- url     : https://prove2.me/submissions/d9026db6-dc34-4244-905f-c961aed990a5

import Mathlib

open Topology

set_option autoImplicit false


theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (CG : Set (Subgroup G))
    (hCG : CG = {H : Subgroup G | IsOpen (H : Set G) ∧
      ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = H}) :
    DirectedOn (· ≤ ·) CG ∧
    (∀ x : G, ∃ H ∈ CG, x ∈ H) ∧
    ∀ V : Set G, IsOpen V ↔ ∀ H ∈ CG, IsOpen ((fun x : H => (x : G)) ⁻¹' V) := by
  subst hCG
  have key : ∀ U ∈ 𝓝 (1 : G), IsCompact U →
      Subgroup.closure U ∈ {H : Subgroup G | IsOpen (H : Set G) ∧
        ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = H} := by
    intro U hU hUc
    exact ⟨Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hU Subgroup.subset_closure),
      U, hU, hUc, rfl⟩
  have cover : ∀ x : G, ∃ H ∈ {H : Subgroup G | IsOpen (H : Set G) ∧
        ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = H}, x ∈ H := by
    intro x
    obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
    refine ⟨Subgroup.closure (K ∪ {x}), key _ (Filter.mem_of_superset hK1 Set.subset_union_left)
      (hK.union isCompact_singleton), Subgroup.subset_closure (Or.inr rfl)⟩
  refine ⟨?_, cover, ?_⟩
  · rintro H₁ ⟨-, U₁, hU₁, hc₁, rfl⟩ H₂ ⟨-, U₂, hU₂, hc₂, rfl⟩
    refine ⟨Subgroup.closure (U₁ ∪ U₂), key _ (Filter.mem_of_superset hU₁ Set.subset_union_left)
      (hc₁.union hc₂), Subgroup.closure_mono Set.subset_union_left,
      Subgroup.closure_mono Set.subset_union_right⟩
  · intro V
    constructor
    · intro hV H _
      exact hV.preimage continuous_subtype_val
    · intro h
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨H, hH, hxH⟩ := cover x
      have h1 := h H hH
      have h2 : IsOpen ((fun y : H => (y : G)) '' ((fun x : H => (x : G)) ⁻¹' V)) :=
        hH.1.isOpenMap_subtype_val _ h1
      refine Filter.mem_of_superset (h2.mem_nhds ⟨⟨x, hxH⟩, hx, rfl⟩) ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hy
