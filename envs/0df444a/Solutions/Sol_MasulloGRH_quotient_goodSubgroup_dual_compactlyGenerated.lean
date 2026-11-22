-- Prove2me | solution 1 for MasulloGRH.quotient_goodSubgroup_dual_compactlyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:08:43.314434+00:00
-- url     : https://prove2.me/submissions/4fb41608-a6db-4623-902e-e6f07b499bdb

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace DualQAux

open MasulloGRH Set Topology

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- compact sets of `G ⧸ k` lift to compact sets of `G` -/
lemma exists_compact_lift (k : Subgroup G) [T2Space (G ⧸ k)] (K : Set (G ⧸ k))
    (hK : IsCompact K) : ∃ L : Set G, IsCompact L ∧ (QuotientGroup.mk : G → G ⧸ k) '' L = K := by
  classical
  have hq : Continuous (QuotientGroup.mk : G → G ⧸ k) := continuous_quot_mk
  have hqo : IsOpenMap (QuotientGroup.mk : G → G ⧸ k) := QuotientGroup.isOpenMap_coe
  -- for each `g`, a compact neighbourhood
  choose N hN using fun g : G => exists_compact_mem_nhds g
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun g : G => (QuotientGroup.mk : G → G ⧸ k) ''
      interior (N g)) (fun g => hqo _ isOpen_interior) (by
    intro x _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hN g).2, rfl⟩)
  refine ⟨(⋃ g ∈ t, N g) ∩ (QuotientGroup.mk : G → G ⧸ k) ⁻¹' K, ?_, ?_⟩
  · exact ((t.isCompact_biUnion fun g _ => (hN g).1)).inter_right (hK.isClosed.preimage hq)
  · apply Subset.antisymm
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
    · intro y hy
      obtain ⟨g, hg, x, hx, rfl⟩ := by simpa using ht hy
      exact ⟨x, ⟨mem_biUnion hg (interior_subset hx), hy⟩, rfl⟩

end DualQAux

open MasulloGRH DualQAux Set Topology in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k : Subgroup G) (hk : IsGoodSubgroup k) :
    IsCompactlyGeneratedSubgroup (⊤ : Subgroup (PontryaginDual (G ⧸ k))) := by
  classical
  haveI : IsClosed (k : Set G) := hk.1
  let q : G →ₜ* G ⧸ k := ⟨QuotientGroup.mk' k, continuous_quot_mk⟩
  let Φ := PontryaginDual.map q
  have hΦ : ∀ χ g, Φ χ g = χ (QuotientGroup.mk g) := fun _ _ => rfl
  -- injective
  have hinj : Function.Injective Φ := by
    intro χ ψ h
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have := congrArg (fun f : PontryaginDual G => f g) h
    simp only [hΦ] at this
    rw [this]
  -- range
  have hrange : range Φ = annihilator k := by
    ext χ
    constructor
    · rintro ⟨ψ, rfl⟩ x hx
      rw [hΦ, (QuotientGroup.eq_one_iff x).2 hx, map_one]
    · intro hχ
      let ψ0 : G ⧸ k →* Circle := QuotientGroup.lift k χ.toMonoidHom (fun x hx => hχ x hx)
      have hψc : Continuous ψ0 := continuous_coinduced_dom.2 χ.continuous
      exact ⟨⟨ψ0, hψc⟩, by ext g; rfl⟩
  -- inducing
  have hind : IsInducing Φ := by
    refine ⟨le_antisymm (continuous_iff_le_induced.1 (map_continuous Φ)) ?_⟩
    show TopologicalSpace.induced Φ _ ≤ TopologicalSpace.induced
      (ContinuousMonoidHom.toContinuousMap) ContinuousMap.compactOpen
    rw [ContinuousMap.compactOpen_eq, induced_generateFrom_eq]
    refine le_generateFrom ?_
    rintro _ ⟨_, ⟨K, hK, U, hU, rfl⟩, rfl⟩
    obtain ⟨L, hL, hLK⟩ := exists_compact_lift k K hK
    refine ⟨{ψ : PontryaginDual G | MapsTo ψ L U}, ?_, ?_⟩
    · exact (ContinuousMap.isOpen_setOfPred_mapsTo (X := G) (Y := Circle) hL hU).preimage
        (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous
    · ext χ
      change MapsTo (fun g => χ (QuotientGroup.mk g)) L U ↔ MapsTo (fun x => χ x) K U
      constructor
      · intro h y hy
        rw [← hLK] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact h hx
      · intro h x hx
        exact h (by rw [← hLK]; exact ⟨x, hx, rfl⟩)
  obtain ⟨A, hA, U, hUc, hUA, ⟨V, hV, hVU⟩, hcl⟩ := hk.2.2
  have hUr : U ⊆ range Φ := by rw [hrange, ← hA]; exact hUA
  refine ⟨Φ ⁻¹' U, (hind.isCompact_preimage_iff hUr).2 hUc, fun _ _ => trivial,
    ⟨Φ ⁻¹' V, (map_continuous Φ).continuousAt.preimage_mem_nhds (by rw [map_one Φ]; exact hV), ?_⟩, ?_⟩
  · rintro x ⟨hx, -⟩
    have : Φ x ∈ (A : Set (PontryaginDual G)) := by rw [hA, ← hrange]; exact ⟨x, rfl⟩
    exact hVU ⟨hx, this⟩
  · let Φh : PontryaginDual (G ⧸ k) →* PontryaginDual G := Φ.toMonoidHom
    apply Subgroup.map_injective (f := Φh) hinj
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map]
    have h1 : (Φh : PontryaginDual (G ⧸ k) → PontryaginDual G) '' (Φ ⁻¹' U) = U :=
      image_preimage_eq_of_subset hUr
    rw [h1, hcl]
    apply SetLike.ext'
    rw [MonoidHom.coe_range, hA]
    exact hrange.symm
