-- Prove2me | solution 1 for MasulloGRH.isStructuralPair_comap_quotient
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:27:23.802009+00:00
-- url     : https://prove2.me/submissions/31778dcb-8563-4807-9d08-12f91b684824

import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup

set_option autoImplicit false

universe u

namespace ComapAux

open MasulloGRH Set Topology

variable {A B : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [LocallyCompactSpace A] [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]

/-- compact sets lift along open continuous surjections from a locally compact group -/
lemma exists_compact_lift (p : A →* B) (hpc : Continuous p) (hpo : IsOpenMap p)
    (hps : Function.Surjective p) (K : Set B) (hK : IsCompact K) :
    ∃ L : Set A, IsCompact L ∧ p '' L = K := by
  classical
  choose N hN using fun g : A => exists_compact_mem_nhds g
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun g : A => p '' interior (N g))
    (fun g => hpo _ isOpen_interior) (by
    intro x _
    obtain ⟨g, rfl⟩ := hps x
    exact mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hN g).2, rfl⟩)
  refine ⟨(⋃ g ∈ t, N g) ∩ p ⁻¹' K, ?_, ?_⟩
  · exact ((t.isCompact_biUnion fun g _ => (hN g).1)).inter_right (hK.isClosed.preimage hpc)
  · apply Subset.antisymm
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
    · intro y hy
      obtain ⟨g, hg, x, hx, rfl⟩ := by simpa using ht hy
      exact ⟨x, ⟨mem_biUnion hg (interior_subset hx), hy⟩, rfl⟩

/-- preimages of compactly generated subgroups under open continuous surjections with compact
kernel are compactly generated -/
lemma isCompactlyGenerated_comap (p : A →* B) (hpc : Continuous p) (hpo : IsOpenMap p)
    (hps : Function.Surjective p) (hK : IsCompact (p.ker : Set A)) (Γ : Subgroup B)
    (hΓ : IsCompactlyGeneratedSubgroup Γ) : IsCompactlyGeneratedSubgroup (Γ.comap p) := by
  obtain ⟨U, hUc, hUΓ, ⟨V, hV, hVU⟩, hcl⟩ := hΓ
  obtain ⟨L, hLc, hLU⟩ := exists_compact_lift p hpc hpo hps U hUc
  let U' : Set A := (fun x : A × A => x.1 * x.2) '' ((L ∪ {1}) ×ˢ (p.ker : Set A))
  have hU'c : IsCompact U' :=
    ((hLc.union isCompact_singleton).prod hK).image continuous_mul
  have hpU' : p '' U' = U ∪ {1} := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨l, c⟩, ⟨hl, hc⟩, rfl⟩, rfl⟩
      have hc1 : p c = 1 := hc
      simp only [map_mul, hc1, mul_one]
      rcases hl with hl | hl
      · exact Or.inl (hLU ▸ mem_image_of_mem p hl)
      · have h1 : l = 1 := hl
        rw [h1, map_one]; exact Or.inr rfl
    · rintro (hy | hy)
      · rw [← hLU] at hy
        obtain ⟨l, hl, rfl⟩ := hy
        exact ⟨l * 1, ⟨(l, 1), ⟨Or.inl hl, p.ker.one_mem⟩, rfl⟩, by simp⟩
      · rw [mem_singleton_iff.1 hy]
        exact ⟨1 * 1, ⟨(1, 1), ⟨Or.inr rfl, p.ker.one_mem⟩, rfl⟩, by simp⟩
  have hkerU' : (p.ker : Set A) ⊆ U' := fun c hc =>
    ⟨(1, c), ⟨Or.inr rfl, hc⟩, by simp⟩
  refine ⟨U', hU'c, ?_, ⟨p ⁻¹' V, hpc.continuousAt.preimage_mem_nhds (by rwa [map_one]), ?_⟩, ?_⟩
  · rintro _ ⟨⟨l, c⟩, ⟨hl, hc⟩, rfl⟩
    have hc1 : p c = 1 := hc
    show p (l * c) ∈ Γ
    rw [map_mul, hc1, mul_one]
    rcases hl with hl | hl
    · exact hUΓ (hLU ▸ mem_image_of_mem p hl)
    · have h1 : l = 1 := hl
      rw [h1, map_one]; exact Γ.one_mem
  · rintro x ⟨hxV, hxΓ⟩
    have : p x ∈ U := hVU ⟨hxV, hxΓ⟩
    rw [← hLU] at this
    obtain ⟨l, hl, hlx⟩ := this
    refine ⟨(l, l⁻¹ * x), ⟨Or.inl hl, ?_⟩, by simp⟩
    show p (l⁻¹ * x) = 1
    rw [map_mul, map_inv, hlx, inv_mul_cancel]
  · have hmap : (Subgroup.closure U').map p = Γ := by
      rw [MonoidHom.map_closure, hpU', Subgroup.closure_union, hcl, Subgroup.closure_singleton_one,
        sup_bot_eq]
    rw [← hmap, Subgroup.comap_map_eq, sup_eq_left.2]
    intro c hc
    exact Subgroup.subset_closure (hkerU' hc)

end ComapAux

open MasulloGRH ComapAux Set Topology in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') (hle : k' ≤ k)
    (Γ k₁ : Subgroup (G ⧸ k)) (hs : IsStructuralPair Γ k₁) :
    IsStructuralPair (Γ.comap (QuotientGroup.map k' k (MonoidHom.id G) hle))
      (k₁.comap (QuotientGroup.map k' k (MonoidHom.id G) hle)) := by
  classical
  haveI : IsClosed (k : Set G) := hk.1
  haveI : IsClosed (k' : Set G) := hk'.1
  set p := QuotientGroup.map k' k (MonoidHom.id G) hle with hpdef
  have hpmk : ∀ g : G, p (QuotientGroup.mk g) = QuotientGroup.mk g := fun _ => rfl
  have hpc : Continuous p := continuous_coinduced_dom.2 continuous_quot_mk
  have hpo : IsOpenMap p := by
    intro W hW
    have : p '' W = (QuotientGroup.mk : G → G ⧸ k) '' ((QuotientGroup.mk : G → G ⧸ k') ⁻¹' W) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        exact ⟨g, hx, rfl⟩
      · rintro ⟨g, hg, rfl⟩; exact ⟨_, hg, rfl⟩
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ (hW.preimage continuous_quot_mk)
  have hps : Function.Surjective p := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hker : (p.ker : Set (G ⧸ k')) = (QuotientGroup.mk : G → G ⧸ k') '' (k : Set G) := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    constructor
    · intro hx
      have : (QuotientGroup.mk g : G ⧸ k) = 1 := hx
      exact ⟨g, (QuotientGroup.eq_one_iff g).1 this, rfl⟩
    · rintro ⟨g', hg', hgg⟩
      show p (QuotientGroup.mk g) = 1
      rw [← hgg, hpmk]; exact (QuotientGroup.eq_one_iff g').2 hg'
  have hkerc : IsCompact (p.ker : Set (G ⧸ k')) := by
    rw [hker]; exact (isCompact_of_isGoodSubgroup G k hk).image continuous_quot_mk
  let pc : (G ⧸ k') →ₜ* (G ⧸ k) := ⟨p, hpc⟩
  let Φ := PontryaginDual.map pc
  have hΦ : ∀ χ x, Φ χ x = χ (p x) := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    intro χ ψ h
    ext x
    obtain ⟨y, rfl⟩ := hps x
    have := congrArg (fun f : PontryaginDual (G ⧸ k') => f y) h
    simp only [hΦ] at this
    rw [this]
  have hind : IsInducing Φ := by
    refine ⟨le_antisymm (continuous_iff_le_induced.1 (map_continuous Φ)) ?_⟩
    show TopologicalSpace.induced Φ _ ≤ TopologicalSpace.induced
      (ContinuousMonoidHom.toContinuousMap) ContinuousMap.compactOpen
    rw [ContinuousMap.compactOpen_eq, induced_generateFrom_eq]
    refine le_generateFrom ?_
    rintro _ ⟨_, ⟨K, hK, U, hU, rfl⟩, rfl⟩
    obtain ⟨L, hL, hLK⟩ := exists_compact_lift p hpc hpo hps K hK
    refine ⟨{ψ : PontryaginDual (G ⧸ k') | MapsTo ψ L U}, ?_, ?_⟩
    · exact (ContinuousMap.isOpen_setOfPred_mapsTo (X := G ⧸ k') (Y := Circle) hL hU).preimage
        (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous
    · ext χ
      change MapsTo (fun g => χ (p g)) L U ↔ MapsTo (fun x => χ x) K U
      constructor
      · intro h y hy
        rw [← hLK] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact h hx
      · intro h x hx
        exact h (by rw [← hLK]; exact ⟨x, hx, rfl⟩)
  -- annihilators correspond
  have hann : ∀ c : Subgroup (G ⧸ k), annihilator (c.comap p) = Φ '' annihilator c := by
    intro c
    ext χ
    constructor
    · intro hχ
      let ψ0 : G ⧸ k →* Circle := QuotientGroup.lift k
        (χ.toMonoidHom.comp (QuotientGroup.mk' k')) (fun g hg => by
          show χ (QuotientGroup.mk g) = 1
          apply hχ
          show p (QuotientGroup.mk g) ∈ c
          rw [hpmk, (QuotientGroup.eq_one_iff g).2 hg]; exact c.one_mem)
      have hψc : Continuous ψ0 :=
        continuous_coinduced_dom.2 (χ.continuous.comp continuous_quot_mk)
      refine ⟨⟨ψ0, hψc⟩, fun y hy => ?_, ?_⟩
      · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
        show χ (QuotientGroup.mk g) = 1
        exact hχ _ (show p (QuotientGroup.mk g) ∈ c from hy)
      · ext x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        rfl
    · rintro ⟨ψ, hψ, rfl⟩ x hx
      rw [hΦ]; exact hψ _ hx
  -- the range is open
  have hrange : IsOpen (range Φ) := by
    have hr : range Φ = annihilator p.ker := by
      have := hann ⊥
      rw [show annihilator (⊥ : Subgroup (G ⧸ k)) = univ by ext χ; simp [annihilator],
        image_univ] at this
      rw [← this]; rfl
    rw [hr]
    haveI : CompactSpace p.ker := isCompact_iff_compactSpace.mp hkerc
    let r := PontryaginDual.map (⟨p.ker.subtype, continuous_subtype_val⟩ : p.ker →ₜ* G ⧸ k')
    have : annihilator p.ker = r ⁻¹' {1} := by
      ext χ
      simp only [annihilator, mem_setOf_eq, mem_preimage, mem_singleton_iff]
      constructor
      · intro h; ext x; exact congrArg _ (h x x.2)
      · intro h x hx
        have := congrArg (fun f : PontryaginDual p.ker => f ⟨x, hx⟩) h
        exact this
    rw [this]
    exact (isOpen_discrete _).preimage (map_continuous r)
  have hopen : ∀ W, IsOpen W → IsOpen (Φ '' W) := by
    intro W hW
    obtain ⟨W'', hW'', rfl⟩ := isOpen_induced_iff.1 (hind.eq_induced ▸ hW)
    rw [image_preimage_eq_inter_range]
    exact hW''.inter hrange
  refine ⟨hs.1.preimage hpc, isCompactlyGenerated_comap p hpc hpo hps hkerc Γ hs.2.1, ⟨?_, ?_, ?_⟩,
    Subgroup.comap_mono hs.2.2.2⟩
  · exact hs.2.2.1.1.preimage hpc
  · rw [hann]; exact hopen _ hs.2.2.1.2.1
  · obtain ⟨A₁, hA₁, U, hUc, hUA, ⟨V, hV, hVU⟩, hcl⟩ := hs.2.2.1.2.2
    refine ⟨A₁.map Φ.toMonoidHom, ?_, Φ '' U, hUc.image (map_continuous Φ), ?_, ?_, ?_⟩
    · rw [Subgroup.coe_map, hann]; exact congrArg _ hA₁
    · exact image_mono hUA
    · rw [hind.nhds_eq_comap, map_one] at hV
      obtain ⟨V'', hV'', hV''V⟩ := hV
      refine ⟨V'', hV'', ?_⟩
      rintro y ⟨hyV, ⟨a, ha, rfl⟩⟩
      exact ⟨a, hVU ⟨hV''V hyV, ha⟩, rfl⟩
    · rw [← hcl, MonoidHom.map_closure]; rfl
