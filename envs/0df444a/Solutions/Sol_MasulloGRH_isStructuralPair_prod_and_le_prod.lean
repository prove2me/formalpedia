-- Prove2me | solution 1 for MasulloGRH.isStructuralPair_prod_and_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:37:47.650809+00:00
-- url     : https://prove2.me/submissions/c5893e7a-8604-4ab8-8aa6-7835a7ceea70

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_LCAGroup_pontryagin_duality

set_option autoImplicit false

namespace Sol_MasulloGRH_isStructuralPair_prod_and_le_prod

open MasulloGRH Topology

/-- Characters separate points (from Pontryagin duality). -/
theorem exists_char_ne_one (D : Type*) [CommGroup D] [TopologicalSpace D] [IsTopologicalGroup D]
    [T2Space D] [LocallyCompactSpace D] {x : D} (hx : x ≠ 1) :
    ∃ χ : PontryaginDual D, χ x ≠ 1 := by
  obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality D
  by_contra h
  push Not at h
  apply hx
  apply e.injective
  rw [map_one]
  refine PontryaginDual.ext (fun χ => ?_)
  rw [he, h χ, PontryaginDual.one_apply]

/-- For a closed subgroup `k`, `(k^⊥)^⊥ = k`. -/
theorem mem_of_forall_annihilator {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {k : Subgroup G}
    (hk : IsClosed (k : Set G)) {x : G} (hx : ∀ χ ∈ annihilator k, χ x = 1) : x ∈ k := by
  by_contra hxk
  have : IsClosed (k : Set G) := hk
  have hq : ((x : G ⧸ k)) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨η, hη⟩ := exists_char_ne_one (G ⧸ k) hq
  let π : G →ₜ* G ⧸ k := ⟨QuotientGroup.mk' k, QuotientGroup.continuous_mk⟩
  let χ : PontryaginDual G := ContinuousMonoidHom.comp η π
  have hχ : χ ∈ annihilator k := by
    intro y hy
    change η ((y : G ⧸ k)) = 1
    rw [(QuotientGroup.eq_one_iff y).mpr hy, map_one]
  exact hη (hx χ hχ)

/-- For an open subgroup `B` of the dual and `χ ∉ B`, some point of `B^⊥` is not killed by `χ`
(`(B^⊥)^⊥ = B` for open `B`). -/
theorem exists_point_of_not_mem {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    {B : Subgroup (PontryaginDual G)} (hBo : IsOpen (B : Set (PontryaginDual G)))
    {χ : PontryaginDual G} (hχ : χ ∉ B) :
    ∃ x : G, (∀ η ∈ B, η x = 1) ∧ χ x ≠ 1 := by
  have : DiscreteTopology (PontryaginDual G ⧸ B) := QuotientGroup.discreteTopology hBo
  have hq : ((χ : PontryaginDual G ⧸ B)) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hχ
  obtain ⟨ψ, hψ⟩ := exists_char_ne_one (PontryaginDual G ⧸ B) hq
  let π : PontryaginDual G →ₜ* PontryaginDual G ⧸ B :=
    ⟨QuotientGroup.mk' B, QuotientGroup.continuous_mk⟩
  let Φ : PontryaginDual (PontryaginDual G) := ContinuousMonoidHom.comp ψ π
  obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality G
  have hx : ∀ η : PontryaginDual G, η (e.symm Φ) = Φ η := by
    intro η
    rw [← he, ContinuousMulEquiv.apply_symm_apply]
  refine ⟨e.symm Φ, fun η hη => ?_, ?_⟩
  · rw [hx]
    change ψ ((η : PontryaginDual G ⧸ B)) = 1
    rw [(QuotientGroup.eq_one_iff η).mpr hη, map_one]
  · rw [hx]
    exact hψ

/-- A product of compactly generated subgroups is compactly generated. -/
theorem isCompactlyGeneratedSubgroup_prod {X Y : Type*} [CommGroup X] [TopologicalSpace X]
    [CommGroup Y] [TopologicalSpace Y] {H₁ : Subgroup X} {H₂ : Subgroup Y}
    (h₁ : IsCompactlyGeneratedSubgroup H₁) (h₂ : IsCompactlyGeneratedSubgroup H₂) :
    IsCompactlyGeneratedSubgroup (H₁.prod H₂) := by
  obtain ⟨U₁, hU₁c, hU₁H, ⟨V₁, hV₁, hV₁U⟩, hU₁cl⟩ := h₁
  obtain ⟨U₂, hU₂c, hU₂H, ⟨V₂, hV₂, hV₂U⟩, hU₂cl⟩ := h₂
  have h1U₁ : (1 : X) ∈ U₁ := hV₁U ⟨mem_of_mem_nhds hV₁, H₁.one_mem⟩
  have h1U₂ : (1 : Y) ∈ U₂ := hV₂U ⟨mem_of_mem_nhds hV₂, H₂.one_mem⟩
  have hsub : U₁ ×ˢ U₂ ⊆ ((H₁.prod H₂ : Subgroup (X × Y)) : Set (X × Y)) := by
    rw [Subgroup.coe_prod]
    exact Set.prod_mono hU₁H hU₂H
  refine ⟨U₁ ×ˢ U₂, hU₁c.prod hU₂c, hsub, ⟨V₁ ×ˢ V₂, ?_, ?_⟩, ?_⟩
  · show V₁ ×ˢ V₂ ∈ 𝓝 ((1 : X), (1 : Y))
    exact prod_mem_nhds hV₁ hV₂
  · rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, hab⟩
    rw [SetLike.mem_coe, Subgroup.mem_prod] at hab
    exact ⟨hV₁U ⟨ha, hab.1⟩, hV₂U ⟨hb, hab.2⟩⟩
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      exact hsub
    · rintro ⟨a, b⟩ hab
      rw [Subgroup.mem_prod] at hab
      have ha : (a, (1 : Y)) ∈ Subgroup.closure (U₁ ×ˢ U₂) := by
        have h0 : a ∈ Subgroup.closure U₁ := hU₁cl ▸ hab.1
        have h := Subgroup.mem_map_of_mem (MonoidHom.inl X Y) h0
        rw [MonoidHom.map_closure] at h
        refine Subgroup.closure_mono ?_ h
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨hu, h1U₂⟩
      have hb : ((1 : X), b) ∈ Subgroup.closure (U₁ ×ˢ U₂) := by
        have h0 : b ∈ Subgroup.closure U₂ := hU₂cl ▸ hab.2
        have h := Subgroup.mem_map_of_mem (MonoidHom.inr X Y) h0
        rw [MonoidHom.map_closure] at h
        refine Subgroup.closure_mono ?_ h
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨h1U₁, hu⟩
      have hm := mul_mem ha hb
      rw [Prod.mk_mul_mk, mul_one, one_mul] at hm
      exact hm

/-- The image of an open compactly generated subgroup under a continuous homomorphism admitting
a continuous section through `1` is open and compactly generated. -/
theorem isOpen_and_cg_map_of_section {X Y : Type*} [CommGroup X] [TopologicalSpace X]
    [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    (f : X →* Y) (hf : Continuous f) (s : Y → X) (hs : Continuous s) (hs1 : s 1 = 1)
    (hfs : ∀ y, f (s y) = y) {H : Subgroup X} (hHo : IsOpen (H : Set X))
    (hH : IsCompactlyGeneratedSubgroup H) :
    IsOpen ((H.map f : Subgroup Y) : Set Y) ∧ IsCompactlyGeneratedSubgroup (H.map f) := by
  obtain ⟨U, hUc, hUH, ⟨V, hV, hVU⟩, hUcl⟩ := hH
  have hW : s ⁻¹' (V ∩ (H : Set X)) ∈ 𝓝 (1 : Y) := by
    apply hs.continuousAt.preimage_mem_nhds
    rw [hs1]
    exact Filter.inter_mem hV (hHo.mem_nhds H.one_mem)
  have hWsub : s ⁻¹' (V ∩ (H : Set X)) ⊆ f '' U := fun y hy => ⟨s y, hVU hy, hfs y⟩
  refine ⟨?_, f '' U, hUc.image hf, ?_, ⟨s ⁻¹' (V ∩ (H : Set X)), hW, fun y hy => hWsub hy.1⟩, ?_⟩
  · apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    refine Filter.mem_of_superset hW ?_
    intro y hy
    exact ⟨s y, hy.2, hfs y⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_map_of_mem f (hUH hu)
  · rw [← MonoidHom.map_closure, hUcl]

/-- Part (1): the annihilator of `k₁ × k₂` is the image of `k₁^⊥ × k₂^⊥`, hence open and
compactly generated. -/
theorem isGoodSubgroup_prod {G₁ G₂ : Type*} [CommGroup G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    {k₁ : Subgroup G₁} {k₂ : Subgroup G₂} (h₁ : IsGoodSubgroup k₁) (h₂ : IsGoodSubgroup k₂) :
    IsGoodSubgroup (k₁.prod k₂) := by
  obtain ⟨hk₁, hA₁o, A₁, hA₁, hA₁cg⟩ := h₁
  obtain ⟨hk₂, hA₂o, A₂, hA₂, hA₂cg⟩ := h₂
  have hA₁o' : IsOpen (A₁ : Set (PontryaginDual G₁)) := hA₁ ▸ hA₁o
  have hA₂o' : IsOpen (A₂ : Set (PontryaginDual G₂)) := hA₂ ▸ hA₂o
  let Φ : PontryaginDual G₁ × PontryaginDual G₂ →* PontryaginDual (G₁ × G₂) :=
    MonoidHom.coprod (PontryaginDual.map (ContinuousMonoidHom.fst G₁ G₂)).toMonoidHom
      (PontryaginDual.map (ContinuousMonoidHom.snd G₁ G₂)).toMonoidHom
  have hΦ : ∀ p : PontryaginDual G₁ × PontryaginDual G₂, ∀ x : G₁ × G₂,
      Φ p x = p.1 x.1 * p.2 x.2 := fun _ _ => rfl
  have hΦc : Continuous Φ := by
    show Continuous fun p : PontryaginDual G₁ × PontryaginDual G₂ =>
      PontryaginDual.map (ContinuousMonoidHom.fst G₁ G₂) p.1 *
        PontryaginDual.map (ContinuousMonoidHom.snd G₁ G₂) p.2
    exact ((PontryaginDual.map _).continuous.comp continuous_fst).mul
      ((PontryaginDual.map _).continuous.comp continuous_snd)
  let s : PontryaginDual (G₁ × G₂) → PontryaginDual G₁ × PontryaginDual G₂ := fun χ =>
    (PontryaginDual.map (ContinuousMonoidHom.inl G₁ G₂) χ,
      PontryaginDual.map (ContinuousMonoidHom.inr G₁ G₂) χ)
  have hsc : Continuous s :=
    (PontryaginDual.map _).continuous.prodMk (PontryaginDual.map _).continuous
  have hs1 : s 1 = 1 := by
    show (PontryaginDual.map (ContinuousMonoidHom.inl G₁ G₂) 1,
      PontryaginDual.map (ContinuousMonoidHom.inr G₁ G₂) 1) = (1, 1)
    rw [map_one, map_one]
  have hΦs : ∀ χ, Φ (s χ) = χ := by
    intro χ
    refine PontryaginDual.ext (fun x => ?_)
    rw [hΦ]
    show χ (x.1, 1) * χ (1, x.2) = χ x
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hHo : IsOpen ((A₁.prod A₂ : Subgroup _) : Set (PontryaginDual G₁ × PontryaginDual G₂)) := by
    rw [Subgroup.coe_prod]
    exact hA₁o'.prod hA₂o'
  obtain ⟨hmo, hmcg⟩ := isOpen_and_cg_map_of_section Φ hΦc s hsc hs1 hΦs hHo
    (isCompactlyGeneratedSubgroup_prod hA₁cg hA₂cg)
  have heq : (((A₁.prod A₂).map Φ : Subgroup (PontryaginDual (G₁ × G₂))) :
      Set (PontryaginDual (G₁ × G₂))) = annihilator (k₁.prod k₂) := by
    ext χ
    constructor
    · rintro ⟨p, hp, rfl⟩ x hx
      rw [SetLike.mem_coe, Subgroup.mem_prod] at hp
      rw [Subgroup.mem_prod] at hx
      have hp1 : p.1 ∈ annihilator k₁ := hA₁ ▸ hp.1
      have hp2 : p.2 ∈ annihilator k₂ := hA₂ ▸ hp.2
      rw [hΦ, hp1 _ hx.1, hp2 _ hx.2, mul_one]
    · intro hχ
      refine ⟨s χ, ?_, hΦs χ⟩
      rw [SetLike.mem_coe, Subgroup.mem_prod]
      constructor
      · change PontryaginDual.map (ContinuousMonoidHom.inl G₁ G₂) χ ∈
          (A₁ : Set (PontryaginDual G₁))
        rw [hA₁]
        intro a ha
        exact hχ (a, 1) (Subgroup.mem_prod.mpr ⟨ha, k₂.one_mem⟩)
      · change PontryaginDual.map (ContinuousMonoidHom.inr G₁ G₂) χ ∈
          (A₂ : Set (PontryaginDual G₂))
        rw [hA₂]
        intro b hb
        exact hχ (1, b) (Subgroup.mem_prod.mpr ⟨k₁.one_mem, hb⟩)
  refine ⟨?_, ?_, (A₁.prod A₂).map Φ, heq, hmcg⟩
  · rw [Subgroup.coe_prod]
    exact hk₁.prod hk₂
  · rw [← heq]
    exact hmo

/-- Part (2), one factor at a time: from a structural pair `(Γ, k)` of `G` and a retraction
`p ∘ j = id` onto `H`, the pair `(p(Γ), j⁻¹(k))` is structural in `H`. -/
theorem isStructuralPair_map_comap {G H : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (p : G →ₜ* H) (j : H →ₜ* G) (hpj : ∀ x, p (j x) = x) {Γ k : Subgroup G}
    (h : IsStructuralPair Γ k) :
    IsStructuralPair (Γ.map p.toMonoidHom) (k.comap j.toMonoidHom) := by
  obtain ⟨hΓo, hΓcg, ⟨hk, hAo, A, hA, hAcg⟩, hkΓ⟩ := h
  have hAo' : IsOpen (A : Set (PontryaginDual G)) := hA ▸ hAo
  obtain ⟨hΓ'o, hΓ'cg⟩ := isOpen_and_cg_map_of_section p.toMonoidHom p.continuous j j.continuous
    (map_one j) hpj hΓo hΓcg
  let f : PontryaginDual G →* PontryaginDual H := (PontryaginDual.map j).toMonoidHom
  let s : PontryaginDual H → PontryaginDual G := PontryaginDual.map p
  have hfs : ∀ η, f (s η) = η := by
    intro η
    refine PontryaginDual.ext (fun x => ?_)
    show η (p (j x)) = η x
    rw [hpj]
  obtain ⟨hBo, hBcg⟩ := isOpen_and_cg_map_of_section f (PontryaginDual.map j).continuous s
    (PontryaginDual.map p).continuous (map_one _) hfs hAo' hAcg
  have heq : ((A.map f : Subgroup (PontryaginDual H)) : Set (PontryaginDual H)) =
      annihilator (k.comap j.toMonoidHom) := by
    ext χ
    constructor
    · rintro ⟨η, hη, rfl⟩ x hx
      have hη' : η ∈ annihilator k := hA ▸ hη
      exact hη' (j x) hx
    · intro hχ
      by_contra hχB
      obtain ⟨x, hxB, hχx⟩ := exists_point_of_not_mem hBo hχB
      apply hχx
      apply hχ x
      show j x ∈ k
      refine mem_of_forall_annihilator hk (fun η hη => ?_)
      have hη' : η ∈ A := by
        change η ∈ (A : Set (PontryaginDual G))
        rw [hA]
        exact hη
      exact hxB (f η) (Subgroup.mem_map_of_mem f hη')
  refine ⟨hΓ'o, hΓ'cg, ⟨?_, ?_, A.map f, heq, hBcg⟩, ?_⟩
  · rw [Subgroup.coe_comap]
    exact hk.preimage j.continuous
  · rw [← heq]
    exact hBo
  · intro x hx
    refine ⟨j x, hkΓ hx, ?_⟩
    exact hpj x

end Sol_MasulloGRH_isStructuralPair_prod_and_le_prod

open MasulloGRH Sol_MasulloGRH_isStructuralPair_prod_and_le_prod in
theorem solution
    (G₁ G₂ : Type*) [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
    [LocallyCompactSpace G₁] [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [T2Space G₂] [LocallyCompactSpace G₂] :
    (∀ (Γ₁ k₁ : Subgroup G₁) (Γ₂ k₂ : Subgroup G₂), IsStructuralPair Γ₁ k₁ →
        IsStructuralPair Γ₂ k₂ → IsStructuralPair (Γ₁.prod Γ₂) (k₁.prod k₂)) ∧
    ∀ Γ k : Subgroup (G₁ × G₂), IsStructuralPair Γ k →
      ∃ (Γ₁ k₁ : Subgroup G₁) (Γ₂ k₂ : Subgroup G₂), IsStructuralPair Γ₁ k₁ ∧
        IsStructuralPair Γ₂ k₂ ∧ Γ ≤ Γ₁.prod Γ₂ ∧ k₁.prod k₂ ≤ k := by
  refine ⟨?_, ?_⟩
  · intro Γ₁ k₁ Γ₂ k₂ h₁ h₂
    obtain ⟨hΓ₁o, hΓ₁cg, hk₁g, hk₁Γ₁⟩ := h₁
    obtain ⟨hΓ₂o, hΓ₂cg, hk₂g, hk₂Γ₂⟩ := h₂
    refine ⟨?_, isCompactlyGeneratedSubgroup_prod hΓ₁cg hΓ₂cg, isGoodSubgroup_prod hk₁g hk₂g,
      Subgroup.prod_mono hk₁Γ₁ hk₂Γ₂⟩
    rw [Subgroup.coe_prod]
    exact hΓ₁o.prod hΓ₂o
  · intro Γ k h
    have hkΓ : k ≤ Γ := h.2.2.2
    refine ⟨Γ.map (ContinuousMonoidHom.fst G₁ G₂).toMonoidHom,
      k.comap (ContinuousMonoidHom.inl G₁ G₂).toMonoidHom,
      Γ.map (ContinuousMonoidHom.snd G₁ G₂).toMonoidHom,
      k.comap (ContinuousMonoidHom.inr G₁ G₂).toMonoidHom,
      isStructuralPair_map_comap _ _ (fun _ => rfl) h,
      isStructuralPair_map_comap _ _ (fun _ => rfl) h, ?_, ?_⟩
    · intro z hz
      rw [Subgroup.mem_prod]
      exact ⟨Subgroup.mem_map_of_mem _ hz, Subgroup.mem_map_of_mem _ hz⟩
    · rintro ⟨a, b⟩ hab
      rw [Subgroup.mem_prod] at hab
      have ha : ((a, (1 : G₂)) : G₁ × G₂) ∈ k := hab.1
      have hb : (((1 : G₁), b) : G₁ × G₂) ∈ k := hab.2
      have hm := mul_mem ha hb
      rw [Prod.mk_mul_mk, mul_one, one_mul] at hm
      exact hm
