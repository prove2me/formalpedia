-- Prove2me | solution 1 for MasulloGRH.isGoodSubgroup_inf_and_isStructuralPair_sup_inf
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:31:55.125352+00:00
-- url     : https://prove2.me/submissions/fc8e21d6-94a5-4c04-87fd-768fa7996f83

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_LCAGroup_pontryagin_duality

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_isGoodSubgroup_inf_and_isStructuralPair_sup_inf

open MasulloGRH

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

/-- The join of an open compactly generated subgroup and a compactly generated subgroup is
compactly generated. -/
theorem isCompactlyGeneratedSubgroup_sup {X : Type*} [CommGroup X] [TopologicalSpace X]
    {H₁ H₂ : Subgroup X} (h₁o : IsOpen (H₁ : Set X)) (h₁ : IsCompactlyGeneratedSubgroup H₁)
    (h₂ : IsCompactlyGeneratedSubgroup H₂) : IsCompactlyGeneratedSubgroup (H₁ ⊔ H₂) := by
  obtain ⟨U₁, hU₁c, hU₁H, ⟨V₁, hV₁, hV₁U⟩, hU₁cl⟩ := h₁
  obtain ⟨U₂, hU₂c, hU₂H, -, hU₂cl⟩ := h₂
  refine ⟨U₁ ∪ U₂, hU₁c.union hU₂c, ?_,
    ⟨V₁ ∩ H₁, Filter.inter_mem hV₁ (h₁o.mem_nhds H₁.one_mem), ?_⟩, ?_⟩
  · exact Set.union_subset (hU₁H.trans (SetLike.coe_subset_coe.mpr le_sup_left))
      (hU₂H.trans (SetLike.coe_subset_coe.mpr le_sup_right))
  · rintro y ⟨⟨hy1, hy2⟩, -⟩
    exact Or.inl (hV₁U ⟨hy1, hy2⟩)
  · rw [Subgroup.closure_union, hU₁cl, hU₂cl]

/-- `(k₁ ∩ k₂)^⊥ = k₁^⊥ k₂^⊥` when `k₁, k₂` are closed and `k₁^⊥` is open. -/
theorem annihilator_inf_eq {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {k₁ k₂ : Subgroup G}
    (hk₁ : IsClosed (k₁ : Set G)) (hk₂ : IsClosed (k₂ : Set G))
    {A₁ A₂ : Subgroup (PontryaginDual G)}
    (hA₁ : (A₁ : Set (PontryaginDual G)) = annihilator k₁)
    (hA₂ : (A₂ : Set (PontryaginDual G)) = annihilator k₂)
    (hA₁o : IsOpen (A₁ : Set (PontryaginDual G))) :
    ((A₁ ⊔ A₂ : Subgroup (PontryaginDual G)) : Set (PontryaginDual G)) =
      annihilator (k₁ ⊓ k₂) := by
  ext χ
  constructor
  · intro hχ
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hχ
    have hy' : y ∈ annihilator k₁ := hA₁ ▸ hy
    have hz' : z ∈ annihilator k₂ := hA₂ ▸ hz
    intro x hx
    change y x * z x = 1
    rw [hy' x (Subgroup.mem_inf.mp hx).1, hz' x (Subgroup.mem_inf.mp hx).2, mul_one]
  · intro hχ
    set H : Subgroup (PontryaginDual G) := A₁ ⊔ A₂ with hHdef
    have hHo : IsOpen (H : Set (PontryaginDual G)) := Subgroup.isOpen_mono le_sup_left hA₁o
    by_contra hχH
    have : DiscreteTopology (PontryaginDual G ⧸ H) := QuotientGroup.discreteTopology hHo
    have hq : ((χ : PontryaginDual G ⧸ H)) ≠ 1 := by
      rw [Ne, QuotientGroup.eq_one_iff]
      exact hχH
    obtain ⟨ψ, hψ⟩ := exists_char_ne_one (PontryaginDual G ⧸ H) hq
    let π : PontryaginDual G →ₜ* PontryaginDual G ⧸ H :=
      ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
    let Φ : PontryaginDual (PontryaginDual G) := ContinuousMonoidHom.comp ψ π
    have hΦH : ∀ η ∈ H, Φ η = 1 := by
      intro η hη
      change ψ ((η : PontryaginDual G ⧸ H)) = 1
      rw [(QuotientGroup.eq_one_iff η).mpr hη, map_one]
    obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality G
    set x : G := e.symm Φ with hxdef
    have hx : ∀ η : PontryaginDual G, η x = Φ η := by
      intro η
      rw [← he, hxdef, ContinuousMulEquiv.apply_symm_apply]
    have hx₁ : x ∈ k₁ := by
      refine mem_of_forall_annihilator hk₁ (fun η hη => ?_)
      rw [hx]
      apply hΦH
      apply Subgroup.mem_sup_left
      change η ∈ (A₁ : Set (PontryaginDual G))
      rw [hA₁]; exact hη
    have hx₂ : x ∈ k₂ := by
      refine mem_of_forall_annihilator hk₂ (fun η hη => ?_)
      rw [hx]
      apply hΦH
      apply Subgroup.mem_sup_right
      change η ∈ (A₂ : Set (PontryaginDual G))
      rw [hA₂]; exact hη
    have h1 : χ x = 1 := hχ x (Subgroup.mem_inf.mpr ⟨hx₁, hx₂⟩)
    rw [hx] at h1
    exact hψ h1

theorem isGoodSubgroup_inf {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {k₁ k₂ : Subgroup G}
    (h₁ : IsGoodSubgroup k₁) (h₂ : IsGoodSubgroup k₂) : IsGoodSubgroup (k₁ ⊓ k₂) := by
  obtain ⟨hk₁, hA₁o, A₁, hA₁, hA₁cg⟩ := h₁
  obtain ⟨hk₂, -, A₂, hA₂, hA₂cg⟩ := h₂
  have hA₁o' : IsOpen (A₁ : Set (PontryaginDual G)) := hA₁ ▸ hA₁o
  have heq := annihilator_inf_eq hk₁ hk₂ hA₁ hA₂ hA₁o'
  refine ⟨hk₁.inter hk₂, ?_, A₁ ⊔ A₂, heq,
    isCompactlyGeneratedSubgroup_sup hA₁o' hA₁cg hA₂cg⟩
  rw [← heq]
  exact Subgroup.isOpen_mono le_sup_left hA₁o'

end Sol_MasulloGRH_isGoodSubgroup_inf_and_isStructuralPair_sup_inf

open MasulloGRH Sol_MasulloGRH_isGoodSubgroup_inf_and_isStructuralPair_sup_inf in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] :
    (∀ k₁ k₂ : Subgroup G, IsGoodSubgroup k₁ → IsGoodSubgroup k₂ → IsGoodSubgroup (k₁ ⊓ k₂)) ∧
    (∀ Γ₁ k₁ Γ₂ k₂ : Subgroup G, IsStructuralPair Γ₁ k₁ → IsStructuralPair Γ₂ k₂ →
      IsStructuralPair (Γ₁ ⊔ Γ₂) (k₁ ⊓ k₂)) := by
  refine ⟨fun k₁ k₂ h₁ h₂ => isGoodSubgroup_inf h₁ h₂, ?_⟩
  intro Γ₁ k₁ Γ₂ k₂ h₁ h₂
  obtain ⟨hΓ₁o, hΓ₁cg, hk₁g, hk₁Γ₁⟩ := h₁
  obtain ⟨-, hΓ₂cg, hk₂g, -⟩ := h₂
  exact ⟨Subgroup.isOpen_mono le_sup_left hΓ₁o, isCompactlyGeneratedSubgroup_sup hΓ₁o hΓ₁cg hΓ₂cg,
    isGoodSubgroup_inf hk₁g hk₂g, inf_le_left.trans (hk₁Γ₁.trans le_sup_left)⟩
