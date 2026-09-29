-- Prove2me | solution 1 for NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2fb4f9fb-24bf-59a7-8d5c-053a3cc970ec

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra

universe u

namespace MaxSpecial

section Top

variable {X : Type u} [TopologicalSpace X]

def IsMax (x : X) : Prop := ∀ x' : X, x' ⤳ x → x' = x

theorem isMax_iff_mem_genericPoints [QuasiSober X] [T0Space X] (x : X) :
    IsMax x ↔ x ∈ genericPoints X := by
  constructor
  · intro hx

    obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
    have hηx : η ⤳ x := hη.specializes mem_irreducibleComponent
    have := hx η hηx
    subst this
    change closure {η} ∈ irreducibleComponents X
    rw [hη.def]
    exact irreducibleComponent_mem_irreducibleComponents η
  · intro hx x' hx'

    have hZ : closure ({x} : Set X) ∈ irreducibleComponents X := hx
    have hsub : closure ({x} : Set X) ⊆ closure {x'} := by
      rw [← specializes_iff_closure_subset]; exact hx'
    have hle : closure ({x'} : Set X) ≤ closure {x} := hZ.2 isIrreducible_singleton.closure hsub
    have h1 : x' ⤳ x := hx'
    have h2 : x ⤳ x' := specializes_iff_closure_subset.mpr hle
    exact (h1.antisymm h2).eq

theorem finite_isMax [QuasiSober X] [T0Space X] [TopologicalSpace.NoetherianSpace X] :
    Set.Finite {x : X | IsMax x} := by
  have : {x : X | IsMax x} = genericPoints X := by
    ext x; exact isMax_iff_mem_genericPoints x
  rw [this]
  exact genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

theorem exists_isMax_specializes [QuasiSober X] [T0Space X] (z : X) : ∃ x : X, IsMax x ∧ x ⤳ z := by
  obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := z)) isClosed_irreducibleComponent
  refine ⟨η, (isMax_iff_mem_genericPoints η).mpr ?_, hη.specializes mem_irreducibleComponent⟩
  change closure {η} ∈ irreducibleComponents X
  rw [hη.def]
  exact irreducibleComponent_mem_irreducibleComponents z

variable (huniq : ∀ x : X, ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z = irreducibleComponent x)

include huniq in
theorem isMax_unique [QuasiSober X] [T0Space X] {x₁ x₂ z : X} (h₁ : IsMax x₁) (h₂ : IsMax x₂)
    (hz₁ : x₁ ⤳ z) (hz₂ : x₂ ⤳ z) : x₁ = x₂ := by
  rw [isMax_iff_mem_genericPoints] at h₁ h₂
  have e₁ := huniq z _ h₁ (specializes_iff_mem_closure.mp hz₁)
  have e₂ := huniq z _ h₂ (specializes_iff_mem_closure.mp hz₂)
  have : closure ({x₁} : Set X) = closure {x₂} := e₁.trans e₂.symm
  exact (isGenericPoint_closure.eq (this ▸ isGenericPoint_closure))

include huniq in

theorem exists_open_isolating [QuasiSober X] [T0Space X] [TopologicalSpace.NoetherianSpace X]
    {x : X} (hx : IsMax x) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ (∀ z ∈ V, x ⤳ z) ∧ (∀ z, x ⤳ z → z ∈ V) := by
  have hxg := (isMax_iff_mem_genericPoints x).mp hx
  have hZ : closure ({x} : Set X) ∈ irreducibleComponents X := hxg
  let B : Set X := ⋃ Z ∈ {Z ∈ irreducibleComponents X | Z ≠ closure {x}}, Z
  have hB : IsClosed B := by
    apply Set.Finite.isClosed_biUnion
    · exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
    · intro Z hZ; exact isClosed_of_mem_irreducibleComponents _ hZ.1
  refine ⟨Bᶜ, hB.isOpen_compl, ?_, ?_, ?_⟩
  · intro hxB
    obtain ⟨Z, hZmem, hxZ⟩ := Set.mem_iUnion₂.mp hxB
    have := huniq x Z hZmem.1 hxZ
    have := hZmem.2 (this.trans (huniq x _ hZ (subset_closure (Set.mem_singleton x))).symm)
    exact this
  · intro z hz

    have hc : irreducibleComponent z = closure {x} := by
      by_contra hne
      exact hz (Set.mem_iUnion₂.mpr ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, hne⟩,
        mem_irreducibleComponent⟩)
    exact specializes_iff_mem_closure.mpr (hc ▸ mem_irreducibleComponent)
  · intro z hxz hzB
    obtain ⟨Z, hZmem, hzZ⟩ := Set.mem_iUnion₂.mp hzB
    have e1 := huniq z Z hZmem.1 hzZ
    have e2 := huniq z _ hZ (specializes_iff_mem_closure.mp hxz)
    exact hZmem.2 (e1.trans e2.symm)

end Top

section SmoothField

theorem exists_preconnected_nhd {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ _root_.IsPreconnected (U : Set X) := by
  let B : Set X := ⋃ Z ∈ {Z ∈ irreducibleComponents X | x ∉ Z}, Z
  have hB : IsClosed B := by
    apply Set.Finite.isClosed_biUnion
    · exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
    · intro Z hZ; exact isClosed_of_mem_irreducibleComponents _ hZ.1
  refine ⟨⟨Bᶜ, hB.isOpen_compl⟩, fun h => ?_, ?_⟩
  · obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp h
    exact hZ.2 hxZ
  ·
    have hcover : (Bᶜ : Set X) = ⋃₀ {S | ∃ Z ∈ irreducibleComponents X, x ∈ Z ∧ S = Z ∩ Bᶜ} := by
      ext z
      constructor
      · intro hz
        refine ⟨irreducibleComponent z ∩ Bᶜ, ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z, ?_, rfl⟩,
          mem_irreducibleComponent, hz⟩
        by_contra hxZ
        exact hz (Set.mem_iUnion₂.mpr ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, hxZ⟩,
          mem_irreducibleComponent⟩)
      · rintro ⟨S, ⟨Z, -, -, rfl⟩, hzS⟩
        exact hzS.2
    change _root_.IsPreconnected (Bᶜ : Set X)
    rw [hcover]
    apply isPreconnected_sUnion x
    · rintro S ⟨Z, hZ, hxZ, rfl⟩
      exact ⟨hxZ, fun h => (Set.mem_iUnion₂.mp h).elim fun Z' hZ' => hZ'.1.2 hZ'.2⟩
    · rintro S ⟨Z, hZ, hxZ, rfl⟩

      have hZirr : IsPreirreducible Z := hZ.1.isPreirreducible
      have : IsPreirreducible (Z ∩ Bᶜ) := by
        intro u v hu hv ⟨a, ⟨haZ, haB⟩, hau⟩ ⟨b, ⟨hbZ, hbB⟩, hbv⟩
        obtain ⟨c, hcZ, ⟨hcu, hcB⟩, hcv, -⟩ := hZirr (u ∩ Bᶜ) (v ∩ Bᶜ) (hu.inter hB.isOpen_compl)
          (hv.inter hB.isOpen_compl) ⟨a, haZ, hau, haB⟩ ⟨b, hbZ, hbv, hbB⟩
        exact ⟨c, ⟨hcZ, hcB⟩, hcu, hcv⟩
      exact this.isPreconnected

theorem isDomain_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [LocallyOfFiniteType g] [CompactSpace X] (x : X) : IsDomain (X.presheaf.stalk x) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : IsNoetherian X := {}
  obtain ⟨U, hxU, hU⟩ := exists_preconnected_nhd x
  haveI : PreconnectedSpace (U : Scheme.{u}) := isPreconnected_iff_preconnectedSpace.mp hU
  haveI : Nonempty (U : Scheme.{u}) := ⟨⟨x, hxU⟩⟩
  have hint : IsIntegral (U : Scheme.{u}) :=
    AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace (U.ι ≫ g)

  haveI : IsDomain ((U : Scheme.{u}).presheaf.stalk ⟨x, hxU⟩) := inferInstance
  exact Function.Injective.isDomain (U.ι.stalkMap ⟨x, hxU⟩).hom
    (ConcreteCategory.injective_of_mono_of_preservesPullback (U.ι.stalkMap ⟨x, hxU⟩))

theorem unique_component_of_smooth {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [LocallyOfFiniteType g] [CompactSpace X] :
    ∀ x : X, ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z = irreducibleComponent x := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  intro x Z hZ hxZ
  exact (AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk (isDomain_stalk_of_smooth g) x).2 Z hZ hxZ

end SmoothField

theorem main
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Set.Finite {ξ : Y | f.base ξ = IsLocalRing.closedPoint R ∧
        ∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ} ∧
    (∀ y : Y, f.base y = IsLocalRing.closedPoint R →
      ∃! ξ : Y, (f.base ξ = IsLocalRing.closedPoint R ∧
        (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ)) ∧ ξ ⤳ y) ∧
    (∀ ξ : Y, f.base ξ = IsLocalRing.closedPoint R →
      (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ) →
      ∃ V : Y.Opens, ξ ∈ V ∧ (∀ y' : Y, f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V) ∧
        (∀ y' : Y, y' ∈ V → f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y') ∧
        (∀ y' : Y, f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y' → y' ∈ V)) := by
  set p₀ := IsLocalRing.closedPoint R with hp₀

  let Xk : Scheme.{u} := f.fiber p₀
  let ι : Xk ⟶ Y := f.fiberι p₀
  let g : Xk ⟶ Spec (CommRingCat.of ↑((Spec (CommRingCat.of R)).residueField p₀)) := f.fiberToSpecResidueField p₀
  have hemb : Topology.IsEmbedding ι.base := ι.isEmbedding
  have hrange : Set.range ι.base = {y : Y | f.base y = p₀} := by
    change Set.range (f.fiberι p₀) = _
    rw [Scheme.Hom.range_fiberι]; rfl
  have hS : IsClosed {y : Y | f.base y = p₀} := by
    change IsClosed (f.base ⁻¹' {p₀})
    exact IsClosed.preimage f.base.hom.continuous
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p₀).mpr (IsLocalRing.maximalIdeal.isMaximal R))
  have hcemb : Topology.IsClosedEmbedding ι.base := ⟨hemb, by rw [hrange]; exact hS⟩
  haveI : Smooth g := by
    change Smooth (pullback.snd f ((Spec (CommRingCat.of R)).fromSpecResidueField p₀))
    exact MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFiniteType g := by
    change LocallyOfFiniteType (pullback.snd f ((Spec (CommRingCat.of R)).fromSpecResidueField p₀))
    exact MorphismProperty.pullback_snd _ _ inferInstance
  haveI : IsLocallyNoetherian Xk := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : IsNoetherian Xk := {}
  have huniq := unique_component_of_smooth g

  have hmem : ∀ {y : Y}, f.base y = p₀ → ∃ x : Xk, ι.base x = y := fun {y} hy => by
    have : y ∈ Set.range ι.base := by rw [hrange]; exact hy
    exact this
  have hbase : ∀ x : Xk, f.base (ι.base x) = p₀ := fun x => by
    have : ι.base x ∈ Set.range ι.base := ⟨x, rfl⟩
    rw [hrange] at this; exact this
  have hspec : ∀ x x' : Xk, ι.base x ⤳ ι.base x' ↔ x ⤳ x' := fun x x' => hemb.isInducing.specializes_iff
  have hdict : ∀ x : Xk, IsMax x ↔
      (f.base (ι.base x) = p₀ ∧ ∀ y' : Y, y' ⤳ ι.base x → f.base y' = p₀ → y' = ι.base x) := by
    intro x
    constructor
    · intro hx
      refine ⟨hbase x, fun y' hy' hy'S => ?_⟩
      obtain ⟨x', rfl⟩ := hmem hy'S
      rw [hx x' ((hspec _ _).mp hy')]
    · rintro ⟨-, hx⟩ x' hx'
      exact hemb.injective (hx _ ((hspec _ _).mpr hx') (hbase x'))
  refine ⟨?_, ?_, ?_⟩
  ·
    apply ((finite_isMax (X := ↥Xk)).image ι.base).subset
    rintro ξ ⟨hξ, hmax⟩
    obtain ⟨x, rfl⟩ := hmem hξ
    exact ⟨x, (hdict x).mpr ⟨hξ, hmax⟩, rfl⟩
  ·
    intro y hy
    obtain ⟨z, rfl⟩ := hmem hy
    obtain ⟨x, hx, hxz⟩ := exists_isMax_specializes z
    refine ⟨ι.base x, ⟨(hdict x).mp hx, (hspec _ _).mpr hxz⟩, ?_⟩
    rintro ξ' ⟨hξ', hξ'z⟩
    obtain ⟨x', rfl⟩ := hmem hξ'.1
    rw [isMax_unique huniq ((hdict x').mpr hξ') hx ((hspec _ _).mp hξ'z) hxz]
  ·
    intro ξ hξ hmax
    obtain ⟨x, rfl⟩ := hmem hξ
    have hx : IsMax x := (hdict x).mpr ⟨hξ, hmax⟩
    obtain ⟨V₀, hV₀, hxV₀, hV₀spec, hspecV₀⟩ := exists_open_isolating huniq hx
    have hC : IsClosed (ι.base '' V₀ᶜ) := hcemb.isClosedMap _ hV₀.isClosed_compl
    refine ⟨⟨(ι.base '' V₀ᶜ)ᶜ, hC.isOpen_compl⟩, ?_, ?_, ?_, ?_⟩
    · rintro ⟨x', hx', hxx'⟩
      exact hx' (hemb.injective hxx' ▸ hxV₀)
    · intro y' hy' hy'C
      obtain ⟨x', -, rfl⟩ := hy'C
      exact hy' (hbase x')
    · intro y' hy'V hy'S
      obtain ⟨z, rfl⟩ := hmem hy'S
      have hz : z ∈ V₀ := by
        by_contra hz; exact hy'V ⟨z, hz, rfl⟩
      exact (hspec _ _).mpr (hV₀spec z hz)
    · intro y' hy'S hξy'
      obtain ⟨z, rfl⟩ := hmem hy'S
      rintro ⟨z', hz', hzz'⟩
      exact hz' (hemb.injective hzz' ▸ hspecV₀ z ((hspec _ _).mp hξy'))

end MaxSpecial

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Set.Finite {ξ : Y | f.base ξ = IsLocalRing.closedPoint R ∧
        ∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ} ∧
    (∀ y : Y, f.base y = IsLocalRing.closedPoint R →
      ∃! ξ : Y, (f.base ξ = IsLocalRing.closedPoint R ∧
        (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ)) ∧ ξ ⤳ y) ∧
    (∀ ξ : Y, f.base ξ = IsLocalRing.closedPoint R →
      (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ) →
      ∃ V : Y.Opens, ξ ∈ V ∧ (∀ y' : Y, f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V) ∧
        (∀ y' : Y, y' ∈ V → f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y') ∧
        (∀ y' : Y, f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y' → y' ∈ V)) :=
  MaxSpecial.main f

end S_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
end P2MW
export P2MW.S_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens (solution)
