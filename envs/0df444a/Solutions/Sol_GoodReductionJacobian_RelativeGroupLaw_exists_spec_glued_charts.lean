-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_spec_glued_charts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e621fb58-23bd-5e3c-8bbd-e235d66fce55

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_spec_glued_charts

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {R A' : Type u} [CommRing R] [IsLocalRing R] [CommRing A'] [IsLocalRing A']
    (φA : R →+* A') [IsLocalHom φA]
    {G N : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {gN : N ⟶ Spec (CommRingCat.of R)} (LN : RelativeGroupLaw R gN)
    {Φ : Type u} [AddCommGroup Φ]
    (e : Φ → (G ⟶ N)) (he : ∀ φ, IsOpenImmersion (e φ)) (hef : ∀ φ, e φ ≫ gN = f)
    (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    (hne : ∀ φ ψ, φ ≠ ψ → ∀ n ∈ Set.range (e φ).base ∩ Set.range (e ψ).base,
      gN.base n ≠ IsLocalRing.closedPoint R)
    (c : Φ → Φ → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hchart : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ ψ : Φ) (a b : SchemeHomOver s f),
        LN.mul s (NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩)
            (NeronModelInfra.schemeHomOverComp b ⟨e ψ, hef ψ⟩) =
          NeronModelInfra.schemeHomOverComp
            (L.mul s (L.mul s a b) (GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) (c φ ψ)))
            ⟨e (φ + ψ), hef (φ + ψ)⟩) :
    ∃ spec : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN → Φ,
      (∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN) (φ : Φ),
        spec s = φ ↔ ∃ a : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) f,
          NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩ = s) ∧
      (∀ s s' : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN,
        spec (LN.mul _ s s') = spec s + spec s') ∧
      Function.Surjective spec := by
  classical

  have hcov : ∀ x : N, ∃ (j : Φ) (y : G), (e j).base y = x := by
    intro x
    have hx : x ∈ (⋃ φ, Set.range (e φ).base) := by rw [hecov]; trivial
    obtain ⟨φ, y, hy⟩ := Set.mem_iUnion.mp hx
    exact ⟨φ, y, hy⟩
  let 𝒰 : Scheme.OpenCover.{u} N := Scheme.Cover.mkOfCovers Φ (fun _ => G) e hcov (fun j => he j)

  have huniq : ∀ s : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN,
      ∃! i : Φ, ∃ s' : Spec (CommRingCat.of A') ⟶ G, s' ≫ e i = s.1 := fun s =>
    AlgebraicGeometry.existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne φA gN 𝒰 hne s.1 s.2
  let spec : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN → Φ := fun s => (huniq s).choose
  have hspec : ∀ s, ∃ s' : Spec (CommRingCat.of A') ⟶ G, s' ≫ e (spec s) = s.1 := fun s => (huniq s).choose_spec.1
  have hspec_eq : ∀ s (φ : Φ), (∃ s' : Spec (CommRingCat.of A') ⟶ G, s' ≫ e φ = s.1) → spec s = φ := by
    intro s φ hφ
    exact ((huniq s).unique (hspec s) hφ)

  have hchar : ∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN) (φ : Φ),
      spec s = φ ↔ ∃ a : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) f,
        NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩ = s := by
    intro s φ
    constructor
    · rintro rfl
      obtain ⟨s', hs'⟩ := hspec s
      refine ⟨⟨s', ?_⟩, Subtype.ext (by simpa using hs')⟩
      rw [← hef (spec s), ← Category.assoc, hs', s.2]
    · rintro ⟨a, ha⟩
      exact hspec_eq s φ ⟨a.1, by simpa using congrArg Subtype.val ha⟩
  refine ⟨spec, hchar, ?_, ?_⟩
  ·
    intro s s'
    obtain ⟨a, ha⟩ := (hchar s (spec s)).mp rfl
    obtain ⟨b, hb⟩ := (hchar s' (spec s')).mp rfl
    apply (hchar _ _).mpr
    refine ⟨L.mul _ (L.mul _ a b) (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom φA))
      (Category.comp_id _) (c (spec s) (spec s'))), ?_⟩
    rw [← hchart, ha, hb]
  ·
    intro φ
    refine ⟨NeronModelInfra.schemeHomOverComp (L.one (Spec.map (CommRingCat.ofHom φA))) ⟨e φ, hef φ⟩, ?_⟩
    exact (hchar _ _).mpr ⟨L.one _, rfl⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_spec_glued_charts
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_spec_glued_charts (solution)
