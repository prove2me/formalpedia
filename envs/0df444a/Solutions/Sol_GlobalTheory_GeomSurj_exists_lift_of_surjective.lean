-- Prove2me | solution 1 for GlobalTheory.GeomSurj.exists_lift_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:50.394773+00:00
-- url     : https://prove2.me/submissions/e0d57ce5-64b3-448f-8bdc-2c2803a196a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ProdSurjectiveGeometricPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.GeomSurj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open scoped CategoryTheory.Obj
namespace GlobalTheory.GeomSurj
namespace _root_.GlobalTheory.GeomSurj
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ A) :
    ∃ p : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ P, x = p ≫ ψ := by
  have hΩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω = Spec (CommRingCat.of Ω) := rfl
  haveI : JacobsonSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : JacobsonSpace (pullback ψ x :) := LocallyOfFiniteType.jacobsonSpace (pullback.snd ψ x)
  obtain ⟨q₀, -⟩ := (pullback.snd ψ x).surjective (Classical.arbitrary _)
  obtain ⟨q, hq⟩ : (closedPoints (pullback ψ x :)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hc := closure_closedPoints (X := (pullback ψ x :))
    rw [h, closure_empty] at hc
    exact (hc ▸ Set.mem_univ q₀ : q₀ ∈ (∅ : Set _))
  haveI : LocallyOfFiniteType ((pullback ψ x).fromSpecResidueField q) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hq
  let g : Spec ((pullback ψ x).residueField q) ⟶ Spec (CommRingCat.of Ω) :=
    (pullback ψ x).fromSpecResidueField q ≫ pullback.snd ψ x
  have hg : LocallyOfFiniteType (Spec.map (Spec.preimage g)) := by
    rw [Spec.map_preimage]; dsimp only [g]; infer_instance
  have hft := HasRingHomProperty.Spec_iff.mp hg
  set f := Spec.preimage g with hf
  letI : Algebra Ω ((pullback ψ x).residueField q) := f.hom.toAlgebra
  haveI : Algebra.FiniteType Ω ((pullback ψ x).residueField q) := hft
  haveI : Module.Finite Ω ((pullback ψ x).residueField q) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  let φ : (pullback ψ x).residueField q →ₐ[Ω] Ω := IsAlgClosed.lift
  have key : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g = 𝟙 _ := by
    rw [← Spec.map_preimage g, ← hf, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of Ω)
    ext a
    exact φ.commutes a
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullback ψ x).fromSpecResidueField q ≫
    pullback.fst ψ x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc (Scheme.fromSpecResidueField _ _), ← Category.assoc]
  change x = (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g) ≫ x
  rw [key, Category.id_comp]
end _root_.GlobalTheory.GeomSurj
end GlobalTheory.GeomSurj
