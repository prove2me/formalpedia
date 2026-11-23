-- Prove2me | solution 1 for GlobalTheory.GeomSurj.surjective_of_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:21.310735+00:00
-- url     : https://prove2.me/submissions/6b29ce7e-54db-453d-843f-2e87349742b8

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
namespace GlobalTheory.GeomSurj
theorem _root_.solution {k K : Type} [Field k] [Field K] [IsAlgClosed K] (σ : k →+* K)
    {P A : Scheme.{0}} (a : A ⟶ Sp k) [LocallyOfFiniteType a] (ψ : P ⟶ A)
    (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp K ⟶ A, x ≫ a = spMap σ → ∃ p : Sp K ⟶ P, x = p ≫ ψ) : Surjective ψ := by
  have hs : Surjective (spMap σ) := ⟨fun y ↦ by
    obtain ⟨z⟩ : Nonempty ↥(Sp K) := inferInstance
    exact ⟨z, Subsingleton.elim _ _⟩⟩
  have hJ : JacobsonSpace ↥(pullback a (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd a (spMap σ))
  have hZ : IsClosed ((pullback.fst a (spMap σ)) ⁻¹' Set.range ψ) :=
    hψ.preimage (pullback.fst a (spMap σ)).continuous
  have hsub : closedPoints ↥(pullback a (spMap σ)) ⊆
      (pullback.fst a (spMap σ)) ⁻¹' Set.range ψ := by
    intro z hz
    replace hz : IsClosed {z} := hz
    obtain ⟨p, hp⟩ := h (pointOfClosedPoint (pullback.snd a (spMap σ)) z hz ≫ pullback.fst _ _)
      (by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc])
    obtain ⟨w⟩ : Nonempty ↥(Sp K) := inferInstance
    refine ⟨p w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  have hall := closure_minimal hsub hZ
  rw [closure_closedPoints] at hall
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨z, rfl⟩ := (pullback.fst a (spMap σ)).surjective y
  exact hall (Set.mem_univ z)
end GlobalTheory.GeomSurj
