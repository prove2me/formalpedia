-- Prove2me | solution 1 for GlobalTheory.OntoSurj.surjective_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:22.720799+00:00
-- url     : https://prove2.me/submissions/52768278-c265-4e9d-8a53-d81331e6b600

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ProdSurjectiveGeometricPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AbelianSchemeSurjectiveOfOntoComplexPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.OntoSurj
namespace GlobalTheory.OntoSurj
theorem _root_.solution {R K : Type} [CommRing R] [Field K] [IsAlgClosed K] (σ : R →+* K)
    (hσ : Function.Injective σ) {P A : Scheme.{0}} (a : A ⟶ Sp R) [LocallyOfFiniteType a]
    (ha : IsOpenMap a) (ψ : P ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp K ⟶ A, x ≫ a = spMap σ → ∃ p : Sp K ⟶ P, x = p ≫ ψ) : Surjective ψ := by
  have hd : Dense (Set.range (spMap σ)) := by
    have : DenseRange (PrimeSpectrum.comap σ) := by
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot σ).mp hσ]
      exact bot_le
    exact this
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
  have hsub' : a ⁻¹' Set.range (spMap σ) ⊆ Set.range ψ := by
    rw [← Scheme.Pullback.range_fst]
    rintro _ ⟨z, rfl⟩
    exact hall (Set.mem_univ z)
  have hall' := closure_minimal hsub' hψ
  rw [(hd.preimage ha).closure_eq] at hall'
  exact ⟨fun y ↦ hall' (Set.mem_univ y)⟩
end GlobalTheory.OntoSurj
