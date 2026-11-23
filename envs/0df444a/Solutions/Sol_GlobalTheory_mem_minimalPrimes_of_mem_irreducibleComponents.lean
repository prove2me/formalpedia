-- Prove2me | solution 1 for GlobalTheory.mem_minimalPrimes_of_mem_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:16.690541+00:00
-- url     : https://prove2.me/submissions/b7d768a6-1238-4f22-b73e-66e1c356ddc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology Limits
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]
variable [IsDiscreteValuationRing O]
omit [IsIntegral Y] [LocallyOfFiniteType f] [Flat f]
namespace GlobalTheory
theorem _root_.solution {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S)
    {A : Type u} [CommRing A] [Algebra O A] {j : Spec (.of A) ⟶ Y} [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A)))
    {q : PrimeSpectrum A} (hq : IsGenericPoint (j q) (i '' Z)) :
    q.asIdeal ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes := by
  have key (p : PrimeSpectrum A) :
      j p ∈ Set.range i ↔ (maximalIdeal O).map (algebraMap O A) ≤ p.asIdeal := by
    rw [hr]
    change (j ≫ f) p = _ ↔ _
    rw [hj, Ideal.map_le_iff_le_comap]
    change PrimeSpectrum.comap (algebraMap O A) p = _ ↔ _
    rw [PrimeSpectrum.ext_iff]
    exact ⟨fun h ↦ h.ge, fun h ↦ ((maximalIdeal.isMaximal O).eq_of_le
      (Ideal.IsPrime.ne_top inferInstance) h).symm⟩
  refine ⟨⟨q.2, (key q).mp (Set.image_subset_range _ _ hq.mem)⟩, fun p hp hpq ↦ ?_⟩
  obtain ⟨s, hs⟩ := (key ⟨p, hp.1⟩).mpr hp.2
  have h₁ : j (⟨p, hp.1⟩ : PrimeSpectrum A) ⤳ j q :=
    ((PrimeSpectrum.le_iff_specializes ⟨p, hp.1⟩ q).mp hpq).map j.continuous
  have h₂ : Z ⊆ closure {s} := fun z hz ↦ by
    rw [← specializes_iff_mem_closure, ← hi.isInducing.specializes_iff, hs]
    exact h₁.trans (hq.specializes ⟨z, hz, rfl⟩)
  have h₃ : s ∈ Z := hZ.2 isIrreducible_singleton.closure h₂ (subset_closure rfl)
  have h₄ : j q ⤳ j (⟨p, hp.1⟩ : PrimeSpectrum A) := hq.specializes ⟨s, h₃, hs⟩
  exact (PrimeSpectrum.le_iff_specializes q ⟨p, hp.1⟩).mpr
    (j.isOpenEmbedding.isInducing.specializes_iff.mp h₄)
end GlobalTheory
