-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_lift_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:24.857743+00:00
-- url     : https://prove2.me/submissions/24cb007f-08a3-4af8-8f58-365a439c2d3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Theorems.Thm_GlobalTheory_exists_valuationSubring_lift_of_flat
import Theorems.Thm_GlobalTheory_specMap_apply_eq_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]
variable (K)
namespace GlobalTheory
theorem _root_.solution {Z : Scheme.{u}} (f : Z ⟶ Spec (.of O))
    [Flat f] [LocallyOfFiniteType f] {W : Set Z} (hW : IsOpen W)
    (hd : ∀ x : Z, f x ≠ closedPoint O → x ∈ closure W)
    {z : Z} (hz : IsClosed ({z} : Set Z)) (hzO : f z = closedPoint O) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (h : O →+* O') (_ : IsLocalHom h)
      (y : Spec (.of O') ⟶ Z),
      (∀ a : O, (h a : K') = algebraMap K K' (algebraMap O K a)) ∧
      y ≫ f = Spec.map (CommRingCat.ofHom h) ∧ y (closedPoint O') = z ∧
      ∀ t : Spec (.of K'), (Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y) t ∈ W := by
  obtain ⟨A, j, hj, x, rfl⟩ := Z.exists_Spec_apply_eq z
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (j ≫ f)
  have hflat : ψ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hψ]
    infer_instance
  have hft : ψ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]
    infer_instance
  let _ : Algebra O A := ψ.hom.toAlgebra
  have : Module.Flat O A := hflat
  have : Algebra.FiniteType O A := hft
  have hfj : ∀ p : Spec A, (f (j p)).asIdeal = p.asIdeal.comap (algebraMap O A) := by
    intro p
    rw [← Scheme.Hom.comp_apply, ← hψ]
    rfl
  have hx : x.asIdeal.IsMaximal := by
    have := hz.preimage j.continuous
    rw [← Set.image_singleton, Set.preimage_image_eq _ j.isOpenEmbedding.injective] at this
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal (R := A) x).mp this
  have hxO : x.asIdeal.comap (algebraMap O A) = maximalIdeal O :=
    (hfj x).symm.trans (congrArg PrimeSpectrum.asIdeal hzO)
  obtain ⟨K', _, _, _, O', φ, hφ, hφm, hφW⟩ := exists_valuationSubring_lift_of_flat (O := O) (K := K)
    (A := A) x.asIdeal hxO (hW.preimage j.continuous) (fun p hp => by
      have := hd (j p) fun e => hp ((hfj p).symm.trans (congrArg PrimeSpectrum.asIdeal e))
      exact j.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage this)
  have hcomap : (maximalIdeal O').comap (φ.comp ψ.hom) = maximalIdeal O := by
    rw [← Ideal.comap_comap, hφm]
    exact hxO
  refine ⟨K', inferInstance, inferInstance, inferInstance, O', φ.comp ψ.hom,
    ((local_hom_TFAE _).out 4 0).mp hcomap, Spec.map (CommRingCat.ofHom φ) ≫ j, hφ, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg j (PrimeSpectrum.ext hφm))
  · intro t
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      specMap_apply_eq_bot _ (IsFractionRing.injective O' K')]
    exact hφW
end GlobalTheory
