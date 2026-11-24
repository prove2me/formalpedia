-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_lift_of_exists_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:47:47.115194+00:00
-- url     : https://prove2.me/submissions/dc2e56b3-db7f-4e80-9019-ca8a9ce7783d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Theorems.Thm_GlobalTheory_exists_valuationSubring_of_height_le_one
import Theorems.Thm_GlobalTheory_exists_mem_height_map_le_one

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
namespace GlobalTheory
theorem _root_.solution {O K : Type*} {A : Type u} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra O A] [Algebra.FiniteType O A]
    (m : Ideal A) [hm : m.IsMaximal] (hmO : m.comap (algebraMap O A) = maximalIdeal O)
    {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (h : ∃ p ∈ U, p.asIdeal ≤ m ∧ p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : A →+* O'),
      (∀ a : O, (φ (algebraMap O A a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      (maximalIdeal O').comap φ = m ∧ PrimeSpectrum.comap φ ⊥ ∈ U := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπm : algebraMap O A π ∈ m := by
    rw [← Ideal.mem_comap, hmO, hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  obtain ⟨q, ⟨hqU, hqπ⟩, hqm, hht⟩ := exists_mem_height_map_le_one m
    (hU.inter (PrimeSpectrum.basicOpen (algebraMap O A π)).isOpen)
    (by
      obtain ⟨p, hpU, hpm, hp⟩ := h
      refine ⟨p, ⟨hpU, fun hπp => hp ?_⟩, hpm⟩
      refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
      exact hπp)
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  have hinj : Function.Injective (algebraMap O (A ⧸ q.asIdeal)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
    rw [map_mul, map_pow, (u.isUnit.map _).mul_right_eq_zero] at ha
    exact hqπ (Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero ha))
  obtain ⟨K', _, _, _, O', φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one (K := K)
    hinj (m.map (Ideal.Quotient.mk q.asIdeal)) hht π hπ.ne_zero (Ideal.mem_map_of_mem _ hπm)
  refine ⟨K', inferInstance, inferInstance, inferInstance, O', φ.comp (Ideal.Quotient.mk _),
    hφ, ?_, ?_⟩
  · rw [← Ideal.comap_comap, hφm, hcomap]
  · convert hqU
    ext x
    change φ (Ideal.Quotient.mk _ x) ∈ (⊥ : Ideal O') ↔ _
    rw [Ideal.mem_bot, map_eq_zero_iff φ hφi, Ideal.Quotient.eq_zero_iff_mem]
end GlobalTheory
