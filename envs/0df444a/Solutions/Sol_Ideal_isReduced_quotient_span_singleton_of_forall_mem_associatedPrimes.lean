-- Prove2me | solution 1 for Ideal.isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1ea588b6-f11d-5402-95af-b3285d018143

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes

open IsLocalRing

theorem solution
    {A : Type*} [CommRing A] [IsNoetherianRing A] (x : A)
    (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ associatedPrimes A (A ⧸ Ideal.span {x}) →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) =
        maximalIdeal (Localization.AtPrime P)) :
    IsReduced (A ⧸ Ideal.span {x}) := by
  rw [isReduced_iff]
  intro a ha
  by_contra ha0
  obtain ⟨P, hP, hcol⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A a ha0
  haveI := hP.isPrime
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨n, hn⟩ := ha
  have han : a ^ n ∈ Ideal.span {x} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]; exact hn
  set S := Localization.AtPrime P with hS
  have hprime : (Ideal.map (algebraMap A S) (Ideal.span {x})).IsPrime := by
    rw [h P hP]; infer_instance
  have h1 : algebraMap A S a ∈ Ideal.map (algebraMap A S) (Ideal.span {x}) := by
    apply hprime.mem_of_pow_mem n
    rw [← map_pow]; exact Ideal.mem_map_of_mem _ han
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at h1
  obtain ⟨y, hy⟩ := h1
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y

  have h2 : algebraMap A S (b * x) = algebraMap A S (↑s * a) := by
    rw [map_mul, map_mul, ← hy]
    calc algebraMap A S b * algebraMap A S x
        = (algebraMap A S ↑s * IsLocalization.mk' S b s) * algebraMap A S x := by
          rw [IsLocalization.mk'_spec']
      _ = algebraMap A S ↑s * (IsLocalization.mk' S b s * algebraMap A S x) := by ring
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists P.primeCompl S).mp h2

  have hmem : (↑t * ↑s : A) ∈ P := by
    apply hcol
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have : ↑t * ↑s * a = (↑t * b) * x := by
      calc (↑t * ↑s * a : A) = ↑t * (↑s * a) := by ring
        _ = ↑t * (b * x) := ht.symm
        _ = ↑t * b * x := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  exact (P.primeCompl.mul_mem t.2 s.2) hmem

end S_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes
end P2MW
export P2MW.S_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes (solution)
