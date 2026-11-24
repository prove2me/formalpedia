-- Prove2me | solution 1 for GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:17.366892+00:00
-- url     : https://prove2.me/submissions/9afe8903-2dca-415f-a3f4-84baa0b0125b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteOfFiniteQuotMapOfIsPrecomplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbedding
import Theorems.Thm_GlobalTheory_CompletionEmbed_algebraMap_injective
import Theorems.Thm_GlobalTheory_CompletionEmbed_finite_quot_span
import Theorems.Thm_GlobalTheory_AdicNoeth_isNoetherianRing_adicCompletion
import Theorems.Thm_GlobalTheory_finite_of_finite_quot_map_of_isPrecomplete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open IsLocalRing GlobalTheory.CompletionEmbed
namespace GlobalTheory.CompletionEmbed
theorem _root_.solution :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C]
      [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C →
      (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) →
      ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D),
        Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  intro p _ C _ _ _ _ hfin hp0 hpm hprime
  set A := AdicCompletion (maximalIdeal C) C
  haveI : IsNoetherianRing A := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _
  letI : Algebra ℤ_[p] A := (toCompletion p C hpm).toAlgebra
  have hJ : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A) = Ideal.span {(p : A)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  haveI : Finite (A ⧸ Ideal.span {(p : A)}) := finite_quot_span p C hp0 hprime
  have hne : Ideal.span {(p : A)} ≠ ⊤ := by
    intro h
    have hu : IsUnit (p : A) := Ideal.span_singleton_eq_top.mp h
    have hu' := hu.map (AdicCompletion.evalOneₐ (maximalIdeal C))
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk (maximalIdeal C)),
      Ideal.Quotient.eq_zero_iff_mem.mpr hpm] at hu'
    exact not_isUnit_zero hu'
  haveI : Module.Finite ℤ_[p] A := by
    refine GlobalTheory.finite_of_finite_quot_map_of_isPrecomplete ℤ_[p] A (maximalIdeal ℤ_[p]) ?_ ?_
    · rw [hJ]; exact hne
    · rw [hJ]; exact Module.Finite.of_finite
  have hnil : ¬ IsNilpotent (p : A) := by
    rintro ⟨n, hn⟩
    have h : algebraMap C A ((p : C) ^ n) = 0 := by rw [map_pow, map_natCast]; exact hn
    have h3 := (injective_iff_map_eq_zero _).mp (algebraMap_injective C) _ h
    exact hp0 (IsNilpotent.eq_zero ⟨n, h3⟩)
  obtain ⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal A, Q.IsPrime ∧ (p : A) ∉ Q := by
    by_contra h
    push_neg at h
    exact hnil (nilpotent_iff_mem_prime.mpr h)
  haveI := hQ
  refine ⟨A ⧸ Q, inferInstance, inferInstance, inferInstance, ?_,
    (Ideal.Quotient.mk Q).comp (algebraMap C A), ?_⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] Q).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[p] Q)
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hbot : Q.comap (algebraMap C A) = ⊥ := by
      by_contra hb
      have h1 := hprime _ (Ideal.comap_isPrime _ _) hb
      apply hpQ
      have h2 : (p : C) ∈ Q.comap (algebraMap C A) := by
        rw [h1]; exact hpm
      rw [Ideal.mem_comap, map_natCast] at h2
      exact h2
    have hx' : x ∈ Q.comap (algebraMap C A) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    rw [hbot] at hx'
    exact (Ideal.mem_bot).mp hx'
end GlobalTheory.CompletionEmbed
