-- Prove2me | solution 1 for GlobalTheory.valuation_embedding_generator_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:54.65558+00:00
-- url     : https://prove2.me/submissions/ecf2d10d-2da1-43f8-9459-430531b0ba53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationEmbeddingGeneratorEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime →
      (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal →
      ∀ (α : 𝓞 K) (h : ℕ), Ideal.span {α} = P.asIdeal ^ h →
      ∀ σ : K →+* ℂ, A.valuation (σ (α : K)) = 1 := by
  intro K _ _ A p _ hpA P hpP α h hα σ
  set f := ringOfIntegersToValuationSubring A σ with hf
  have hfx : ∀ x : 𝓞 K, ((f x : A) : ℂ) = σ (x : K) := fun x => rfl
  set Q : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime f (IsLocalRing.maximalIdeal A)
  have hQne : Q ≠ ⊤ := hQp.ne_top
  have hmem : ∀ x : 𝓞 K, x ∈ Q ↔ A.valuation (σ (x : K)) < 1 := by
    intro x
    rw [hQ, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hfx]
  have hpQ : (p : 𝓞 K) ∈ Q := by
    rw [hmem]
    have : σ (((p : 𝓞 K) : K)) = (p : ℂ) := by simp
    rw [this]
    exact (ValuationSubring.mem_nonunits_iff A).mp hpA
  refine le_antisymm ?_ ?_
  · exact (ValuationSubring.valuation_le_one_iff A _).mpr (ringOfIntegers_map_mem_valuationSubring A σ α)
  · by_contra hlt
    push_neg at hlt
    have hαQ : α ∈ Q := (hmem α).mpr hlt
    have hspan : P.asIdeal ^ h ≤ Q := by
      rw [← hα, Ideal.span_singleton_le_iff_mem]
      exact hαQ
    have hPQ : P.asIdeal ≤ Q := Ideal.IsPrime.le_of_pow_le hspan
    have hPeq : P.asIdeal = Q := P.isMaximal.eq_of_le hQne hPQ
    exact hpP (hPeq ▸ hpQ)
end GlobalTheory
