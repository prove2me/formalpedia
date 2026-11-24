-- Prove2me | solution 1 for GlobalTheory.exists_unit_at_prime_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:50.483794+00:00
-- url     : https://prove2.me/submissions/a6a253d2-e67a-40c7-a706-03f2c4e05bbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitDenominatorIntegral

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
theorem _root_.solution (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (T : Set K) (d : 𝓞 K) (hd : d ≠ 0)
    (hdT : ∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) (hPT : ∀ t ∈ T, P.valuation K t ≤ 1) :
    ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) := by
  have hspan : Ideal.span {d} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  have hirr : Irreducible P.asIdeal := (Ideal.prime_of_isPrime P.ne_bot P.isPrime).irreducible
  obtain ⟨a, J, hPJ, hdJ⟩ := WfDvdMonoid.max_power_factor hspan hirr
  have hJP : ¬ J ≤ P.asIdeal := fun h => hPJ (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.mp hJP
  have hsJ' : J ∣ Ideal.span {s} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsJ)
  have hvPs : P.valuation K (s : K) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    refine le_antisymm (P.intValuation_le_one s) (not_lt.mp fun h => hsP ?_)
    rw [HeightOneSpectrum.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton] at h
    exact h

  have hQ : ∀ Q : HeightOneSpectrum (𝓞 K), Q ≠ P → Q.intValuation s ≤ Q.intValuation d := by
    intro Q hQP
    have hQd : Q.intValuation d = WithZero.exp (-((Associates.mk Q.asIdeal).count
        (Associates.mk (Ideal.span {d})).factors : ℤ)) := by
      rw [HeightOneSpectrum.intValuation_def, if_neg hd]
    set n := (Associates.mk Q.asIdeal).count (Associates.mk (Ideal.span {d})).factors
    have hdiv : Q.asIdeal ^ n ∣ Ideal.span {d} :=
      (Q.intValuation_le_pow_iff_dvd d n).mp (le_of_eq hQd)
    have hne : Q.asIdeal ≠ P.asIdeal := fun h => hQP (HeightOneSpectrum.ext h)
    have hcop : IsCoprime Q.asIdeal P.asIdeal :=
      Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne Q.isMaximal P.isMaximal hne)
    have hcopn : IsCoprime (Q.asIdeal ^ n) (P.asIdeal ^ a) := hcop.pow
    rw [hdJ] at hdiv
    have hQJ : Q.asIdeal ^ n ∣ J := hcopn.dvd_of_dvd_mul_left hdiv
    rw [hQd]
    exact (Q.intValuation_le_pow_iff_dvd s n).mpr (hQJ.trans hsJ')
  refine ⟨s, hvPs, fun t ht => ?_⟩
  have hdt : (d : K) * t ∈ (algebraMap (𝓞 K) K).range := ⟨⟨_, hdT t ht⟩, rfl⟩
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((s : K) * t) (by
    intro Q
    by_cases hQP : Q = P
    · subst hQP
      rw [map_mul, hvPs, one_mul]; exact hPT t ht
    · obtain ⟨z, hz⟩ := hdt
      have h1 : Q.valuation K ((d : K) * t) ≤ 1 := by
        rw [← hz]; exact Q.valuation_le_one z
      rw [map_mul] at h1 ⊢
      calc Q.valuation K (s : K) * Q.valuation K t ≤ Q.valuation K (d : K) * Q.valuation K t := by
            gcongr
            rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
            exact hQ Q hQP
        _ ≤ 1 := h1)
  rw [← hy]
  exact RingOfIntegers.isIntegral_coe y
end GlobalTheory
