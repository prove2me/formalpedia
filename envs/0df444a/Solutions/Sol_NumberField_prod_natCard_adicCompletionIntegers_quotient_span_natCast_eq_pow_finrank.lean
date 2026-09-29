-- Prove2me | solution 1 for NumberField.prod_natCard_adicCompletionIntegers_quotient_span_natCast_eq_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5a420c5a-4024-5332-8939-6e6410b18606

import Mathlib
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Theorems.Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_prod_natCard_adicCompletionIntegers_quotient_span_natCast_eq_pow_finrank

set_option autoImplicit false

namespace P2mS26C4a

open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 1600000 in

theorem natCard_quotient_span_natCast (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime) :
    Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(p : v.adicCompletionIntegers K)})
      = Nat.card (𝓞 K ⧸ v.asIdeal) ^ (Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal := by
  classical
  have hmapP0 : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hpO : ((p : v.adicCompletionIntegers K) : v.adicCompletion K) = (p : v.adicCompletion K) := by
    rw [← map_natCast (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) p]; rfl
  have hp0 : (p : v.adicCompletionIntegers K) ≠ 0 := by
    intro h
    have h1 : ((p : v.adicCompletionIntegers K) : v.adicCompletion K) = 0 := by rw [h]; rfl
    rw [hpO, ← map_natCast (algebraMap K (v.adicCompletion K)), map_eq_zero, Nat.cast_eq_zero] at h1
    exact hp.ne_zero h1

  have hval : Valued.v ((p : v.adicCompletionIntegers K) : v.adicCompletion K) = v.intValuation (p : 𝓞 K) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) v (p : 𝓞 K)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h
    rw [hpO, ← h]
    congr 1
    exact (map_natCast (algebraMap (𝓞 K) (v.adicCompletion K)) p).symm
  have hmem : ∀ j : ℕ, (p : v.adicCompletionIntegers K) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ j
      ↔ (p : 𝓞 K) ∈ v.asIdeal ^ j := by
    intro j
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← hval]
    exact HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow K v (p : v.adicCompletionIntegers K)

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (show Ideal.span {(p : v.adicCompletionIntegers K)} ≠ ⊥ by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  have hk' : Ideal.span {(p : v.adicCompletionIntegers K)} = IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ k := by
    rw [hk, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

  have hram : (Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal = k := by
    apply Ideal.ramificationIdx_spec
    · rw [hmapP0, Ideal.span_singleton_le_iff_mem, ← hmem, ← hk']
      exact Ideal.subset_span rfl
    · rw [hmapP0, Ideal.span_singleton_le_iff_mem, ← hmem]
      intro h
      have hle : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ k
          ≤ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (k + 1) := by
        rw [← hk', Ideal.span_singleton_le_iff_mem]; exact h
      have hlt : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (k + 1)
          < IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ k :=
        Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers K)) k
      exact absurd hle (not_le_of_gt hlt)
  rw [hram, hk', IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv.symm]

end P2mS26C4a

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution {K : Type*} [Field K]
    [NumberField K] {p : ℕ} (hp : p.Prime)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ v.asIdeal → v ∈ S) :
    ∏ v ∈ S, Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(p : v.adicCompletionIntegers K)})
      = p ^ Module.finrank ℚ K := by
  classical
  haveI hpfact : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hP0max : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hP0ne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  have hmapP0 : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (Ideal.span {(p : ℤ)})
      = Ideal.span {(p : NumberField.RingOfIntegers K)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hover : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ v.asIdeal → v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := fun v hv =>
    ⟨hP0max.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top)
      (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]; exact hv)⟩

  have hsplit : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(p : v.adicCompletionIntegers K)})
        = if (p : NumberField.RingOfIntegers K) ∈ v.asIdeal
          then p ^ ((Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal * (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal)
          else 1 := by
    intro v
    rw [P2mS26C4a.natCard_quotient_span_natCast K v hp]
    split_ifs with hv
    · haveI := hover v hv
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_eq_pow_inertiaDeg v.asIdeal hpZ,
        Int.natAbs_natCast, ← pow_mul, mul_comm]
    · have h0 : (Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal = 0 := by
        apply Ideal.ramificationIdx_spec
        · simp
        · rw [hmapP0, pow_one, Ideal.span_singleton_le_iff_mem]; exact hv
      rw [h0, pow_zero]
  simp_rw [hsplit, ← Finset.prod_filter, Finset.prod_pow_eq_pow_sum]
  congr 1

  rw [← Ideal.sum_ramification_inertia (R := ℤ) (NumberField.RingOfIntegers K) ℚ K hP0ne]
  refine Finset.sum_nbij (fun v => v.asIdeal) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro v hv
    rw [Finset.mem_filter] at hv
    rw [IsDedekindDomain.mem_primesOverFinset_iff hP0ne]
    exact ⟨v.isPrime, hover v hv.2⟩
  · intro v _ w _ h
    exact IsDedekindDomain.HeightOneSpectrum.ext h
  · intro P hP
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hP0ne] at hP
    obtain ⟨hPprime, hPover⟩ := hP
    have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hP0ne P
    have hpP : (p : NumberField.RingOfIntegers K) ∈ P := by
      have h1 : (p : ℤ) ∈ Ideal.under ℤ P := by
        rw [← hPover.over]; exact Ideal.mem_span_singleton_self _
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
      exact h1
    exact ⟨⟨P, hPprime, hPne⟩, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hS _ hpP, hpP⟩), rfl⟩

end S_NumberField_prod_natCard_adicCompletionIntegers_quotient_span_natCast_eq_pow_finrank
end P2MW
export P2MW.S_NumberField_prod_natCard_adicCompletionIntegers_quotient_span_natCast_eq_pow_finrank (solution)
