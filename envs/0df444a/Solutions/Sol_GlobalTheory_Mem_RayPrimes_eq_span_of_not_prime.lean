-- Prove2me | solution 1 for GlobalTheory.Mem.RayPrimes.eq_span_of_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:13.233676+00:00
-- url     : https://prove2.me/submissions/d3852d82-fa4b-4534-8e32-1a58e0fe284f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_two_le_absNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayPrimes
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.RayPrimes
theorem _root_.solution (h2 : Module.finrank ℚ K = 2) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ∃ p : ℕ, v.asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm v.asIdeal = p ^ 2 := by
  have hP := v.isPrime
  have h2' := two_le_absNorm v
  have hm := Ideal.absNorm_mem v.asIdeal
  obtain ⟨p, hp, hpv⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal := by
    rw [← Nat.prod_primeFactorsList (n := Ideal.absNorm v.asIdeal) (by omega), Nat.cast_list_prod] at hm
    obtain ⟨x, hx, hxv⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem hP
      (((Ideal.absNorm v.asIdeal).primeFactorsList.map Nat.cast : List (𝓞 K)) : Multiset (𝓞 K))).1
      (by simpa using hm)
    simp only [Multiset.mem_coe, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hxv⟩
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.dvd_span_singleton]; exact hpv
  have hmul : p ^ 2 = Ideal.absNorm v.asIdeal * Ideal.absNorm J := by rw [← hN, hJ, map_mul]
  obtain ⟨i, hi, hiv⟩ := (Nat.dvd_prime_pow hp).1 ⟨_, hmul⟩
  have hi2 : i = 2 := by
    interval_cases i
    · rw [pow_zero] at hiv; omega
    · rw [pow_one] at hiv; exact absurd (hiv ▸ hp) hv
    · rfl
  subst hi2
  refine ⟨p, ?_, hiv⟩
  have hJ1 : Ideal.absNorm J = 1 := by
    rw [hiv] at hmul
    exact (Nat.mul_eq_left (pow_ne_zero _ hp.ne_zero)).1 hmul.symm
  rw [Ideal.absNorm_eq_one_iff] at hJ1
  rw [hJ, hJ1, Ideal.mul_top]
end GlobalTheory.Mem.RayPrimes
