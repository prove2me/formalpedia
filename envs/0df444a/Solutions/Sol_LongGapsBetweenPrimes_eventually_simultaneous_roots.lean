-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_simultaneous_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:19:12.69266+00:00
-- url     : https://prove2.me/submissions/a933f387-83f6-4be0-9b5e-50b55fcdc0ec

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_mem_auxiliaryPrimes
import Theorems.Thm_LongGapsBetweenPrimes_prime_dvd_auxiliaryProduct
import Theorems.Thm_LongGapsBetweenPrimes_tendsto_sieveZ
import Theorems.Thm_LongGapsBetweenPrimes_tendsto_log_sieveZ
import Theorems.Thm_LongGapsBetweenPrimes_weightConstant_gt_one
import Theorems.Thm_LongGapsBetweenPrimes_eventually_sieve_coefficient_estimates
import Theorems.Thm_LongGapsBetweenPrimes_uncoveredBound_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_finite_simultaneous_roots
import Theorems.Thm_LongGapsBetweenPrimes_truncated_exponential_le
import Theorems.Thm_LongGapsBetweenPrimes_gramBound_le_simple
import Theorems.Thm_LongGapsBetweenPrimes_collisionBound_le_simple
import Theorems.Thm_LongGapsBetweenPrimes_uncoveredBound_le_simple
import Theorems.Thm_LongGapsBetweenPrimes_sieveZ_lower
import Theorems.Thm_LongGapsBetweenPrimes_sieveT_lower
import Theorems.Thm_LongGapsBetweenPrimes_intervalError_le_simple
import Theorems.Thm_LongGapsBetweenPrimes_eventually_sieve_beta_scale
import Theorems.Thm_LongGapsBetweenPrimes_eventually_simple_sieve_bounds
import Theorems.Thm_LongGapsBetweenPrimes_sieveDelta_lt_half

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ k : ℕ, (((k + 1 : ℕ) : ℝ)) ≤ sieveDelta * x →
    ∀ root : (p : PrimeIndex (sieveP x)) → Fin (k + 1) → Fin p.val,
    (∀ p, Function.Injective (root p)) →
    ∃ n < sieveT x, ∀ i : Fin (k + 1), ∃ p : PrimeIndex (sieveP x),
      residueVector (sieveP x) n p = root p i := by
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x / x)
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  filter_upwards [eventually_sieve_coefficient_estimates, eventually_sieve_beta_scale,
    eventually_simple_sieve_bounds weightConstant, Filter.eventually_ge_atTop (2 : ℝ),
    tendsto_sieveZ.eventually_ge_atTop 2, tendsto_log_sieveZ.eventually_ge_atTop 1,
    hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 12)]
    with x hcoeff hbeta ⟨hgram, htail, herr, hbad⟩ hx hZ hlogZ hlog
  intro k hk root hroot
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hC : 0 < weightConstant := zero_lt_one.trans weightConstant_gt_one
  have hn : ((k + 1 : ℕ) : ℝ) ≤ x := by
    have := mul_le_mul_of_nonneg_right sieveDelta_lt_half.le hx0.le
    linarith
  have hsize : ((k + 1 : ℕ) : ℝ) * weightConstant ≤ x / 16 := by
    calc
      _ ≤ (sieveDelta * x) * weightConstant := mul_le_mul_of_nonneg_right hk hC.le
      _ = x / 64 := by unfold sieveDelta; field_simp
      _ ≤ x / 16 := by linarith
  have hkn : (k : ℝ) ≤ x := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hn
    linarith
  have hksize : (k : ℝ) * weightConstant ≤ x / 16 := by
    have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    exact (mul_le_mul_of_nonneg_right this hC.le).trans hsize
  have hM := sieveZ_lower hx
  have hM' : x ^ 4 ≤ (sieveZ x : ℝ) := hM.trans (sub_le_self _ zero_le_one)
  have hmin : ∀ p ∈ (sieveP x).primeFactors, sieveZ x < p := by
    intro p hp
    obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact (mem_auxiliaryPrimes.mp (prime_dvd_auxiliaryProduct hp hdvd)).2.1
  have hT : 0 < sieveT x := by
    exact_mod_cast (half_pos (Real.exp_pos x)).trans_le (sieveT_lower hx)
  have herror := intervalError_le_simple hx (by
    have := (div_le_iff₀ hx0).mp hlog
    linarith)
  apply finite_simultaneous_roots hcoeff.2 hcoeff.1.le
    (show 1 ≤ sieveD x by unfold sieveD; exact Real.one_le_exp (by linarith))
    (by omega : 1 < sieveZ x) hT hmin root hroot
  · exact (add_le_add (truncated_exponential_le hx0 hcoeff.1.le hsize hbeta)
      (collisionBound_le_simple hx0 hn hM')).trans htail
  · exact (gramBound_le_simple hx1 hn hM hlogZ).trans hgram
  · exact herror.trans herr
  · have huncovered := uncoveredBound_le_simple hx1 hcoeff.1.le hkn hksize hbeta
      hM hlogZ hgram
    calc
      _ ≤ x * (((5 / 4) * (2 * weightConstant ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 6 +
          32 / x ^ 3) := by
        gcongr
        exact add_nonneg
          (uncoveredBound_nonneg k (sieveBeta x) weightConstant (sieveZ x) (Real.exp_nonneg _))
          (by positivity)
      _ = ((5 / 4) * (2 * weightConstant ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 5 +
          32 / x ^ 2 := by field_simp
      _ < 1 / 4 := hbad
end LongGapsBetweenPrimes
