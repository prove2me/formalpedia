-- Prove2me | solution 1 for OAI.ShortEgyptian.scalePrimes_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:33:16.715203+00:00
-- url     : https://prove2.me/submissions/c70cbb16-90ce-45b8-947d-4027d5d31b59

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/PrimeLists.lean:L138-L170
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.scalePrimes_card. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Theorems.Thm_OAI_ShortEgyptian_centralBinom_le_with_prime_count

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeLists ----
namespace OAI

namespace ShortEgyptian

open Finset
theorem dyadic_prime_log_lower (n : ℕ) (hn : 4 ≤ n) :
    (n:ℝ)/3*Real.log 4 ≤ Real.log n + Real.sqrt (2*(n:ℝ))*Real.log (2*(n:ℝ)) +
      ((dyadicPrimes n).card:ℝ)*Real.log (2*(n:ℝ)) := by
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hbin : (0:ℝ) < n.centralBinom := by exact_mod_cast n.centralBinom_pos
  have hlow := Real.log_le_log (by positivity : (0:ℝ)<(4:ℝ)^n)
    (show (4:ℝ)^n ≤ (n:ℝ)*n.centralBinom by exact_mod_cast (Nat.four_pow_lt_mul_centralBinom n hn).le)
  rw [Real.log_pow,Real.log_mul hnR.ne' hbin.ne'] at hlow
  have hup := Real.log_le_log hbin (show (n.centralBinom:ℝ) ≤
    (2*(n:ℝ))^Nat.sqrt (2*n)*4^(2*n/3)*(2*(n:ℝ))^(dyadicPrimes n).card by
      exact_mod_cast centralBinom_le_with_prime_count n (by omega))
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow] at hup
  have hsqrt : (Nat.sqrt (2*n):ℝ) ≤ Real.sqrt (2*(n:ℝ)) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Real.nat_sqrt_le_real_sqrt (a := 2*n))
  have hdiv : (↑(2*n/3):ℝ) ≤ 2*(n:ℝ)/3 := by
    exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := 2*n) (n := 3))
  have hlog2n : 0 ≤ Real.log (2*(n:ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*n))
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 := mul_le_mul_of_nonneg_right hsqrt hlog2n
  have h2 := mul_le_mul_of_nonneg_right hdiv hlog4
  linarith

theorem dyadic_prime_count_lower (n : ℕ) (hn : 4 ≤ n) (hl : 1 ≤ Real.log n)
    (hsmall : 30*Real.log n ≤ Real.sqrt n) :
    (n:ℝ)/(20*Real.log n) ≤ ((dyadicPrimes n).card:ℝ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
  have hl0 : 0 < Real.log n := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hlog4 : (1:ℝ) ≤ Real.log 4 := by
    have hh : Real.log (4:ℝ) = 2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    rw [hh]; linarith [Real.log_two_gt_d9]
  have hlog2n : Real.log (2*(n:ℝ)) ≤ 2*Real.log n := by
    rw [Real.log_mul (by norm_num) hn0.ne']; linarith
  have hsqrt : Real.sqrt (2*(n:ℝ)) ≤ 2*Real.sqrt n := by
    have hsq := Real.sq_sqrt hn0.le
    have hsq2 := Real.sq_sqrt (show 0≤2*(n:ℝ) by positivity)
    nlinarith [Real.sqrt_nonneg (n:ℝ),Real.sqrt_nonneg (2*(n:ℝ))]
  have hsqrt1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
  have herror : Real.log n + Real.sqrt (2*(n:ℝ))*Real.log (2*(n:ℝ)) ≤ (n:ℝ)/6 := by
    have h1 := mul_le_mul hsqrt hlog2n (Real.log_nonneg (by linarith : 1≤2*(n:ℝ))) (by positivity : 0≤2*Real.sqrt n)
    have h2 := mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg (n:ℝ))
    have h3 := Real.sq_sqrt hn0.le
    nlinarith only [h1,h2,h3,hsqrt1,hl0]
  have hmain := dyadic_prime_log_lower n hn
  have hlogterm := mul_le_mul_of_nonneg_left hlog2n (Nat.cast_nonneg (dyadicPrimes n).card)
  have hlower := mul_le_mul_of_nonneg_left hlog4 (by positivity : 0 ≤ (n:ℝ)/3)
  apply (div_le_iff₀ (by positivity : 0 < 20*Real.log n)).mpr
  nlinarith only [hmain,hlogterm,hlower,herror,hn0]

lemma scalePrimes_card (S : ℝ) (hS : 2 ≤ S) (hlog : 1 ≤ Real.log S)
    (hbig : 4000*Real.log S ≤ S) : S^99 ≤ ((scalePrimes S).card:ℝ) := by
  let n := ⌊S^100⌋₊
  have hS0 : 0 < S := by linarith
  have hnU : (n:ℝ) ≤ S^100 := Nat.floor_le (by positivity)
  have hnL : S^100-1 < (n:ℝ) := Nat.sub_one_lt_floor _
  have hpow : S^4 ≤ S^100 := pow_le_pow_right₀ (by linarith) (by norm_num : 4 ≤ 100)
  have hsq : 4 ≤ S^2 := by nlinarith
  have hnBig : S^2 ≤ (n:ℝ) := by nlinarith [sq_nonneg (S^2-2)]
  have hn4 : 4 ≤ n := by exact_mod_cast (hsq.trans hnBig)
  have hn0 : 0 < (n:ℝ) := by linarith
  have hnl : 1 ≤ Real.log n := by
    have hh := Real.log_le_log (sq_pos_of_pos hS0) hnBig
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hnlog : Real.log n ≤ 100*Real.log S := by
    have hh := Real.log_le_log hn0 hnU
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hroot : S ≤ Real.sqrt n := by
    exact (Real.le_sqrt hS0.le (Nat.cast_nonneg n)).mpr hnBig
  have herr : 30*Real.log n ≤ Real.sqrt n := by linarith
  have hh := dyadic_prime_count_lower n hn4 hnl herr
  apply le_trans _ hh
  apply (le_div_iff₀ (by positivity : 0 < 20*Real.log n)).mpr
  have hhalf : S^100/2 ≤ (n:ℝ) := by
    have h100 : 2 ≤ S^100 := by linarith
    linarith
  calc
    _ ≤ S^99*(2000*Real.log S) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ S^99*(S/2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = S^100/2 := by ring
    _ ≤ _ := hhalf

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.scalePrimes_card := @_root_.OAI.ShortEgyptian.scalePrimes_card
