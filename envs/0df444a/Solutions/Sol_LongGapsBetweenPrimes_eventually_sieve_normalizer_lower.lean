-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_sieve_normalizer_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:08.587522+00:00
-- url     : https://prove2.me/submissions/3e1c416d-2201-4efb-abcc-3aa430f58629

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sieve_normalizer_lower_of_bounds
import Theorems.Thm_LongGapsBetweenPrimes_tendsto_sieveZ

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    sieveZ x ≤ sieveY x ∧ normalizerLower ≤ normalizer (sieveP x) := by
  have hpow : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ 6 / x)
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_sieveZ.eventually_ge_atTop 2,
    hpow.eventually_le_const (by positivity : (0 : ℝ) < 1 / (7 * Real.exp 6)),
    hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 24),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * (Real.log 7 + 8))]
    with x hx hlx hZ hpow hlog hconst
  apply sieve_normalizer_lower_of_bounds hx hlx hZ
  · simpa [mul_comm] using
      (div_le_div_iff₀ hx (by positivity : 0 < 7 * Real.exp 6)).mp hpow
  · have h := (div_le_iff₀ (zero_lt_one.trans_le hlx)).mp hlog
    linarith
end LongGapsBetweenPrimes
