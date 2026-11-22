-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_simple_sieve_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:55.34881+00:00
-- url     : https://prove2.me/submissions/eef8d4db-3f1b-45ba-b1ac-cab64a6fcb3f

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (C : ℝ) : ∀ᶠ x : ℝ in Filter.atTop,
    Real.exp (1 / x ^ 2) ≤ 5 / 4 ∧
    1 / x ^ 3 + 16 / x ^ 2 ≤ 1 / 2 ∧
    32 / x ^ 3 ≤ 1 / 8 ∧
    ((5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 5 + 32 / x ^ 2 < 1 / 4 := by
  have h (n : ℕ) (hn : n ≠ 0) :
      Filter.Tendsto (fun x : ℝ => 1 / x ^ n) Filter.atTop (nhds 0) := by
    simpa [one_div, hn] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow n
  have h₂ := h 2 (by decide)
  have h₃ := h 3 (by decide)
  have h₅ := h 5 (by decide)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp h₂
  have htail := h₃.add (h₂.const_mul 16)
  have herr := h₃.const_mul 32
  have hbad := (h₅.const_mul ((5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2))).add
    (h₂.const_mul 32)
  filter_upwards [hexp.eventually (gt_mem_nhds (by norm_num : Real.exp 0 < 5 / 4)),
    htail.eventually (gt_mem_nhds (by norm_num : 0 + 16 * 0 < (1 : ℝ) / 2)),
    herr.eventually (gt_mem_nhds (by norm_num : 32 * 0 < (1 : ℝ) / 8)),
    hbad.eventually (gt_mem_nhds (by simp :
      ((5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2)) * 0 + 32 * 0 < (1 : ℝ) / 4))]
    with x hexp htail herr hbad
  exact ⟨hexp.le, by simpa only [mul_one_div] using htail.le,
    by simpa only [mul_one_div] using herr.le,
    by simpa only [mul_one_div] using hbad⟩
end LongGapsBetweenPrimes
