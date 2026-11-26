-- Prove2me | solution 1 for Kyprianou.Ch04.WHRatioLimitRegularNonzeroExponent
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:25:22.036163+00:00
-- url     : https://prove2.me/submissions/70fd2386-d59d-4123-babf-16204766f162

import Mathlib
open Filter
set_option autoImplicit false
theorem _root_.solution
    (q r : ℕ → ℝ) (beta m psiBeta : ℝ)
    (hpsi : psiBeta ≠ 0)
    (hq0 : Tendsto q atTop (nhds 0))
    (hr0 : Tendsto r atTop (nhds 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (nhds m)) :
    Tendsto (fun n => (q n / r n) * ((r n - beta) / (q n - psiBeta)))
      atTop (nhds (m * beta / psiBeta)) := by
  have h2 : Tendsto (fun n => (r n - beta) / (q n - psiBeta)) atTop (nhds ((0 - beta) / (0 - psiBeta))) :=
    (hr0.sub_const beta).div (hq0.sub_const psiBeta) (by simpa using hpsi)
  have h := hquot.mul h2
  have e : m * ((0 - beta) / (0 - psiBeta)) = m * beta / psiBeta := by
    rw [zero_sub, zero_sub, neg_div_neg_eq, mul_div_assoc]
  rwa [e] at h

