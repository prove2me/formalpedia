-- Prove2me | solution 1 for Kyprianou.Ch01.brownianAdjustmentRoot
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:19:09.376203+00:00
-- url     : https://prove2.me/submissions/f0d2637d-d48a-419b-9ee9-ee631800db1b

import Mathlib
open Real
set_option autoImplicit false

theorem solution
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q) :
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    0 < theta ∧ sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q := by
  intro theta
  have hs2 : 0 < sigma ^ 2 := by positivity
  have hnn : 0 ≤ gamma ^ 2 + 2 * sigma ^ 2 * q := by positivity
  set s := Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) with hs
  have hsq : s ^ 2 = gamma ^ 2 + 2 * sigma ^ 2 * q := Real.sq_sqrt hnn
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hgt : gamma < s := by
    by_contra hle
    push Not at hle
    have : 2 * sigma ^ 2 * q > 0 := by positivity
    nlinarith [abs_nonneg gamma, sq_abs gamma]
  refine ⟨div_pos (by linarith) hs2, ?_⟩
  show sigma ^ 2 * ((s - gamma) / sigma ^ 2) ^ 2 / 2 + gamma * ((s - gamma) / sigma ^ 2) = q
  field_simp
  nlinarith [hsq]
