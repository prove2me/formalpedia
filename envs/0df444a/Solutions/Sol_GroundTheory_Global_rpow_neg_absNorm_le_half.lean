-- Prove2me | solution 1 for GroundTheory.Global.rpow_neg_absNorm_le_half
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:28:43.194596+00:00
-- url     : https://prove2.me/submissions/8251c2c3-4582-4e53-b30e-5ac385eab488

import Mathlib
open NumberField Ideal
variable {K : Type*} [Field K] [NumberField K]


theorem solution {p : Ideal (𝓞 K)} (hp : Prime p) {s : ℝ} (hs : 1 ≤ s) :
    (absNorm p : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h0 : absNorm p ≠ 0 := fun h => hp.ne_zero ((Ideal.absNorm_eq_zero_iff.mp h))
  have h1 : absNorm p ≠ 1 := fun h => hp.not_unit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  have hn : (2 : ℝ) ≤ absNorm p := by exact_mod_cast (show 2 ≤ absNorm p by omega)
  rw [Real.rpow_neg (by positivity)]
  have hpow := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ absNorm p by linarith) hs
  rw [Real.rpow_one] at hpow
  simpa [one_div] using inv_anti₀ (show (0:ℝ)<2 by norm_num) (hn.trans hpow)
