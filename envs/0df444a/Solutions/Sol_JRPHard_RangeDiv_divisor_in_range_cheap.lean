-- Prove2me | solution 1 for JRPHard.RangeDiv.divisor_in_range_cheap
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:15:38.70508+00:00
-- url     : https://prove2.me/submissions/9cc4081b-5bf3-480d-aca6-760a72b64bf5

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting
open JRPHard.RangeDiv
set_option autoImplicit false

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, Lemma 3.
theorem solution (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) (q : ℕ)
    (hdvd : q ∣ M) (hL : L ≤ q) (hU : q ≤ U) :
    obj5 M L U q ≤ (L : ℝ) + U := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le hI.1 hL)
  have hL' : (L : ℝ) ≤ q := by exact_mod_cast hL
  have hU' : (q : ℝ) ≤ U := by exact_mod_cast hU
  rw [obj5, Nat.gcd_eq_left hdvd, Nat.cast_mul]
  apply (le_sub_iff_add_le).mp
  apply (div_le_iff₀ hq).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hL') (sub_nonneg.mpr hU')]
