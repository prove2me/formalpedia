-- Prove2me | solution 1 for JRPHard.Periodic.small_divisor_value
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:53:14.776747+00:00
-- url     : https://prove2.me/submissions/2f1b8b48-f82b-42f8-bb29-f4f13a86e878

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting
open JRPHard.Periodic
set_option autoImplicit false

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, Lemma 2.
theorem solution (M p : ℕ) (hpM : p ∣ M) (hp3 : 3 ≤ p) (hple : 3 * p ≤ M) :
    obj4 M p ≤ 2 * (M : ℝ) / 3 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpleR : 3 * (p : ℝ) ≤ M := by exact_mod_cast hple
  have hd : (M : ℝ) / p ≤ (M : ℝ) / 3 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hpR
  rw [obj4, Nat.gcd_eq_left hpM]
  linarith
