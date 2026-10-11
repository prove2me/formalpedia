-- Prove2me | solution 1 for GravityNonRenorm.exponent_comparison_footnote26
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T12:50:05.676997+00:00
-- url     : https://prove2.me/submissions/64c0eb7e-a8fa-45ba-a98c-1de6dfb56b7d

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm

theorem fn26_main (d : ℕ) (hd : 4 ≤ d) :
    ((d : ℝ) - 1) / d < 1 ∧ 1 < ((d : ℝ) - 2) / ((d : ℝ) - 3) := by
  have h4 : (4 : ℝ) ≤ d := by exact_mod_cast hd
  constructor
  · rw [div_lt_one (by linarith)]; linarith
  · rw [one_lt_div (by linarith)]; linarith

end GravityNonRenorm

open GravityNonRenorm

theorem solution (d : ℕ) (hd : 4 ≤ d) :
    ((d : ℝ) - 1) / d < 1 ∧ 1 < ((d : ℝ) - 2) / ((d : ℝ) - 3) :=
  fn26_main d hd
