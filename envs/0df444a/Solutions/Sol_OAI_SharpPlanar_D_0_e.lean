-- Prove2me | solution 1 for OAI.SharpPlanar.D_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:23:35.813493+00:00
-- url     : https://prove2.me/submissions/353f9c79-e916-4206-ba64-008b1b2d27ff

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_D_as_table_e
import Theorems.Thm_OAI_SharpPlanar_b_pos_e
import Theorems.Thm_OAI_SharpPlanar_b_sq_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma b_lt_one : b < 1 := by nlinarith [b_sq_e, b_pos_e]
lemma b_pow_even (n : ℕ) : b^(2*n) = (3/4 : ℝ)^n := by rw [pow_mul, b_sq_e]
lemma b_pow_odd (n : ℕ) : b^(2*n+1) = (3/4 : ℝ)^n * b := by rw [pow_add, b_pow_even]; simp
lemma b_pow_3 : b^3 = (3/4 : ℝ)^1 * b := b_pow_odd 1

lemma one_sub_b_ne : 1 - b ≠ 0 := by linarith [b_lt_one]
lemma one_add_b_ne : 1 + b ≠ 0 := by linarith [b_pos_e]

lemma D_0_e_oai : D 0 = -7 * Real.pi * b / 9 := by
  rw [D_as_table_e, show 0 % 12 = 0 from rfl,
    show residues.erase 0 = {1, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq_e]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_pow_3]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.D_0_e_oai := @OAI.SharpPlanar.D_0_e_oai
