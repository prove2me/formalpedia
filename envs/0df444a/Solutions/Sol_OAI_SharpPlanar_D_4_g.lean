-- Prove2me | solution 1 for OAI.SharpPlanar.D_4_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:19:56.049213+00:00
-- url     : https://prove2.me/submissions/0a8e607a-fe1d-422d-869b-8d9e40d7fd27

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_D_as_table_g
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_b_sq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma b_lt_one : b < 1 := by nlinarith [b_sq_g, b_pos_g]
lemma b_pow_even (n : ℕ) : b^(2*n) = (3/4 : ℝ)^n := by rw [pow_mul, b_sq_g]
lemma b_pow_odd (n : ℕ) : b^(2*n+1) = (3/4 : ℝ)^n * b := by rw [pow_add, b_pow_even]; simp
lemma b_pow_3 : b^3 = (3/4 : ℝ)^1 * b := b_pow_odd 1

lemma one_sub_b_ne : 1 - b ≠ 0 := by linarith [b_lt_one]
lemma one_add_b_ne : 1 + b ≠ 0 := by linarith [b_pos_g]

lemma D_4_g_oai : D 4 = 7 * Real.pi * b / 9 := by
  rw [D_as_table_g, show 4 % 12 = 4 from rfl,
    show residues.erase 4 = {0, 1, 3, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq_g]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_pow_3]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.D_4_g_oai := @OAI.SharpPlanar.D_4_g_oai
