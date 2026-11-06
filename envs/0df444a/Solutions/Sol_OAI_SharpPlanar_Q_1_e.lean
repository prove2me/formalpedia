-- Prove2me | solution 1 for OAI.SharpPlanar.Q_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:29:14.142396+00:00
-- url     : https://prove2.me/submissions/f6f2c63c-0714-44fa-b6d4-fdd4efc95dc6

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_Q_as_table_e
import Theorems.Thm_OAI_SharpPlanar_b_sq_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma b_pow_even (n : ℕ) : b^(2*n) = (3/4 : ℝ)^n := by rw [pow_mul, b_sq_e]
lemma b_pow_odd (n : ℕ) : b^(2*n+1) = (3/4 : ℝ)^n * b := by rw [pow_add, b_pow_even]; simp
lemma b_pow_3 : b^3 = (3/4 : ℝ)^1 * b := b_pow_odd 1

lemma Q_1_e_oai : Q 1 = (2*Real.pi^2/3)*(2-2*b) := by
  rw [Q_as_table_e, show 1 % 12 = 1 from rfl,
    show residues.erase 1 = {0, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq_e, b_pow_3]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_1_e_oai := @OAI.SharpPlanar.Q_1_e_oai
