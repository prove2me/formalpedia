-- Prove2me | solution 1 for OAI.SharpPlanar.Q_1_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:10:43.432567+00:00
-- url     : https://prove2.me/submissions/e3258f42-5fac-4096-be9e-8d331bf9db01

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_Q_as_table_g
import Theorems.Thm_OAI_SharpPlanar_b_sq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma b_pow_even (n : ℕ) : b^(2*n) = (3/4 : ℝ)^n := by rw [pow_mul, b_sq_g]
lemma b_pow_odd (n : ℕ) : b^(2*n+1) = (3/4 : ℝ)^n * b := by rw [pow_add, b_pow_even]; simp
lemma b_pow_3 : b^3 = (3/4 : ℝ)^1 * b := b_pow_odd 1

lemma Q_1_g_oai : Q 1 = (2*Real.pi^2/3)*(2-2*b) := by
  rw [Q_as_table_g, show 1 % 12 = 1 from rfl,
    show residues.erase 1 = {0, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq_g, b_pow_3]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_1_g_oai := @OAI.SharpPlanar.Q_1_g_oai
