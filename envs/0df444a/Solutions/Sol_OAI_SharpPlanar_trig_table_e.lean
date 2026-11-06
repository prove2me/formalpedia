-- Prove2me | solution 1 for OAI.SharpPlanar.trig_table_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:50:13.911178+00:00
-- url     : https://prove2.me/submissions/65238a42-1c68-4b8a-8857-b402a43e285a

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_b_sq_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma trig_table_e_oai (n : ℕ) (hn : n ≤ 12) :
    Real.sin (Real.pi * n / 6) = sinTable n ∧
    Real.cos (Real.pi * n / 6) = cosTable n := by
  induction n with
  | zero => norm_num [sinTable, cosTable]
  | succ n ih =>
    have hn' : n ≤ 12 := by omega
    obtain ⟨hs, hc⟩ := ih hn'
    rw [show Real.pi * (n+1 : ℕ) / 6 = Real.pi * n / 6 + Real.pi / 6 by push_cast; ring]
    rw [Real.sin_add, Real.cos_add, hs, hc, Real.sin_pi_div_six, Real.cos_pi_div_six]
    change sinTable n * b + cosTable n * (1/2) = sinTable (n+1) ∧
      cosTable n * b - sinTable n * (1/2) = cosTable (n+1)
    have hn11 : n ≤ 11 := by omega
    interval_cases n <;> norm_num [sinTable, cosTable] <;> constructor <;> nlinarith [b_sq_e]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.trig_table_e_oai := @OAI.SharpPlanar.trig_table_e_oai
