-- Prove2me | solution 1 for OAI.SharpPlanar.decay_atomBase_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:24:36.114853+00:00
-- url     : https://prove2.me/submissions/15846cf1-eb9b-4d1d-80ed-97abd628da66

import Mathlib
import Definitions.Def_OAIQ098G362
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_atomBase_contains_g
import Theorems.Thm_OAI_SharpPlanar_dampingCap_pos_g
import Theorems.Thm_OAI_SharpPlanar_pi_fine_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_AtomTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
lemma decay_atomBase_g_oai (j : Fin 7) (n : ℕ) :
    Real.exp (-Real.pi*dampingCap j*n) ≤ atomBase j^n := by
  have he : Real.exp (-Real.pi*dampingCap j)≤atomBase j :=
    (Real.exp_le_exp.mpr (by nlinarith [pi_fine_g,dampingCap_pos_g j])).trans (atomBase_contains_g j)
  rw [mul_comm _ (n:ℝ),Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he n
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.decay_atomBase_g_oai := @OAI.SharpPlanar.decay_atomBase_g_oai
