-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.exp_direct_step_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:09:38.220973+00:00
-- url     : https://prove2.me/submissions/f7ddccb1-4336-4e4f-ad38-5bf1cc7cb4c6

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma exp_direct_step_g_oai {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (-Complex.I*Real.pi*t*n)))
    (hq : q.Contains (Complex.exp (-Complex.I*Real.pi*t))) :
    (p.mul q).Contains (Complex.exp (-Complex.I*Real.pi*t*(n+1))) := by
  have hh := CBox.contains_mul_g hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.exp_direct_step_g_oai := @OAI.SharpPlanar.IntegerBasis.exp_direct_step_g_oai
