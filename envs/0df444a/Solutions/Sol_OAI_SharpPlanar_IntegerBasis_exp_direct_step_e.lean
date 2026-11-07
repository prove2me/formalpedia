-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.exp_direct_step_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T17:02:42.669197+00:00
-- url     : https://prove2.me/submissions/27d8fc10-7f6e-4832-86c1-61afb82ac109

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma exp_direct_step_e_oai {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (-Complex.I*Real.pi*t*n)))
    (hq : q.Contains (Complex.exp (-Complex.I*Real.pi*t))) :
    (p.mul q).Contains (Complex.exp (-Complex.I*Real.pi*t*(n+1))) := by
  have hh := CBox.contains_mul_e hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.exp_direct_step_e_oai := @OAI.SharpPlanar.IntegerBasis.exp_direct_step_e_oai
