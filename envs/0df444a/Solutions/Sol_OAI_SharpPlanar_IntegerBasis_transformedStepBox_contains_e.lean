-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.transformedStepBox_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T17:03:27.529092+00:00
-- url     : https://prove2.me/submissions/562c957b-181f-46b0-8abf-b03f414fdbcf

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma transformedStepBox_contains_e_oai {p : PointBox} {t : ℝ} (hp : p.Contains t) :
    (transformedStepBox p).Contains (Complex.exp (Complex.I*Real.pi*z t)) := by
  have hh := CBox.contains_powFast_e hp.2.2.2.2 3 4 (by norm_num)
  rw [← Complex.exp_nat_mul] at hh
  change (p.quarter.powFast 3 4).Contains _
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [pointZ_eq_e]
  congr 1
  push_cast
  ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.transformedStepBox_contains_e_oai := @OAI.SharpPlanar.IntegerBasis.transformedStepBox_contains_e_oai
