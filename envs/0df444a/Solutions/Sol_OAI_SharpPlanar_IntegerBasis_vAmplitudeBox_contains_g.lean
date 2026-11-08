-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.vAmplitudeBox_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T01:03:45.199761+00:00
-- url     : https://prove2.me/submissions/9868eb3a-1687-460d-b1db-d8cb122e788a

import Mathlib
import Definitions.Def_OAIQ098G202
import Definitions.Def_OAIQ098G235
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma vAmplitudeBox_contains_g_oai {a : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j)) :
    (vAmplitudeBox a).Contains (vAmplitude n j) := by
  have he := CBox.contains_mul_g (CBox.contains_scale_g piI_contains_g 2 1 (by norm_num)) ha
  unfold vAmplitudeBox
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  unfold vAmplitude
  push_cast
  ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.vAmplitudeBox_contains_g_oai := @OAI.SharpPlanar.IntegerBasis.vAmplitudeBox_contains_g_oai
