-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.vAmplitudeBox_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:37:58.615177+00:00
-- url     : https://prove2.me/submissions/bc19bd6f-0deb-4f9c-a557-67beeb3c54e3

import Mathlib
import Definitions.Def_OAIQ098E071
import Definitions.Def_OAIQ098E087
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_e

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

lemma vAmplitudeBox_contains_e_oai {a : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j)) :
    (vAmplitudeBox a).Contains (vAmplitude n j) := by
  have he := CBox.contains_mul_e (CBox.contains_scale_e piI_contains_e 2 1 (by norm_num)) ha
  unfold vAmplitudeBox
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  unfold vAmplitude
  push_cast
  ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.vAmplitudeBox_contains_e_oai := @OAI.SharpPlanar.IntegerBasis.vAmplitudeBox_contains_e_oai
