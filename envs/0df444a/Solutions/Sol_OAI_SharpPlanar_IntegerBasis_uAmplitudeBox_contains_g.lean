-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:11:59.374109+00:00
-- url     : https://prove2.me/submissions/3c5cc5c3-3ab2-41cd-8ea5-c0e66002ef38

import Mathlib
import Definitions.Def_OAIQ098G235
import Definitions.Def_OAIQ098G322
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g

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

lemma uAmplitudeBox_contains_g_oai {t : RBox} {a b : CBox} {s : ℝ} {n j : ℕ}
    (ht : t.Contains s) (ha : a.Contains (basisAlpha n j)) (hb : b.Contains (basisBeta n j)) :
    (uAmplitudeBox t a b).Contains (uAmplitude n j s) := by
  have hp := CBox.contains_scale_g (rcast_contains_g
    (RBox.contains_mul_g piBounds_contains_g piBounds_contains_g)) (-2) 1 (by norm_num)
  have he := CBox.contains_mul_g hp
    (CBox.contains_add_g hb (CBox.neg_contains_g (CBox.contains_mul_g (rcast_contains_g ht) ha)))
  unfold uAmplitudeBox
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  unfold uAmplitude
  push_cast
  ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains_g_oai := @OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains_g_oai
