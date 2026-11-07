-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.waveAmplitudeBox_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T17:03:49.951801+00:00
-- url     : https://prove2.me/submissions/26decd38-42b7-4343-b545-75291dcced6f

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_neg_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma waveAmplitudeBox_contains_e_oai {p : PointBox} {t : ℝ} (hp : p.Contains t)
    {a b : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j))
    (hb : b.Contains (basisBeta n j)) (d : Bool) :
    (waveAmplitudeBox p a b d).Contains (waveAmplitude d n j t) := by
  cases d
  · have hh := CBox.contains_mul_e
      (CBox.contains_scale_e (CBox.contains_mul_e (rcast_contains_e piBounds_contains_e)
        (rcast_contains_e piBounds_contains_e)) (-2) 1 (by norm_num))
      (CBox.contains_add_e hb (CBox.neg_contains_e (CBox.contains_mul_e (rcast_contains_e hp.1) ha)))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,Bool.false_eq_true,ite_false, if_false,Int.cast_neg,Int.cast_ofNat,Int.cast_one] <;> ring)
  · have hh := CBox.contains_mul_e (CBox.contains_scale_e piI_contains_e 2 1 (by norm_num)) ha
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,ite_true, if_true,Int.cast_ofNat,Int.cast_one] <;> ring)

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.waveAmplitudeBox_contains_e_oai := @OAI.SharpPlanar.IntegerBasis.waveAmplitudeBox_contains_e_oai
