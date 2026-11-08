-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.waveAmplitudeBox_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T01:04:08.105723+00:00
-- url     : https://prove2.me/submissions/6027e8ba-5278-4f14-ac09-036acdb981b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G091
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma waveAmplitudeBox_contains_g_oai {p : PointBox} {t : ℝ} (hp : p.Contains t)
    {a b : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j))
    (hb : b.Contains (basisBeta n j)) (d : Bool) :
    (waveAmplitudeBox p a b d).Contains (waveAmplitude d n j t) := by
  cases d
  · have hh := CBox.contains_mul_g
      (CBox.contains_scale_g (CBox.contains_mul_g (rcast_contains_g piBounds_contains_g)
        (rcast_contains_g piBounds_contains_g)) (-2) 1 (by norm_num))
      (CBox.contains_add_g hb (CBox.neg_contains_g (CBox.contains_mul_g (rcast_contains_g hp.1) ha)))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,Bool.false_eq_true,ite_false, if_false,Int.cast_neg,Int.cast_ofNat,Int.cast_one] <;> ring)
  · have hh := CBox.contains_mul_g (CBox.contains_scale_g piI_contains_g 2 1 (by norm_num)) ha
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,ite_true, if_true,Int.cast_ofNat,Int.cast_one] <;> ring)

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.waveAmplitudeBox_contains_g_oai := @OAI.SharpPlanar.IntegerBasis.waveAmplitudeBox_contains_g_oai
