-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:56:30.768133+00:00
-- url     : https://prove2.me/submissions/77371309-23e1-4138-bf15-f135e5ac15a5

import Mathlib
import Definitions.Def_OAIQ098E087
import Definitions.Def_OAIQ098E111
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_neg_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_ofReal_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_check_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

lemma RBox.contains_mul {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := RBox.mul_contains_e hx hy (RBox.mul_check_e _ _)

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

lemma rcast_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (rcast a).Contains (x:ℂ) := CBox.ofReal_contains_e hx

end SharpPlanar.IntegerIntervals

end OAI
end

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

lemma uAmplitudeBox_contains_e_oai {t : RBox} {a b : CBox} {s : ℝ} {n j : ℕ}
    (ht : t.Contains s) (ha : a.Contains (basisAlpha n j)) (hb : b.Contains (basisBeta n j)) :
    (uAmplitudeBox t a b).Contains (uAmplitude n j s) := by
  have hp := CBox.contains_scale_e (rcast_contains
    (RBox.contains_mul piBounds_contains_e piBounds_contains_e)) (-2) 1 (by norm_num)
  have he := CBox.contains_mul_e hp
    (CBox.contains_add_e hb (CBox.neg_contains_e (CBox.contains_mul_e (rcast_contains ht) ha)))
  unfold uAmplitudeBox
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  unfold uAmplitude
  push_cast
  ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains_e_oai := @OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains_e_oai
