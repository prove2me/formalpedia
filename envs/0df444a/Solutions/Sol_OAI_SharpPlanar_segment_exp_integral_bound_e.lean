-- Prove2me | solution 1 for OAI.SharpPlanar.segment_exp_integral_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:24:02.793898+00:00
-- url     : https://prove2.me/submissions/5b741aec-3b54-4733-a95e-4cf6ca60c32b

import Mathlib
import Definitions.Def_OAIQ098E125
import Theorems.Thm_OAI_SharpPlanar_exp_segment_bound_e
import Theorems.Thm_OAI_SharpPlanar_slopeCap_nonneg_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis

lemma segment_exp_integral_bound_e_oai (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6,
      Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t))) ≤ pieceMass j s := by
  have he := exp_segment_bound_e (mul_nonneg (mul_nonneg Real.pi_pos.le (slopeCap_nonneg_e j)) hs)
    (by linarith : (j.val:ℝ)/6 ≤ ((j.val:ℝ)+1)/6)
  have hlen : ((j.val:ℝ)+1)/6-(j.val:ℝ)/6=1/6 := by ring
  simpa only [pieceMass,hlen,mul_assoc,mul_eq_zero,Real.pi_ne_zero,false_or] using he

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.segment_exp_integral_bound_e_oai := @OAI.SharpPlanar.segment_exp_integral_bound_e_oai
