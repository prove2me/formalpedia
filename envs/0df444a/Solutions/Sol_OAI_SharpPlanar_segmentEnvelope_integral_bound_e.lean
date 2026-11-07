-- Prove2me | solution 1 for OAI.SharpPlanar.segmentEnvelope_integral_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:23:22.872756+00:00
-- url     : https://prove2.me/submissions/b8d17161-c8ec-43d8-ae74-a89ed521de08

import Mathlib
import Definitions.Def_OAIQ098E125
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_e
import Theorems.Thm_OAI_SharpPlanar_segment_exp_integral_bound_e
import Theorems.Thm_OAI_SharpPlanar_zCap_nonneg_e

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

lemma segmentEnvelope_integral_bound_e_oai (j : Fin 6) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, segmentEnvelope j ell s t) ≤
      pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell := by
  unfold segmentEnvelope
  rw [intervalIntegral.integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left (segment_exp_integral_bound_e j hs)
    (mul_nonneg (mul_nonneg (lambdaCap_nonneg_e ⟨j.val,by omega⟩)
      (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg_e ⟨j.val,by omega⟩)) ell))
      (Real.exp_pos (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)).le)
  convert hb using 1 <;> first | rfl | (unfold pieceL; ring)

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.segmentEnvelope_integral_bound_e_oai := @OAI.SharpPlanar.segmentEnvelope_integral_bound_e_oai
