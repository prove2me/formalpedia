-- Prove2me | solution 1 for OAI.SharpPlanar.directEnvelope_le_rat_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:41:26.813735+00:00
-- url     : https://prove2.me/submissions/71d4a903-7c4b-4073-9e72-c133beeed011

import Mathlib
import Definitions.Def_OAIQ098G1675
import Definitions.Def_OAIQ098G1676
import Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_pi_fine_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_RationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational Fourier envelopes

Explicit rational majorants control the direct and transformed spectral envelopes
at integral and half-integral radii.
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma pi_le_upper : Real.pi ≤ piUpper := pi_fine_g.2.le
lemma directEnvelope_le_rat_g_oai (ell : ℕ) : directEnvelope ell ≤ directRational ell := by
  apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right pi_le_upper (by positivity)) (by norm_num)
  · exact div_nonneg (densityCap_nonneg_g _) (by norm_num)
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.directEnvelope_le_rat_g_oai := @OAI.SharpPlanar.directEnvelope_le_rat_g_oai
