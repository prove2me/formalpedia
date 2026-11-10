-- Prove2me | solution 1 for OAI.SharpPlanar.transformEnvelope_le_rat_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:48:34.98663+00:00
-- url     : https://prove2.me/submissions/992623e3-91a4-4293-a436-410a2dbf2ac0

import Mathlib
import Definitions.Def_OAIQ098G1689
import Definitions.Def_OAIQ098G1698
import Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_massRational_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_pi_fine_g
import Theorems.Thm_OAI_SharpPlanar_pieceBase_pos_g
import Theorems.Thm_OAI_SharpPlanar_pieceL_le_intCap_g
import Theorems.Thm_OAI_SharpPlanar_zCap_nonneg_g

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
lemma pieceIntCap_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ pieceIntCap j n := by
  exact mul_nonneg (mul_nonneg (lambdaCap_nonneg_g _) (pow_nonneg (pieceBase_pos_g j).le n)) (massRational_nonneg_g _ _)
lemma transformEnvelope_le_rat_g_oai (ell n : ℕ) : transformEnvelope ell n ≤ transformRational ell n := by
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pieceL_le_intCap_g j n) (densityCap_nonneg_g _))
    (pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le (zCap_nonneg_g _))
      (mul_le_mul_of_nonneg_right pi_le_upper (zCap_nonneg_g _)) ell)
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg_g _)) _)
    (mul_nonneg (densityCap_nonneg_g _) (pieceIntCap_nonneg _ _))
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.transformEnvelope_le_rat_g_oai := @OAI.SharpPlanar.transformEnvelope_le_rat_g_oai
