-- Prove2me | solution 1 for OAI.SharpPlanar.atomicEnvelope_le_rat_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:25:23.269997+00:00
-- url     : https://prove2.me/submissions/13ddbec0-e36c-4da6-9761-7a61b1ac5c15

import Mathlib
import Definitions.Def_OAIQ098G1670
import Definitions.Def_OAIQ098G1671
import Theorems.Thm_OAI_SharpPlanar_atomBase_pos_g
import Theorems.Thm_OAI_SharpPlanar_decay_atomBase_g
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_pi_fine_g
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
lemma atomIntCap_nonneg (j : Fin 7) (n : ℕ) : 0 ≤ atomIntCap j n := by
  exact mul_nonneg (mul_nonneg (by fin_cases j <;> norm_num [atomMass]) (lambdaCap_nonneg_g _)) (pow_nonneg (atomBase_pos_g j).le n)
lemma atomL_le_intCap (j : Fin 7) (n : ℕ) : atomL j n ≤ atomIntCap j n := by
  exact mul_le_mul_of_nonneg_left (decay_atomBase_g j n)
    (mul_nonneg (by fin_cases j <;> norm_num [atomMass]) (lambdaCap_nonneg_g _))
lemma atomicEnvelope_le_rat_g_oai (ell n : ℕ) : atomicEnvelope ell n ≤ atomicRational ell n := by
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul (atomL_le_intCap j n)
    (pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le (zCap_nonneg_g _))
      (mul_le_mul_of_nonneg_right pi_le_upper (zCap_nonneg_g _)) ell)
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg_g _)) _)
    (atomIntCap_nonneg _ _)
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.atomicEnvelope_le_rat_g_oai := @OAI.SharpPlanar.atomicEnvelope_le_rat_g_oai
