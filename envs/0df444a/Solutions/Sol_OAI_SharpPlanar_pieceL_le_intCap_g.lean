-- Prove2me | solution 1 for OAI.SharpPlanar.pieceL_le_intCap_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:25:26.309827+00:00
-- url     : https://prove2.me/submissions/27f8e4d7-7b7a-4116-9c44-a35f873c0c33

import Mathlib
import Definitions.Def_OAIQ098G1670
import Theorems.Thm_OAI_SharpPlanar_decay_pieceBase_g
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_pieceBase_pos_g
import Theorems.Thm_OAI_SharpPlanar_pieceMass_le_g
import Theorems.Thm_OAI_SharpPlanar_pieceMass_nonneg_g

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
lemma pieceL_le_intCap_g_oai (j : Fin 6) (n : ℕ) : pieceL j n ≤ pieceIntCap j n := by
  exact mul_le_mul (mul_le_mul_of_nonneg_left (decay_pieceBase_g j n) (lambdaCap_nonneg_g _))
    (pieceMass_le_g j n) (pieceMass_nonneg_g _ (Nat.cast_nonneg n))
      (mul_nonneg (lambdaCap_nonneg_g _) (pow_nonneg (pieceBase_pos_g j).le n))
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceL_le_intCap_g_oai := @OAI.SharpPlanar.pieceL_le_intCap_g_oai
