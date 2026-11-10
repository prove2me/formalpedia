-- Prove2me | solution 1 for OAI.SharpPlanar.transformEnvelope_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:25:27.853252+00:00
-- url     : https://prove2.me/submissions/37af025e-dce5-4f6d-9d8f-25dd63a02ae8

import Mathlib
import Definitions.Def_OAIQ098G1698
import Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_pieceL_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_zCap_nonneg_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Envelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral derivative bounds

Monotone spectral envelopes bound the cardinal functions and their Fourier kernels.
The estimates follow *A sharp Fourier certificate for planar circle packing*
(OpenAI, 2026).
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma transformEnvelope_nonneg_g_oai (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ transformEnvelope ell s := by
  apply Finset.sum_nonneg; intro j _
  exact mul_nonneg (mul_nonneg (densityCap_nonneg_g _) (pieceL_nonneg_g _ hs))
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg_g _)) _)
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.transformEnvelope_nonneg_g_oai := @OAI.SharpPlanar.transformEnvelope_nonneg_g_oai
