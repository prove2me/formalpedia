-- Prove2me | solution 1 for OAI.SharpPlanar.pieceL_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:21:56.100522+00:00
-- url     : https://prove2.me/submissions/0e5fbc11-1478-4977-b60f-9bb1f788f904

import Mathlib
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_pieceMass_nonneg_g

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

lemma pieceL_nonneg_g_oai (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pieceL j s := by
  exact mul_nonneg (mul_nonneg (lambdaCap_nonneg_g _) (Real.exp_pos _).le) (pieceMass_nonneg_g j hs)

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceL_nonneg_g_oai := @OAI.SharpPlanar.pieceL_nonneg_g_oai
