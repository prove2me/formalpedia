-- Prove2me | solution 1 for OAI.SharpPlanar.pieceL_nonneg_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:16:18.285594+00:00
-- url     : https://prove2.me/submissions/f420b6a2-5226-4945-8f92-16c697d060d1

import Mathlib
import Definitions.Def_OAIQ098E125
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_e
import Theorems.Thm_OAI_SharpPlanar_pieceMass_nonneg_e

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

lemma pieceL_nonneg_e_oai (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pieceL j s := by
  exact mul_nonneg (mul_nonneg (lambdaCap_nonneg_e _) (Real.exp_pos _).le) (pieceMass_nonneg_e j hs)

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceL_nonneg_e_oai := @OAI.SharpPlanar.pieceL_nonneg_e_oai
