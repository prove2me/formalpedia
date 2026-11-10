-- Prove2me | solution 1 for OAI.SharpPlanar.pieceMass_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:21:59.185025+00:00
-- url     : https://prove2.me/submissions/e313e868-5e7c-4f19-8a6b-3b75332538fe

import Mathlib
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_slopeCap_nonneg_g

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

lemma pieceMass_nonneg_g_oai (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pieceMass j s := by
  unfold pieceMass
  split_ifs
  · norm_num
  · exact le_min (by norm_num) (div_nonneg (by norm_num) (mul_nonneg (mul_nonneg Real.pi_pos.le (slopeCap_nonneg_g _)) hs))

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceMass_nonneg_g_oai := @OAI.SharpPlanar.pieceMass_nonneg_g_oai
