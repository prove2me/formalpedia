-- Prove2me | solution 1 for OAI.SharpPlanar.pieceMass_nonneg_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:22:43.45348+00:00
-- url     : https://prove2.me/submissions/0c265c81-ccc0-4cad-b493-5fb2410fb6ae

import Mathlib
import Definitions.Def_OAIQ098E125
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

lemma pieceMass_nonneg_e_oai (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pieceMass j s := by
  unfold pieceMass
  split_ifs
  · norm_num
  · exact le_min (by norm_num) (div_nonneg (by norm_num) (mul_nonneg (mul_nonneg Real.pi_pos.le (slopeCap_nonneg_e _)) hs))

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceMass_nonneg_e_oai := @OAI.SharpPlanar.pieceMass_nonneg_e_oai
