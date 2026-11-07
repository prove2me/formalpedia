-- Prove2me | solution 1 for OAI.SharpPlanar.pieceBase_pos_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T19:53:13.245206+00:00
-- url     : https://prove2.me/submissions/fd30fb8a-d9b2-48f9-9b64-5d754fb3aa04

import Mathlib
import Definitions.Def_OAIQ098E125

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
lemma pieceBase_pos_e_oai (j : Fin 6) : 0 < pieceBase j := by fin_cases j <;> (first | (simp [pieceBase]; all_goals first | (norm_num [pieceBase]; done) | rfl | decide) | (norm_num [pieceBase]; done) | norm_num [pieceBase])
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceBase_pos_e_oai := @OAI.SharpPlanar.pieceBase_pos_e_oai
