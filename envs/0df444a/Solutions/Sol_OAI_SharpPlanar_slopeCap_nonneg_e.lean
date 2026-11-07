-- Prove2me | solution 1 for OAI.SharpPlanar.slopeCap_nonneg_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:24:42.962241+00:00
-- url     : https://prove2.me/submissions/c8259194-8c9f-4bc3-83d0-109e4d0b3b95

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

lemma slopeCap_nonneg_e_oai (j : Fin 6) : 0 ≤ slopeCap j := by fin_cases j <;> (first | (simp [slopeCap]; all_goals first | (norm_num [slopeCap]; done) | rfl | decide) | (norm_num [slopeCap]; done) | norm_num [slopeCap])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.slopeCap_nonneg_e_oai := @OAI.SharpPlanar.slopeCap_nonneg_e_oai
