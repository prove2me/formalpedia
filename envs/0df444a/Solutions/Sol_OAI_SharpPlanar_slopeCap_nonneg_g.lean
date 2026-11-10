-- Prove2me | solution 1 for OAI.SharpPlanar.slopeCap_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:23:15.536183+00:00
-- url     : https://prove2.me/submissions/4e82a6d7-843a-45ba-b3af-b521875c2e85

import Mathlib
import Definitions.Def_OAIQ098G362

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

lemma slopeCap_nonneg_g_oai (j : Fin 6) : 0 ≤ slopeCap j := by fin_cases j <;> (first | (simp [slopeCap]; all_goals first | (norm_num [slopeCap]; done) | rfl | decide) | (norm_num [slopeCap]; done) | norm_num [slopeCap])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.slopeCap_nonneg_g_oai := @OAI.SharpPlanar.slopeCap_nonneg_g_oai
