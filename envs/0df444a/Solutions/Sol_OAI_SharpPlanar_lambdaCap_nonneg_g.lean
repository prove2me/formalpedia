-- Prove2me | solution 1 for OAI.SharpPlanar.lambdaCap_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:21:22.431623+00:00
-- url     : https://prove2.me/submissions/e55bded4-11bb-4971-8a84-72e252ee09d6

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

lemma lambdaCap_nonneg_g_oai (j : Fin 7) : 0 ≤ lambdaCap j := by fin_cases j <;> (first | (simp [lambdaCap]; all_goals first | (norm_num [lambdaCap]; done) | rfl | decide) | (norm_num [lambdaCap]; done) | norm_num [lambdaCap])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.lambdaCap_nonneg_g_oai := @OAI.SharpPlanar.lambdaCap_nonneg_g_oai
