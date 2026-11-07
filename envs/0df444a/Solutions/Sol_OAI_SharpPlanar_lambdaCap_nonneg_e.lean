-- Prove2me | solution 1 for OAI.SharpPlanar.lambdaCap_nonneg_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T19:54:36.339908+00:00
-- url     : https://prove2.me/submissions/50c0d3c5-c4db-49ac-9814-0e68597aa021

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

lemma lambdaCap_nonneg_e_oai (j : Fin 7) : 0 ≤ lambdaCap j := by fin_cases j <;> (first | (simp [lambdaCap]; all_goals first | (norm_num [lambdaCap]; done) | rfl | decide) | (norm_num [lambdaCap]; done) | norm_num [lambdaCap])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.lambdaCap_nonneg_e_oai := @OAI.SharpPlanar.lambdaCap_nonneg_e_oai
