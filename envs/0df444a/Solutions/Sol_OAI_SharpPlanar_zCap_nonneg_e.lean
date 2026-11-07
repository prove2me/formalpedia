-- Prove2me | solution 1 for OAI.SharpPlanar.zCap_nonneg_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:24:44.179893+00:00
-- url     : https://prove2.me/submissions/0ad9ce42-b2fa-4de1-9d32-f92b4f94955c

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

lemma zCap_nonneg_e_oai (j : Fin 7) : 0 ≤ zCap j := by fin_cases j <;> (first | (simp [zCap]; all_goals first | (norm_num [zCap]; done) | rfl | decide) | (norm_num [zCap]; done) | norm_num [zCap])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.zCap_nonneg_e_oai := @OAI.SharpPlanar.zCap_nonneg_e_oai
