-- Prove2me | solution 1 for OAI.SharpPlanar.zCap_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:23:17.105591+00:00
-- url     : https://prove2.me/submissions/4a2c5b1f-4080-4e2e-8cca-e7eab993b6f8

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

lemma zCap_nonneg_g_oai (j : Fin 7) : 0 ≤ zCap j := by fin_cases j <;> (first | (simp [zCap]; all_goals first | (norm_num [zCap]; done) | rfl | decide) | (norm_num [zCap]; done) | norm_num [zCap])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.zCap_nonneg_g_oai := @OAI.SharpPlanar.zCap_nonneg_g_oai
