-- Prove2me | solution 1 for OAI.SharpPlanar.dampingCap_pos_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:20:15.868564+00:00
-- url     : https://prove2.me/submissions/c9fd2fe6-fbc3-4f17-810b-b80238754a48

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

lemma dampingCap_pos_g_oai (j : Fin 7) : 0 < dampingCap j := by fin_cases j <;> (first | (simp [dampingCap]; all_goals first | (norm_num [dampingCap]; done) | rfl | decide) | (norm_num [dampingCap]; done) | norm_num [dampingCap])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.dampingCap_pos_g_oai := @OAI.SharpPlanar.dampingCap_pos_g_oai
