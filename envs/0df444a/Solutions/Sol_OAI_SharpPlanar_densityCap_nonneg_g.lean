-- Prove2me | solution 1 for OAI.SharpPlanar.densityCap_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:25:25.484953+00:00
-- url     : https://prove2.me/submissions/6941fd8d-9a6c-408b-a6ed-c7f7b432e295

import Mathlib
import Definitions.Def_OAIQ098G365

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

lemma densityCap_nonneg_g_oai (j : Fin 6) : 0 ≤ densityCap j := by
  fin_cases j <;> (first | (simp [densityCap,densityNum,densityDen]; all_goals first | (norm_num [densityCap,densityNum,densityDen]; done) | rfl | decide) | (norm_num [densityCap,densityNum,densityDen]; done) | norm_num [densityCap,densityNum,densityDen])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.densityCap_nonneg_g_oai := @OAI.SharpPlanar.densityCap_nonneg_g_oai
