-- Prove2me | solution 1 for OAI.SharpPlanar.densityCap_nonneg_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T03:58:11.148187+00:00
-- url     : https://prove2.me/submissions/c91f5855-f3ae-4181-a3e1-77f864e997a9

import Mathlib
import Definitions.Def_OAIQ098E126

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

lemma densityCap_nonneg_e_oai (j : Fin 6) : 0 ≤ densityCap j := by
  fin_cases j <;> (first | (simp [densityCap,densityNum,densityDen]; all_goals first | (norm_num [densityCap,densityNum,densityDen]; done) | rfl | decide) | (norm_num [densityCap,densityNum,densityDen]; done) | norm_num [densityCap,densityNum,densityDen])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.densityCap_nonneg_e_oai := @OAI.SharpPlanar.densityCap_nonneg_e_oai
