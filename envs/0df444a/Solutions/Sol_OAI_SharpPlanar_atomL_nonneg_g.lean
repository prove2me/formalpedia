-- Prove2me | solution 1 for OAI.SharpPlanar.atomL_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:24:34.631748+00:00
-- url     : https://prove2.me/submissions/de8d30ae-ddf7-444e-92ce-3e80fc4e92a9

import Mathlib
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_g

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

lemma atomL_nonneg_g_oai (j : Fin 7) (s : ℝ) : 0 ≤ atomL j s := by
  unfold atomL
  apply mul_nonneg _ (Real.exp_pos _).le
  apply mul_nonneg _ (lambdaCap_nonneg_g _)
  fin_cases j <;> (first | (simp [atomMass]; all_goals first | (norm_num [atomMass]; done) | rfl | decide) | (norm_num [atomMass]; done) | norm_num [atomMass])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.atomL_nonneg_g_oai := @OAI.SharpPlanar.atomL_nonneg_g_oai
