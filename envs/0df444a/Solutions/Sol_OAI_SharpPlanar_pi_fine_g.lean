-- Prove2me | solution 1 for OAI.SharpPlanar.pi_fine_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:50.461991+00:00
-- url     : https://prove2.me/submissions/a8e74655-b18a-4c27-b210-1ad472a9763f

import Mathlib

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

lemma pi_fine_g_oai : (314159/100000:ℝ) < Real.pi ∧ Real.pi < 31416/10000 := by
  constructor <;> linarith [Real.pi_gt_d6,Real.pi_lt_d6]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pi_fine_g_oai := @OAI.SharpPlanar.pi_fine_g_oai
