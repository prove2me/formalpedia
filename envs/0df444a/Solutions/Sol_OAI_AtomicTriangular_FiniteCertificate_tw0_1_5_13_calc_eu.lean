-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_13_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:00:45.01294+00:00
-- url     : https://prove2.me/submissions/705682c4-4b85-428f-8003-8398ab9156c8

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave015
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_5_13_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 1 5 13 j = tw0_1_5_13 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_13_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_13_calc_eu_oai
