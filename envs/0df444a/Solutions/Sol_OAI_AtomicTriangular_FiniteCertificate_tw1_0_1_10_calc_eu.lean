-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_10_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:05:19.464385+00:00
-- url     : https://prove2.me/submissions/729d3fb5-ba2f-4d26-8327-d778ddb2fe5d

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_1_10_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 0 1 10 j = tw1_0_1_10 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_10_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_10_calc_eu_oai
