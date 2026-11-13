-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_16_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:54:17.428215+00:00
-- url     : https://prove2.me/submissions/d5b849e7-2ba7-4b72-a6e8-b946c974b2aa

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_1_16_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 0 1 16 j = tw0_0_1_16 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_16_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_16_calc_eu_oai
