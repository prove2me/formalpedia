-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_11_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:10:12.024792+00:00
-- url     : https://prove2.me/submissions/658b8a1b-e529-4276-b099-704d2164ea80

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_4_11_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 0 4 11 j = tw1_0_4_11 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_11_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_11_calc_eu_oai
