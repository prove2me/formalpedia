-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_14_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:10:17.932291+00:00
-- url     : https://prove2.me/submissions/137bec6c-e288-4ab1-b199-62cba44d6621

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
lemma tw1_0_4_14_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 0 4 14 j = tw1_0_4_14 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_14_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_14_calc_eu_oai
