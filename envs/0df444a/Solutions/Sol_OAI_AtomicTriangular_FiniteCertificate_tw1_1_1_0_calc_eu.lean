-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_0_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:15:33.961389+00:00
-- url     : https://prove2.me/submissions/5892f010-14a2-4bed-b5e4-02f89c691f26

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_1_0_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 1 1 0 j = tw1_1_1_0 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_0_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_0_calc_eu_oai
