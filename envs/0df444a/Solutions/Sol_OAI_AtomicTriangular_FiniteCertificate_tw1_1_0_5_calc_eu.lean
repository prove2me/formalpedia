-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_5_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:15:58.672746+00:00
-- url     : https://prove2.me/submissions/112c88ec-b403-4ed4-ae1e-238e89c7b904

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_0_5_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 1 0 5 j = tw1_1_0_5 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_5_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_5_calc_eu_oai
