-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_4_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:09:33.122331+00:00
-- url     : https://prove2.me/submissions/adb66c84-044b-4b5e-8db0-b913c9d1bb59

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_3_4_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 0 3 4 j = tw1_0_3_4 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_4_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_4_calc_eu_oai
