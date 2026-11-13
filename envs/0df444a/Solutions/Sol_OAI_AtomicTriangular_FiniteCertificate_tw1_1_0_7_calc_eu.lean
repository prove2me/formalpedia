-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_7_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:15:30.798203+00:00
-- url     : https://prove2.me/submissions/701adb46-0ab8-410a-b50a-90dc98ac10b9

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
lemma tw1_1_0_7_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 1 0 7 j = tw1_1_0_7 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_7_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_7_calc_eu_oai
