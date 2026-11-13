-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_15_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:57:25.983812+00:00
-- url     : https://prove2.me/submissions/65654d30-cbd5-4d95-84c4-19a1c3365b2f

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave012
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_2_15_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 1 2 15 j = tw0_1_2_15 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_15_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_15_calc_eu_oai
