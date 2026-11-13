-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_15_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:58:33.101196+00:00
-- url     : https://prove2.me/submissions/1b8f036d-d62f-455e-b3d2-2e12b2123555

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave013
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_3_15_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 1 3 15 j = tw0_1_3_15 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_15_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_15_calc_eu_oai
