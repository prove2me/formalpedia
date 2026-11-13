-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_14_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:59:43.315249+00:00
-- url     : https://prove2.me/submissions/0abb88ed-1122-434e-b749-ee998673ce3c

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave014
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_4_14_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 1 4 14 j = tw0_1_4_14 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_14_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_14_calc_eu_oai
