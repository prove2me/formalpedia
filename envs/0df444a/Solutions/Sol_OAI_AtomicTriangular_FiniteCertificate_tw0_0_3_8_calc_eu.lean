-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_3_8_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T14:06:00.544376+00:00
-- url     : https://prove2.me/submissions/af553515-08e2-4b78-974e-7f2a5776dc2b

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_3_8_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 0 3 8 j = tw0_0_3_8 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_3_8_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_3_8_calc_eu_oai
