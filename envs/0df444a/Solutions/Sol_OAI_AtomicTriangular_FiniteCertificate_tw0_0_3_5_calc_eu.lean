-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_3_5_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T14:05:35.872664+00:00
-- url     : https://prove2.me/submissions/32daec32-c2b4-4fa6-ba34-c9c1ac9265b6

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
lemma tw0_0_3_5_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 0 3 5 j = tw0_0_3_5 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_3_5_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_3_5_calc_eu_oai
