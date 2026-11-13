-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_3_2_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T14:05:33.917491+00:00
-- url     : https://prove2.me/submissions/9ded2a7c-031e-43ad-bffd-68e33e35bf2a

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
lemma tw0_0_3_2_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 0 3 2 j = tw0_0_3_2 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_3_2_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_3_2_calc_eu_oai
