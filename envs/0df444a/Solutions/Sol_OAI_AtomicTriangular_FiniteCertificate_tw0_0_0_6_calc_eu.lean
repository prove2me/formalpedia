-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_6_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:21:58.853261+00:00
-- url     : https://prove2.me/submissions/8c687a7a-5f4b-45e1-99cb-c6db91fbaaaf

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_0_6_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 0 0 6 j = tw0_0_0_6 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_6_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_6_calc_eu_oai
