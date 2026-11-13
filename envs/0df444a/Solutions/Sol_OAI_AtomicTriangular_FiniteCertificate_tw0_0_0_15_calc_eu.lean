-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_15_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:53:48.025554+00:00
-- url     : https://prove2.me/submissions/a08cddd7-0185-477b-98a8-0d4a29535cb2

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
lemma tw0_0_0_15_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 0 0 15 j = tw0_0_0_15 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_15_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_15_calc_eu_oai
