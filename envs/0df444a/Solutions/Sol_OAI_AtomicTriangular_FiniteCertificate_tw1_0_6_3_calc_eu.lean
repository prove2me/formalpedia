-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_6_3_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:13:29.048442+00:00
-- url     : https://prove2.me/submissions/2d3d8ed6-3b9f-4b69-9af9-0bfd76ac444f

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_6_3_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 0 6 3 j = tw1_0_6_3 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_6_3_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_6_3_calc_eu_oai
