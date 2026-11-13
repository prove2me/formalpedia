-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData00_4_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:02:30.746204+00:00
-- url     : https://prove2.me/submissions/b478b560-a480-4f63-bae4-aa9782c77913

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_CurvatureData00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData00_4_calc_eu_oai (j : Fin 31) : curvatureBox 0 0 4 j=curvatureData00_4 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData00_4_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData00_4_calc_eu_oai
