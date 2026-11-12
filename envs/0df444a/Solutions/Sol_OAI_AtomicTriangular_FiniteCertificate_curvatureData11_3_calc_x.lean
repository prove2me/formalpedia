-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData11_3_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:08.336204+00:00
-- url     : https://prove2.me/submissions/24db24ec-f378-4ecb-9c0c-20d9a2b460b9

import Mathlib
import Definitions.Def_OAIQ257X021

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData11_3_calc_x_oai (j : Fin 31) : curvatureBox 1 1 3 j=curvatureData11_3 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData11_3_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData11_3_calc_x_oai
