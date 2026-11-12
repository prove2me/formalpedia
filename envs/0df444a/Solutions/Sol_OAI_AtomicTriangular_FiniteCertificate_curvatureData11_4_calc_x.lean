-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData11_4_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:09.656203+00:00
-- url     : https://prove2.me/submissions/bdd2fb17-dc02-47ff-abc7-2b692348072f

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
lemma curvatureData11_4_calc_x_oai (j : Fin 31) : curvatureBox 1 1 4 j=curvatureData11_4 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData11_4_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData11_4_calc_x_oai
