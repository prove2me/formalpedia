-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_3_1_13_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:51:37.492263+00:00
-- url     : https://prove2.me/submissions/20e5b70a-16f3-4ed7-af9f-fc312493723c

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_3_1_13_calc_x_oai (r : Fin 8) : taylorRowBox 1 3 1 13 r = tr1_3_1_13 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_3_1_13_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_3_1_13_calc_x_oai
