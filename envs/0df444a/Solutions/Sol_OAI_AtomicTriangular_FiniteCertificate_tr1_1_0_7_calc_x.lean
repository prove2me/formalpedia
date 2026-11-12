-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_7_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:41:14.608981+00:00
-- url     : https://prove2.me/submissions/2a04efe3-c2b5-4f77-8b62-e2e51de1ed7b

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_1_0_7_calc_x_oai (r : Fin 8) : taylorRowBox 1 1 0 7 r = tr1_1_0_7 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_7_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_7_calc_x_oai
