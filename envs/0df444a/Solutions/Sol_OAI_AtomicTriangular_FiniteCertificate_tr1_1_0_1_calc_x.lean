-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_1_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:40:20.353199+00:00
-- url     : https://prove2.me/submissions/f5842a56-98fd-43dd-989b-c97516ef0966

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

lemma tr1_1_0_1_calc_x_oai (r : Fin 8) : taylorRowBox 1 1 0 1 r = tr1_1_0_1 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_1_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_1_calc_x_oai
