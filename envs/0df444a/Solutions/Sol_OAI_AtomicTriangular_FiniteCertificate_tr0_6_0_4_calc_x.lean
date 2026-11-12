-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_6_0_4_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:26:41.093197+00:00
-- url     : https://prove2.me/submissions/541030fd-0b8c-415c-95e8-f8ddeec7b4bb

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_6_0_4_calc_x_oai (r : Fin 8) : taylorRowBox 0 6 0 4 r = tr0_6_0_4 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_6_0_4_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_6_0_4_calc_x_oai
