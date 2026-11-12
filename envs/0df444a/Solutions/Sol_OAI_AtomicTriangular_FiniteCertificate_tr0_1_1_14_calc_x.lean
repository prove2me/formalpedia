-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_14_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:57:27.920585+00:00
-- url     : https://prove2.me/submissions/267e09ed-43ca-4a47-914f-051d93c0d6fa

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_1_1_14_calc_x_oai (r : Fin 8) : taylorRowBox 0 1 1 14 r = tr0_1_1_14 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_14_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_14_calc_x_oai
