-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_5_1_0_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:20:56.035142+00:00
-- url     : https://prove2.me/submissions/37b16158-b708-4164-8e3b-26a64460e61b

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_5_1_0_calc_x_oai (r : Fin 8) : taylorRowBox 0 5 1 0 r = tr0_5_1_0 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_5_1_0_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_5_1_0_calc_x_oai
