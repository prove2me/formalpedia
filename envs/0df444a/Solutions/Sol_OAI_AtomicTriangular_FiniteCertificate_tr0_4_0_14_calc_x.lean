-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_14_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:09:56.590018+00:00
-- url     : https://prove2.me/submissions/91736f19-f2b4-4ce4-a980-ef03e163502c

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_4_0_14_calc_x_oai (r : Fin 8) : taylorRowBox 0 4 0 14 r = tr0_4_0_14 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_14_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_14_calc_x_oai
