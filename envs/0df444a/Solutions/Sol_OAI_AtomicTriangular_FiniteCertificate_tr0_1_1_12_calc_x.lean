-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_12_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:56:08.992401+00:00
-- url     : https://prove2.me/submissions/e385f50c-9d84-4a6f-8f72-4b3df1a7e196

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

lemma tr0_1_1_12_calc_x_oai (r : Fin 8) : taylorRowBox 0 1 1 12 r = tr0_1_1_12 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_12_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_12_calc_x_oai
