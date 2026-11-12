-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_17_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:07:32.156847+00:00
-- url     : https://prove2.me/submissions/09c8c969-9173-49bc-b2a7-0c27e916e08f

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_3_1_17_calc_x_oai (r : Fin 8) : taylorRowBox 0 3 1 17 r = tr0_3_1_17 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_17_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_17_calc_x_oai
