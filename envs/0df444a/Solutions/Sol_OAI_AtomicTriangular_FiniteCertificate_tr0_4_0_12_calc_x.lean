-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_12_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:10:24.204319+00:00
-- url     : https://prove2.me/submissions/b12cea83-a189-40dc-b70d-326a330c3015

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

lemma tr0_4_0_12_calc_x_oai (r : Fin 8) : taylorRowBox 0 4 0 12 r = tr0_4_0_12 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_12_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_12_calc_x_oai
