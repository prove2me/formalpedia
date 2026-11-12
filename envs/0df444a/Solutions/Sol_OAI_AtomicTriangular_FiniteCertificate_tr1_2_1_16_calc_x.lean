-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_16_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:48:11.596828+00:00
-- url     : https://prove2.me/submissions/e2341a7f-e756-4090-bc4e-9ceb43855747

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_2_1_16_calc_x_oai (r : Fin 8) : taylorRowBox 1 2 1 16 r = tr1_2_1_16 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_16_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_16_calc_x_oai
