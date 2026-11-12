-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_13_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:48:09.453147+00:00
-- url     : https://prove2.me/submissions/8a576e78-5127-42db-9b7a-cf82825850ac

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

lemma tr1_2_1_13_calc_x_oai (r : Fin 8) : taylorRowBox 1 2 1 13 r = tr1_2_1_13 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_13_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_13_calc_x_oai
