-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_4_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:44:53.904223+00:00
-- url     : https://prove2.me/submissions/eba48d55-12a2-4f7b-8530-ad2e820ba74f

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

lemma tr1_1_1_4_calc_x_oai (r : Fin 8) : taylorRowBox 1 1 1 4 r = tr1_1_1_4 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_4_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_4_calc_x_oai
