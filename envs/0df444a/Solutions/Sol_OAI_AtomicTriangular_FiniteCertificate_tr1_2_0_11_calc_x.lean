-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_2_0_11_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:44:29.295638+00:00
-- url     : https://prove2.me/submissions/8bbc42fa-903f-4f05-9544-3643e2b7d828

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

lemma tr1_2_0_11_calc_x_oai (r : Fin 8) : taylorRowBox 1 2 0 11 r = tr1_2_0_11 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_2_0_11_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_2_0_11_calc_x_oai
