-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_20_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:41:09.744897+00:00
-- url     : https://prove2.me/submissions/b1c083a7-cba6-4982-acce-161d96bd2783

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

lemma tr1_1_0_20_calc_x_oai (r : Fin 8) : taylorRowBox 1 1 0 20 r = tr1_1_0_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_20_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_20_calc_x_oai
