-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_4_0_11_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:38.03314+00:00
-- url     : https://prove2.me/submissions/b17b2756-1e14-41a6-9f03-7582e026129b

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_4_0_11_calc_x_oai (r : Fin 8) : taylorRowBox 1 4 0 11 r = tr1_4_0_11 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_4_0_11_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_4_0_11_calc_x_oai
