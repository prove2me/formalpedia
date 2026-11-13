-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_5_1_5_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:09:52.156743+00:00
-- url     : https://prove2.me/submissions/1cc6f295-0453-4ccf-a193-eca3eac242f5

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_5_1_5_calc_x_oai (r : Fin 8) : taylorRowBox 1 5 1 5 r = tr1_5_1_5 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_5_1_5_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_5_1_5_calc_x_oai
