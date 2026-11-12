-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_4_0_9_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:56:31.717445+00:00
-- url     : https://prove2.me/submissions/d093fcff-f211-4d1b-981e-808d2a2c1b26

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

lemma tr1_4_0_9_calc_x_oai (r : Fin 8) : taylorRowBox 1 4 0 9 r = tr1_4_0_9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_4_0_9_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_4_0_9_calc_x_oai
