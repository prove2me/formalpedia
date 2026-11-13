-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_5_0_7_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:19:56.187207+00:00
-- url     : https://prove2.me/submissions/168100d7-aa0a-4d83-8f01-fd38bbbe587a

import Mathlib
import Definitions.Def_OAIQ334E023

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_5_0_7_calc_eu_oai (r : Fin 8) : taylorRowBox 1 5 0 7 r = tr1_5_0_7 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_5_0_7_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_5_0_7_calc_eu_oai
