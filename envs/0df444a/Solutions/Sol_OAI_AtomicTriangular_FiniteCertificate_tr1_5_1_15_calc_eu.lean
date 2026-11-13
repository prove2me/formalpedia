-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_5_1_15_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:19:29.756109+00:00
-- url     : https://prove2.me/submissions/9c0b3514-f61d-4a39-824d-d80e46793218

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

lemma tr1_5_1_15_calc_eu_oai (r : Fin 8) : taylorRowBox 1 5 1 15 r = tr1_5_1_15 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_5_1_15_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_5_1_15_calc_eu_oai
