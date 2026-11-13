-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_19_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:18:05.245196+00:00
-- url     : https://prove2.me/submissions/e18367ef-14f5-4ded-8697-80f50b45b24f

import Mathlib
import Definitions.Def_OAIQ334E023

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_4_1_19_calc_eu_oai (r : Fin 8) : taylorRowBox 1 4 1 19 r = tr1_4_1_19 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_19_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_19_calc_eu_oai
