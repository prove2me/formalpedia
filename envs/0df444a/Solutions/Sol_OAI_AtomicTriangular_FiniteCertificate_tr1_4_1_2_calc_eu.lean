-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_2_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T14:01:39.669533+00:00
-- url     : https://prove2.me/submissions/34e5c082-2e35-40b2-a335-b1ed490a66ba

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

lemma tr1_4_1_2_calc_eu_oai (r : Fin 8) : taylorRowBox 1 4 1 2 r = tr1_4_1_2 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_2_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_2_calc_eu_oai
