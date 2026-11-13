-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_16_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:20:56.423911+00:00
-- url     : https://prove2.me/submissions/0cb18513-9808-4018-a739-cfee1b4a84da

import Mathlib
import Definitions.Def_OAIQ334E023

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_6_0_16_calc_eu_oai (r : Fin 8) : taylorRowBox 1 6 0 16 r = tr1_6_0_16 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_16_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_16_calc_eu_oai
