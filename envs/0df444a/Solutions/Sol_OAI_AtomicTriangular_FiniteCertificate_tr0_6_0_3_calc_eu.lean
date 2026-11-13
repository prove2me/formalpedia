-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_6_0_3_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:51:33.270413+00:00
-- url     : https://prove2.me/submissions/4a73c191-21b5-478c-8265-a381ef7de60f

import Mathlib
import Definitions.Def_OAIQ334E023

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_6_0_3_calc_eu_oai (r : Fin 8) : taylorRowBox 0 6 0 3 r = tr0_6_0_3 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_6_0_3_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_6_0_3_calc_eu_oai
