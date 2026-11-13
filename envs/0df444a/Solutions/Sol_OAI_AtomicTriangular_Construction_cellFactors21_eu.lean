-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors21_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:06:46.900699+00:00
-- url     : https://prove2.me/submissions/f96330ae-ee5b-4609-b126-b60ae56bdfc3

import Mathlib
import Definitions.Def_OAIQ334E011

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGrid2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors21_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors21_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors21_eu_oai
