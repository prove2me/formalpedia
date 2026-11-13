-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors06_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:04:51.949209+00:00
-- url     : https://prove2.me/submissions/c5bd0ff4-861a-45b1-a624-3ac86f60cf62

import Mathlib
import Definitions.Def_OAIQ334E011

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors06_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 6 k j) ∧ cellBarrier 6 < ∏ j : Fin 15,(cellFactor 6 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 6 k j) ∧ cellBarrier 6 < ∏ j : Fin 15,(cellFactor 6 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors06_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors06_eu_oai
