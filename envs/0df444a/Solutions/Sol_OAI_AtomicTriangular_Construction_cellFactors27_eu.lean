-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors27_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:08:03.330789+00:00
-- url     : https://prove2.me/submissions/030e964a-57c2-4e6c-b43f-35b5bc9f7811

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
lemma cellFactors27_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 27 k j) ∧ cellBarrier 27 < ∏ j : Fin 15,(cellFactor 27 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 27 k j) ∧ cellBarrier 27 < ∏ j : Fin 15,(cellFactor 27 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors27_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors27_eu_oai
