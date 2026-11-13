-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors08_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:05:18.673477+00:00
-- url     : https://prove2.me/submissions/356ffb3b-6c2a-4444-a780-bda12d413d35

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
lemma cellFactors08_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors08_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors08_eu_oai
