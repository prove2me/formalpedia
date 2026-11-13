-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors25_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:08:56.01665+00:00
-- url     : https://prove2.me/submissions/00d2f926-4e3c-4778-86bc-95c18998bf52

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
lemma cellFactors25_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors25_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors25_eu_oai
