-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors23_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:07:13.648577+00:00
-- url     : https://prove2.me/submissions/c96977da-49d2-4d8d-ac89-52ea0831642a

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
lemma cellFactors23_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 23 k j) ∧ cellBarrier 23 < ∏ j : Fin 15,(cellFactor 23 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 23 k j) ∧ cellBarrier 23 < ∏ j : Fin 15,(cellFactor 23 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors23_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors23_eu_oai
