-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors29_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:08:05.863449+00:00
-- url     : https://prove2.me/submissions/9386c1cb-72e2-4120-b52f-375f44dcd3d0

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
lemma cellFactors29_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 29 k j) ∧ cellBarrier 29 < ∏ j : Fin 15,(cellFactor 29 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 29 k j) ∧ cellBarrier 29 < ∏ j : Fin 15,(cellFactor 29 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors29_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors29_eu_oai
