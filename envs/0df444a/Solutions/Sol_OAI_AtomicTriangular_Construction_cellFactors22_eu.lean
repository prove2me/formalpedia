-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors22_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:07:12.485693+00:00
-- url     : https://prove2.me/submissions/7492d7ae-74b2-4a88-866e-84c3c12e9f54

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
lemma cellFactors22_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors22_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors22_eu_oai
