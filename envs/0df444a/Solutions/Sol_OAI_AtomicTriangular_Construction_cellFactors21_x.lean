-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors21_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:11:36.27802+00:00
-- url     : https://prove2.me/submissions/63282f80-3f7d-438d-b1f3-bb4c5409b929

import Mathlib
import Definitions.Def_OAIQ257X011

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors21_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors21_x_oai := @OAI.AtomicTriangular.Construction.cellFactors21_x_oai
