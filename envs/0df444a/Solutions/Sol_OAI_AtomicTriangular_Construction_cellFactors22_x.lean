-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors22_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:11:37.318202+00:00
-- url     : https://prove2.me/submissions/b23bd39c-fc2c-4c88-9708-fb715a6fe3b0

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
lemma cellFactors22_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors22_x_oai := @OAI.AtomicTriangular.Construction.cellFactors22_x_oai
