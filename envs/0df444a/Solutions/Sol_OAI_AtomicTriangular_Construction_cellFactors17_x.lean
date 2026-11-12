-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors17_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:10:41.647351+00:00
-- url     : https://prove2.me/submissions/68ee4bd3-1c1c-48e2-89c6-1c29487b3f83

import Mathlib
import Definitions.Def_OAIQ257X011

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors17_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 17 k j) ∧ cellBarrier 17 < ∏ j : Fin 15,(cellFactor 17 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 17 k j) ∧ cellBarrier 17 < ∏ j : Fin 15,(cellFactor 17 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors17_x_oai := @OAI.AtomicTriangular.Construction.cellFactors17_x_oai
