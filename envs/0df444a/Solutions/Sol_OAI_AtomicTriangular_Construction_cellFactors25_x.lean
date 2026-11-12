-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors25_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:11:40.956145+00:00
-- url     : https://prove2.me/submissions/dcd3222c-f8d3-4fd6-983d-c34c8e5a58a2

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
lemma cellFactors25_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors25_x_oai := @OAI.AtomicTriangular.Construction.cellFactors25_x_oai
