-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors15_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:10:39.081781+00:00
-- url     : https://prove2.me/submissions/b9117689-b0dc-40e2-9856-e1276b76bae3

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
lemma cellFactors15_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 15 k j) ∧ cellBarrier 15 < ∏ j : Fin 15,(cellFactor 15 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 15 k j) ∧ cellBarrier 15 < ∏ j : Fin 15,(cellFactor 15 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors15_x_oai := @OAI.AtomicTriangular.Construction.cellFactors15_x_oai
