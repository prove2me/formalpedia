-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors02_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:10:02.600316+00:00
-- url     : https://prove2.me/submissions/021a6814-b8dd-4dbe-ba62-2ff0a4a6e581

import Mathlib
import Definitions.Def_OAIQ257X011

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors02_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 2 k j) ∧ cellBarrier 2 < ∏ j : Fin 15,(cellFactor 2 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 2 k j) ∧ cellBarrier 2 < ∏ j : Fin 15,(cellFactor 2 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors02_x_oai := @OAI.AtomicTriangular.Construction.cellFactors02_x_oai
