-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors00_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:04:39.649622+00:00
-- url     : https://prove2.me/submissions/a23053be-45d3-4127-932e-fb27998d5423

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
lemma cellFactors00_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 0 k j) ∧ cellBarrier 0 < ∏ j : Fin 15,(cellFactor 0 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 0 k j) ∧ cellBarrier 0 < ∏ j : Fin 15,(cellFactor 0 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors00_x_oai := @OAI.AtomicTriangular.Construction.cellFactors00_x_oai
