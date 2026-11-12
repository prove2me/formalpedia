-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors01_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:03:48.919205+00:00
-- url     : https://prove2.me/submissions/196611c6-74cf-4ede-af1c-c456e1814f92

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
lemma cellFactors01_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 1 k j) ∧ cellBarrier 1 < ∏ j : Fin 15,(cellFactor 1 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 1 k j) ∧ cellBarrier 1 < ∏ j : Fin 15,(cellFactor 1 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors01_x_oai := @OAI.AtomicTriangular.Construction.cellFactors01_x_oai
