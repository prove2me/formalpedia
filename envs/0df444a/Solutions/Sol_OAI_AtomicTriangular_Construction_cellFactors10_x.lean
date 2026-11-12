-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors10_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:10:08.064708+00:00
-- url     : https://prove2.me/submissions/40085256-d02f-4756-950f-5d9e5b610c4e

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
lemma cellFactors10_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 10 k j) ∧ cellBarrier 10 < ∏ j : Fin 15,(cellFactor 10 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 10 k j) ∧ cellBarrier 10 < ∏ j : Fin 15,(cellFactor 10 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors10_x_oai := @OAI.AtomicTriangular.Construction.cellFactors10_x_oai
