-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors08_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:05:30.529955+00:00
-- url     : https://prove2.me/submissions/9017fa07-0c2c-451d-88cf-f2208362b604

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
lemma cellFactors08_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors08_x_oai := @OAI.AtomicTriangular.Construction.cellFactors08_x_oai
