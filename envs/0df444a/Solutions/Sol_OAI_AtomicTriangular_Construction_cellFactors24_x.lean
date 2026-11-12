-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors24_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:11:39.757477+00:00
-- url     : https://prove2.me/submissions/afc0d8f0-758a-47c6-8c1e-a3969ab63893

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
lemma cellFactors24_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 24 k j) ∧ cellBarrier 24 < ∏ j : Fin 15,(cellFactor 24 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 24 k j) ∧ cellBarrier 24 < ∏ j : Fin 15,(cellFactor 24 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors24_x_oai := @OAI.AtomicTriangular.Construction.cellFactors24_x_oai
