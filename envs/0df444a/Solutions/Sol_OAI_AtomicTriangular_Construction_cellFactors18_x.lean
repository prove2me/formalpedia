-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors18_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:11:08.017339+00:00
-- url     : https://prove2.me/submissions/a9bb11a3-86ca-4977-bfdc-26ecbf04d02f

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
lemma cellFactors18_x_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 18 k j) ∧ cellBarrier 18 < ∏ j : Fin 15,(cellFactor 18 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 18 k j) ∧ cellBarrier 18 < ∏ j : Fin 15,(cellFactor 18 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors18_x_oai := @OAI.AtomicTriangular.Construction.cellFactors18_x_oai
