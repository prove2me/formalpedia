-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry27_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:16:36.608222+00:00
-- url     : https://prove2.me/submissions/e7e97d09-3c54-481c-b033-fc0a7faf066d

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
lemma cellGeometry27_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 27 k ∧ cellMagnitude 27 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 27 → 0 ≤ cellSeparation 27 k j ∧ cellSeparation 27 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 27 k ∧ cellMagnitude 27 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 27 → 0 ≤ cellSeparation 27 k j ∧ cellSeparation 27 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry27_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry27_x_oai
