-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry23_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:16:08.803958+00:00
-- url     : https://prove2.me/submissions/ac4ca878-19c6-43bf-8018-ee290d60a4ff

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
lemma cellGeometry23_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0 ≤ cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0 ≤ cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry23_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry23_x_oai
