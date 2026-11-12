-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry00_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:12:58.366935+00:00
-- url     : https://prove2.me/submissions/b9fb542f-7a3a-49b4-8ed8-fbd87aac9a50

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
lemma cellGeometry00_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 0 k ∧ cellMagnitude 0 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 0 → 0 ≤ cellSeparation 0 k j ∧ cellSeparation 0 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 0 k ∧ cellMagnitude 0 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 0 → 0 ≤ cellSeparation 0 k j ∧ cellSeparation 0 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry00_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry00_x_oai
