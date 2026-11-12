-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry09_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:14:17.603356+00:00
-- url     : https://prove2.me/submissions/e3d91ba2-1cc6-419b-a6d3-c2d502832162

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
lemma cellGeometry09_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 9 k ∧ cellMagnitude 9 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 9 → 0 ≤ cellSeparation 9 k j ∧ cellSeparation 9 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 9 k ∧ cellMagnitude 9 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 9 → 0 ≤ cellSeparation 9 k j ∧ cellSeparation 9 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry09_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry09_x_oai
