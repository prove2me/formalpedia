-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry15_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:14:48.148475+00:00
-- url     : https://prove2.me/submissions/a7951c17-f48f-46cf-9828-4deb51ae1216

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
lemma cellGeometry15_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 15 k ∧ cellMagnitude 15 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 15 → 0 ≤ cellSeparation 15 k j ∧ cellSeparation 15 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 15 k ∧ cellMagnitude 15 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 15 → 0 ≤ cellSeparation 15 k j ∧ cellSeparation 15 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry15_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry15_x_oai
