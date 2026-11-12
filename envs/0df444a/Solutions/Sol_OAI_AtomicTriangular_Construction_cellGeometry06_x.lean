-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry06_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:13:52.194351+00:00
-- url     : https://prove2.me/submissions/4da62677-af97-4129-a0d4-b55c78a26e35

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
lemma cellGeometry06_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 6 k ∧ cellMagnitude 6 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 6 → 0 ≤ cellSeparation 6 k j ∧ cellSeparation 6 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 6 k ∧ cellMagnitude 6 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 6 → 0 ≤ cellSeparation 6 k j ∧ cellSeparation 6 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry06_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry06_x_oai
