-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry11_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:14:20.100198+00:00
-- url     : https://prove2.me/submissions/fa7ad098-26f1-455f-909b-0b5f9df12c61

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
lemma cellGeometry11_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 11 k ∧ cellMagnitude 11 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 11 → 0 ≤ cellSeparation 11 k j ∧ cellSeparation 11 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 11 k ∧ cellMagnitude 11 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 11 → 0 ≤ cellSeparation 11 k j ∧ cellSeparation 11 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry11_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry11_x_oai
