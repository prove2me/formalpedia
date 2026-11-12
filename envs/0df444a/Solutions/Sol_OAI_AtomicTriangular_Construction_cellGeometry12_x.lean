-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry12_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:14:21.603581+00:00
-- url     : https://prove2.me/submissions/20d8f5f6-c3b3-473d-bd08-b3ab68c36ef7

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
lemma cellGeometry12_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 12 k ∧ cellMagnitude 12 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 12 → 0 ≤ cellSeparation 12 k j ∧ cellSeparation 12 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 12 k ∧ cellMagnitude 12 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 12 → 0 ≤ cellSeparation 12 k j ∧ cellSeparation 12 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry12_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry12_x_oai
