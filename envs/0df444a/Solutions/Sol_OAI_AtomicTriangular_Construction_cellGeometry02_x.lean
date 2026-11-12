-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry02_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:13:24.1112+00:00
-- url     : https://prove2.me/submissions/63384df3-95a5-41be-a2ef-76bf463668bf

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
lemma cellGeometry02_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 2 k ∧ cellMagnitude 2 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 2 → 0 ≤ cellSeparation 2 k j ∧ cellSeparation 2 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 2 k ∧ cellMagnitude 2 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 2 → 0 ≤ cellSeparation 2 k j ∧ cellSeparation 2 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry02_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry02_x_oai
