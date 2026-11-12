-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry16_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:14:49.192188+00:00
-- url     : https://prove2.me/submissions/a3865dc9-6e1e-43e2-ba15-f5d527eb6f7d

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
lemma cellGeometry16_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 16 k ∧ cellMagnitude 16 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 16 → 0 ≤ cellSeparation 16 k j ∧ cellSeparation 16 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 16 k ∧ cellMagnitude 16 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 16 → 0 ≤ cellSeparation 16 k j ∧ cellSeparation 16 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry16_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry16_x_oai
