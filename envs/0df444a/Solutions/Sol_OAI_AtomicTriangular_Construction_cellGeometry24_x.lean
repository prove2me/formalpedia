-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry24_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:16:09.781198+00:00
-- url     : https://prove2.me/submissions/628d4282-464e-4bf0-a8fd-f3f7f80df54f

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
lemma cellGeometry24_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 24 k ∧ cellMagnitude 24 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 24 → 0 ≤ cellSeparation 24 k j ∧ cellSeparation 24 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 24 k ∧ cellMagnitude 24 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 24 → 0 ≤ cellSeparation 24 k j ∧ cellSeparation 24 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry24_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry24_x_oai
