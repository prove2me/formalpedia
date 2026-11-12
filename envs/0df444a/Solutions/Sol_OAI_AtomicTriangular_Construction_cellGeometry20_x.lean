-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry20_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:16:04.839532+00:00
-- url     : https://prove2.me/submissions/22fa25ca-4a68-43d8-b705-6f16c3bad8aa

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
lemma cellGeometry20_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 20 k ∧ cellMagnitude 20 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 20 → 0 ≤ cellSeparation 20 k j ∧ cellSeparation 20 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 20 k ∧ cellMagnitude 20 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 20 → 0 ≤ cellSeparation 20 k j ∧ cellSeparation 20 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry20_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry20_x_oai
