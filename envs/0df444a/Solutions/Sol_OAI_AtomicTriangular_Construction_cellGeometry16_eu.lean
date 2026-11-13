-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry16_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:10:22.31538+00:00
-- url     : https://prove2.me/submissions/c2b9d0ea-56bf-4ae5-af87-d761affa66aa

import Mathlib
import Definitions.Def_OAIQ334E011

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry16_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 16 k ∧ cellMagnitude 16 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 16 → 0 ≤ cellSeparation 16 k j ∧ cellSeparation 16 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 16 k ∧ cellMagnitude 16 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 16 → 0 ≤ cellSeparation 16 k j ∧ cellSeparation 16 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry16_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry16_eu_oai
