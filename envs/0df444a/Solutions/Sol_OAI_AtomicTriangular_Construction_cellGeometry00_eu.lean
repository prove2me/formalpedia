-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry00_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:09:22.313965+00:00
-- url     : https://prove2.me/submissions/0fbe9950-8711-469f-a78d-ed26ba20a890

import Mathlib
import Definitions.Def_OAIQ334E011

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry00_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 0 k ∧ cellMagnitude 0 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 0 → 0 ≤ cellSeparation 0 k j ∧ cellSeparation 0 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 0 k ∧ cellMagnitude 0 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 0 → 0 ≤ cellSeparation 0 k j ∧ cellSeparation 0 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry00_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry00_eu_oai
