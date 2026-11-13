-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry06_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:09:48.101996+00:00
-- url     : https://prove2.me/submissions/16037f6c-84b7-4f1f-a291-c3ad91160f0a

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
lemma cellGeometry06_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 6 k ∧ cellMagnitude 6 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 6 → 0 ≤ cellSeparation 6 k j ∧ cellSeparation 6 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 6 k ∧ cellMagnitude 6 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 6 → 0 ≤ cellSeparation 6 k j ∧ cellSeparation 6 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry06_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry06_eu_oai
