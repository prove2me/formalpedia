-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry18_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:10:50.508958+00:00
-- url     : https://prove2.me/submissions/64d2da02-dfbf-4d5e-a6f5-8d5534fda664

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
lemma cellGeometry18_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 18 k ∧ cellMagnitude 18 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 18 → 0 ≤ cellSeparation 18 k j ∧ cellSeparation 18 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 18 k ∧ cellMagnitude 18 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 18 → 0 ≤ cellSeparation 18 k j ∧ cellSeparation 18 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry18_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry18_eu_oai
