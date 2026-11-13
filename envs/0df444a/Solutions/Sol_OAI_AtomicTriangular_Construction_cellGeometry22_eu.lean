-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry22_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:11:19.543269+00:00
-- url     : https://prove2.me/submissions/f44b2a76-c810-4bd8-9842-8626b9eeeade

import Mathlib
import Definitions.Def_OAIQ334E011

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGrid2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry22_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 22 k ∧ cellMagnitude 22 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 22 → 0 ≤ cellSeparation 22 k j ∧ cellSeparation 22 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 22 k ∧ cellMagnitude 22 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 22 → 0 ≤ cellSeparation 22 k j ∧ cellSeparation 22 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry22_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry22_eu_oai
