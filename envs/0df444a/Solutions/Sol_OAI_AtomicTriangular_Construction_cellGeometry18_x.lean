-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry18_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:15:38.163208+00:00
-- url     : https://prove2.me/submissions/c0383fca-8e26-453b-b999-2d88803897aa

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
lemma cellGeometry18_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 18 k ∧ cellMagnitude 18 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 18 → 0 ≤ cellSeparation 18 k j ∧ cellSeparation 18 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 18 k ∧ cellMagnitude 18 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 18 → 0 ≤ cellSeparation 18 k j ∧ cellSeparation 18 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry18_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry18_x_oai
