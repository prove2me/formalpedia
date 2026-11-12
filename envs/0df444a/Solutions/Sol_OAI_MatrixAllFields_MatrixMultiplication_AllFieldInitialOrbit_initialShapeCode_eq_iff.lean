-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.initialShapeCode_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:42.621201+00:00
-- url     : https://prove2.me/submissions/1df300f4-8eee-4da9-91c0-b0935f1e90dd

import Mathlib
import Definitions.Def_OAIQ254M000

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InitialOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldInitialOrbit

open AllFieldParameters AllFieldHistory AllFieldInitialEntropy
open scoped BigOperators

theorem decodeShape_injective : Function.Injective decodeShape := by
  intro u v h
  apply Prod.ext
  · exact Fin.ext (congrFun h 0)
  · apply Prod.ext
    · exact Fin.ext (congrFun h 1)
    · exact Fin.ext (congrFun h 2)

theorem initialShapeCode_eq_iff_oai (p : PlacedInitial) (u : JointPopulation.Shape) :
    initialShapeCode p = u ↔
      physicalShape p.2 (sortedInitial.get p.1) = decodeShape u := by
  have hdecode : decodeShape (initialShapeCode p) =
      physicalShape p.2 (sortedInitial.get p.1) := by
    funext i
    exact initialShapeCode_side p i
  rw [← hdecode]
  exact decodeShape_injective.eq_iff.symm

end MatrixMultiplication.AllFieldInitialOrbit

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.initialShapeCode_eq_iff_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.initialShapeCode_eq_iff_oai
