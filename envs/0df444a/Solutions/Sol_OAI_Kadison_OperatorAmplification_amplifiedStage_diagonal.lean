-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.amplifiedStage_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:59:13.552663+00:00
-- url     : https://prove2.me/submissions/2d88a3df-b37f-4871-840d-e10e2fff3c9d

import Mathlib
import Definitions.Def_OAIQ039C067

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerStage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

variable (E : MatrixTower.Stage M)

attribute [local instance] OAI.Kadison.OperatorAmplification.amplifiedTowerStageDecidableEq
lemma amplifiedStage_diagonal_oai (a : Matrix E.I E.I ℂ) :
    diagonalHom ι i₀ M (E.hom a)∈(amplifiedStage ι i₀ M E).hom.range := by
  have hh := MatrixTensor.right_mem (A := matrixVonNeumann ι i₀ M)
    (I := ι) (J := E.I) (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp E.hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x (E.hom y)) a
  obtain ⟨b,hb⟩ := hh
  exact ⟨b,hb⟩

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.amplifiedStage_diagonal_oai := @OAI.Kadison.OperatorAmplification.amplifiedStage_diagonal_oai
